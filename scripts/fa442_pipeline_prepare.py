from __future__ import annotations

import io
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.request
import zipfile
from pathlib import Path
from typing import Any

from fa442_pipeline_common import (
    BASELINE_LINE_COUNT,
    BASELINE_SHA256,
    BLOCKER,
    FA423_RUN_ID,
    FA442_RUN_ID,
    REPO,
    append_github_output,
    extract_blocker_header,
    git,
    line_count_bytes,
    sha256_bytes,
    slugify,
    source_metadata,
    write_json,
)

OUT = REPO / "build-logs/fa442-pipeline-repair/prep"
BUNDLE = OUT / "candidate-bundle"
API = "https://api.github.com"
TOKEN = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN", "")
REPOSITORY = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")


def request(url: str, *, accept: str = "application/vnd.github+json") -> bytes:
    req = urllib.request.Request(url)
    req.add_header("Accept", accept)
    req.add_header("X-GitHub-Api-Version", "2022-11-28")
    req.add_header("User-Agent", "fa442-direct-metric-repair")
    if TOKEN:
        req.add_header("Authorization", f"Bearer {TOKEN}")
    with urllib.request.urlopen(req, timeout=120) as response:
        return response.read()


def api_json(path_or_url: str) -> Any:
    url = path_or_url if path_or_url.startswith("http") else API + path_or_url
    return json.loads(request(url).decode("utf-8"))


def paged(path: str, key: str) -> list[Any]:
    out: list[Any] = []
    page = 1
    while True:
        sep = "&" if "?" in path else "?"
        payload = api_json(f"{path}{sep}per_page=100&page={page}")
        rows = payload.get(key, payload if isinstance(payload, list) else [])
        out.extend(rows)
        if len(rows) < 100:
            break
        page += 1
    return out


def workflow_from_run(run: dict[str, Any]) -> tuple[str, str]:
    path = str(run.get("path") or "")
    head_sha = str(run.get("head_sha") or "")
    if not path or not head_sha:
        raise RuntimeError("FA442 run metadata does not contain workflow path/head SHA")
    cp = subprocess.run(
        ["git", "show", f"{head_sha}:{path}"],
        cwd=REPO,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if cp.returncode != 0:
        subprocess.run(["git", "fetch", "origin", head_sha, "--depth=1"], cwd=REPO, check=True)
        cp = subprocess.run(
            ["git", "show", f"{head_sha}:{path}"], cwd=REPO,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
        )
    return path, cp.stdout.decode("utf-8")


def step_blocks(workflow: str) -> list[dict[str, str]]:
    lines = workflow.splitlines()
    blocks: list[dict[str, str]] = []
    i = 0
    name_re = re.compile(r"^(\s*)-\s+name:\s*(.+?)\s*$")
    while i < len(lines):
        match = name_re.match(lines[i])
        if not match:
            i += 1
            continue
        indent = len(match.group(1))
        name = match.group(2).strip("'\"")
        block = [lines[i]]
        j = i + 1
        while j < len(lines):
            next_match = name_re.match(lines[j])
            if next_match and len(next_match.group(1)) == indent:
                break
            block.append(lines[j])
            j += 1
        condition = ""
        step_id = ""
        for raw in block[1:]:
            stripped = raw.strip()
            if stripped.startswith("if:"):
                condition = stripped[3:].strip()
            elif stripped.startswith("id:"):
                step_id = stripped[3:].strip()
        blocks.append({
            "name": name,
            "id": step_id,
            "if": condition,
            "text": "\n".join(block),
        })
        i = j
    return blocks


def output_references(condition: str) -> list[str]:
    refs = re.findall(r"(?:steps|needs)\.[A-Za-z0-9_-]+\.outputs\.[A-Za-z0-9_-]+", condition)
    return sorted(set(refs))


def ref_definition_status(workflow: str, ref: str) -> dict[str, Any]:
    parts = ref.split(".")
    scope, owner, _, output = parts
    if scope == "steps":
        owner_exists = bool(re.search(rf"(?m)^\s*id:\s*{re.escape(owner)}\s*$", workflow))
        output_written = bool(re.search(
            rf"(?m)(?:echo|printf).*{re.escape(output)}=.*GITHUB_OUTPUT", workflow
        ))
        return {
            "reference": ref,
            "owner_exists": owner_exists,
            "output_definition_found": output_written,
        }
    job_exists = bool(re.search(rf"(?m)^\s{{2}}{re.escape(owner)}:\s*$", workflow))
    output_mapped = bool(re.search(
        rf"(?ms)^\s{{2}}{re.escape(owner)}:.*?^\s{{4}}outputs:.*?"
        rf"^\s{{6}}{re.escape(output)}:\s*",
        workflow,
    ))
    return {
        "reference": ref,
        "owner_exists": job_exists,
        "output_definition_found": output_mapped,
    }


def diagnose(run: dict[str, Any], jobs: list[dict[str, Any]], workflow_path: str,
             workflow: str) -> dict[str, Any]:
    target_names = {
        "Install pinned Lean and Mathlib cache",
        "Directly compile completed prerequisites and candidate FA",
    }
    blocks = {block["name"]: block for block in step_blocks(workflow)}
    skipped: list[dict[str, Any]] = []
    for job in jobs:
        for step in job.get("steps", []):
            if step.get("name") in target_names and step.get("conclusion") == "skipped":
                block = blocks.get(step["name"], {})
                condition = str(block.get("if", ""))
                refs = output_references(condition)
                skipped.append({
                    "job_id": job.get("id"),
                    "job_name": job.get("name"),
                    "step_name": step.get("name"),
                    "step_number": step.get("number"),
                    "conclusion": step.get("conclusion"),
                    "condition": condition,
                    "output_references": [ref_definition_status(workflow, ref) for ref in refs],
                })
    undefined = sorted({
        ref["reference"]
        for item in skipped
        for ref in item["output_references"]
        if not ref["output_definition_found"]
    })
    guarded = sorted({item["condition"] for item in skipped if item["condition"]})
    if undefined:
        root_cause = (
            "The skipped Lean setup/compile steps were guarded by output-dependent `if:` "
            "expressions that referenced outputs with no definition in the FA442 workflow: "
            + ", ".join(undefined)
            + ". GitHub Actions resolves an unset output to the empty string, so the guard "
              "evaluated false and both Lean steps were skipped."
        )
    elif guarded:
        root_cause = (
            "The skipped Lean setup/compile steps were not unconditional. Their actual FA442 "
            "`if:` guards were: " + " | ".join(guarded)
            + ". In the candidate jobs the referenced upstream value was empty/false, so GitHub "
              "Actions evaluated the guard false. Candidate generation therefore completed while "
              "no direct Lean metric was produced."
        )
    else:
        root_cause = (
            "The FA442 jobs API records both Lean setup and direct compile as skipped, but no "
            "step-level `if:` was recoverable from the run workflow. This is classified as an "
            "infrastructure failure and the replacement workflow removes all metadata-dependent "
            "guards from candidate Lean setup/compile."
        )
    return {
        "classification": "INFRA_FAILURE",
        "run_id": run.get("id"),
        "run_url": run.get("html_url"),
        "head_branch": run.get("head_branch"),
        "head_sha": run.get("head_sha"),
        "workflow_path": workflow_path,
        "workflow_name": run.get("name"),
        "skipped_steps": skipped,
        "undefined_output_references": undefined,
        "guard_expressions": guarded,
        "selector_failure": "RuntimeError: expected one baseline direct metric, found 0",
        "git_identity_failure": "Author identity unknown / fatal: empty ident name",
        "root_cause": root_cause,
        "repair": {
            "candidate_lean_install_unconditional": True,
            "candidate_direct_compile_unconditional": True,
            "missing_metric_classification": "INFRA_FAILURE",
            "selector_requires_exactly_one_current_run_baseline_metric": True,
            "git_identity_configured_in_every_commit_job": True,
        },
    }


def extract_zip(data: bytes, destination: Path) -> None:
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        archive.extractall(destination)


def download_run_artifacts(run_id: int, destination: Path) -> list[dict[str, Any]]:
    artifacts = paged(f"/repos/{REPOSITORY}/actions/runs/{run_id}/artifacts", "artifacts")
    destination.mkdir(parents=True, exist_ok=True)
    manifest = []
    for artifact in artifacts:
        artifact_id = int(artifact["id"])
        name = str(artifact["name"])
        target = destination / f"{artifact_id}-{slugify(name)}"
        target.mkdir(parents=True, exist_ok=True)
        try:
            data = request(
                f"{API}/repos/{REPOSITORY}/actions/artifacts/{artifact_id}/zip",
                accept="application/vnd.github+json",
            )
            extract_zip(data, target)
            status = "downloaded"
        except Exception as exc:  # evidence must survive partial artifact failures
            status = f"download_failed: {exc!r}"
        manifest.append({
            "id": artifact_id,
            "name": name,
            "expired": artifact.get("expired"),
            "status": status,
            "path": str(target.relative_to(OUT)),
        })
    return manifest


def candidate_bytes(path: Path) -> bytes | None:
    try:
        if not path.is_file() or path.stat().st_size < 100_000 or path.stat().st_size > 20_000_000:
            return None
        data = path.read_bytes()
        if f"theorem {BLOCKER}".encode() not in data:
            return None
        data.decode("utf-8")
        return data
    except Exception:
        return None


def scan_tree(root: Path, origin: str, found: dict[str, dict[str, Any]]) -> None:
    if not root.exists():
        return
    for path in root.rglob("*"):
        data = candidate_bytes(path)
        if data is None:
            continue
        sha = sha256_bytes(data)
        entry = found.setdefault(sha, {
            "data": data,
            "origins": [],
            "line_count": line_count_bytes(data),
        })
        entry["origins"].append(f"{origin}:{path.relative_to(root)}")


def scan_git_refs(found: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    subprocess.run(
        ["git", "fetch", "origin", "+refs/heads/*:refs/remotes/origin/*", "--depth=1"],
        cwd=REPO, check=True,
    )
    refs = git("for-each-ref", "--format=%(refname:short)", "refs/remotes/origin").splitlines()
    relevant = [
        ref for ref in refs
        if re.search(r"(?:fa42[3-9]|fa4[3-9][0-9]|functional|primality-sheaf-clean-build)", ref, re.I)
    ]
    branch_rows: list[dict[str, Any]] = []
    for ref in relevant:
        cp = subprocess.run(
            ["git", "show", f"{ref}:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"],
            cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, check=False,
        )
        if cp.returncode != 0:
            continue
        data = cp.stdout
        if f"theorem {BLOCKER}".encode() not in data:
            continue
        sha = sha256_bytes(data)
        entry = found.setdefault(sha, {
            "data": data,
            "origins": [],
            "line_count": line_count_bytes(data),
        })
        entry["origins"].append(f"git:{ref}")
        branch_rows.append({"ref": ref, "sha256": sha, "line_count": line_count_bytes(data)})
    return branch_rows


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)
    BUNDLE.mkdir(parents=True)

    run = api_json(f"/repos/{REPOSITORY}/actions/runs/{FA442_RUN_ID}")
    jobs = paged(f"/repos/{REPOSITORY}/actions/runs/{FA442_RUN_ID}/jobs", "jobs")
    head_sha = str(run["head_sha"])
    subprocess.run(["git", "fetch", "origin", head_sha, "--depth=1"], cwd=REPO, check=True)
    workflow_path, workflow = workflow_from_run(run)
    (OUT / "fa442-workflow.yml").write_text(workflow, encoding="utf-8")
    write_json(OUT / "fa442-run.json", run)
    write_json(OUT / "fa442-jobs.json", {"jobs": jobs})
    root_cause = diagnose(run, jobs, workflow_path, workflow)
    write_json(OUT / "ROOT_CAUSE.json", root_cause)
    (OUT / "ROOT_CAUSE.md").write_text(
        "# FA442 matrix pipeline root cause\n\n"
        f"**Classification:** {root_cause['classification']}\n\n"
        f"**Run:** {root_cause['run_url']}\n\n"
        f"**Workflow:** `{workflow_path}` at `{head_sha}`\n\n"
        f"## Root cause\n\n{root_cause['root_cause']}\n\n"
        "## Actual skipped steps and guards\n\n"
        + "\n".join(
            f"- `{x['job_name']}` — `{x['step_name']}` — `if: {x['condition'] or '<none>'}`"
            for x in root_cause["skipped_steps"]
        )
        + "\n",
        encoding="utf-8",
    )

    found: dict[str, dict[str, Any]] = {}
    artifacts_root = OUT / "downloaded-artifacts"
    manifest_442 = download_run_artifacts(FA442_RUN_ID, artifacts_root / f"run-{FA442_RUN_ID}")
    manifest_423 = download_run_artifacts(FA423_RUN_ID, artifacts_root / f"run-{FA423_RUN_ID}")
    write_json(OUT / "artifact-manifest.json", {
        str(FA442_RUN_ID): manifest_442,
        str(FA423_RUN_ID): manifest_423,
    })
    scan_tree(artifacts_root / f"run-{FA442_RUN_ID}", f"run-{FA442_RUN_ID}", found)
    scan_tree(artifacts_root / f"run-{FA423_RUN_ID}", f"run-{FA423_RUN_ID}", found)
    branches = scan_git_refs(found)
    write_json(OUT / "relevant-branches.json", branches)

    if BASELINE_SHA256 not in found:
        raise RuntimeError(
            f"INFRA_FAILURE: authoritative baseline source {BASELINE_SHA256} was not found "
            "in FA423/FA442 artifacts or relevant remote branches"
        )
    baseline = found[BASELINE_SHA256]
    baseline_data = baseline["data"]
    if line_count_bytes(baseline_data) != BASELINE_LINE_COUNT:
        raise RuntimeError("authoritative baseline line-count mismatch")
    baseline_header = extract_blocker_header(baseline_data)
    baseline_meta = source_metadata(baseline_data)
    baseline_meta["origins"] = baseline["origins"]
    write_json(OUT / "baseline-meta.json", baseline_meta)
    (OUT / "baseline-source.lean").write_bytes(baseline_data)

    variants: list[dict[str, Any]] = []
    used_slugs: set[str] = set()
    ordered = [(BASELINE_SHA256, baseline)] + sorted(
        [(sha, entry) for sha, entry in found.items() if sha != BASELINE_SHA256],
        key=lambda row: (0 if any("31345045760" in x for x in row[1]["origins"]) else 1, row[0]),
    )
    for sha, entry in ordered:
        data = entry["data"]
        if line_count_bytes(data) != BASELINE_LINE_COUNT:
            continue
        try:
            if extract_blocker_header(data) != baseline_header:
                continue
        except Exception:
            continue
        origin = entry["origins"][0] if entry["origins"] else sha[:12]
        variant = "baseline-direct" if sha == BASELINE_SHA256 else origin
        base_slug = slugify("baseline" if sha == BASELINE_SHA256 else variant)
        slug = base_slug
        suffix = 2
        while slug in used_slugs:
            slug = f"{base_slug}-{suffix}"
            suffix += 1
        used_slugs.add(slug)
        target = BUNDLE / slug
        target.mkdir(parents=True)
        (target / "source.lean").write_bytes(data)
        metadata = source_metadata(data)
        metadata.update({
            "variant": variant,
            "slug": slug,
            "is_baseline": sha == BASELINE_SHA256,
            "origins": entry["origins"],
        })
        write_json(target / "metadata.json", metadata)
        variants.append({
            "variant": variant,
            "slug": slug,
            "sha256": sha,
            "is_baseline": sha == BASELINE_SHA256,
        })

    baseline_variants = [v for v in variants if v["is_baseline"]]
    if len(baseline_variants) != 1:
        raise RuntimeError(f"expected exactly one baseline matrix entry, found {len(baseline_variants)}")
    if len(variants) < 2:
        raise RuntimeError(
            "INFRA_FAILURE: no FA442/current candidate sources with unchanged header and same height were recovered"
        )

    matrix = {"include": variants}
    write_json(OUT / "matrix.json", matrix)
    write_json(OUT / "candidate-inventory.json", {
        "baseline_sha256": BASELINE_SHA256,
        "line_count": BASELINE_LINE_COUNT,
        "candidate_count_including_baseline": len(variants),
        "variants": variants,
    })
    append_github_output(matrix=matrix, candidate_count=len(variants),
                         baseline_sha=BASELINE_SHA256)
    print(json.dumps({
        "root_cause": root_cause["root_cause"],
        "candidate_count": len(variants),
        "baseline": baseline_variants[0],
    }, indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        OUT.mkdir(parents=True, exist_ok=True)
        failure = {
            "classification": "INFRA_FAILURE",
            "stage": "prepare",
            "error": repr(exc),
        }
        write_json(OUT / "PREP_INFRA_FAILURE.json", failure)
        print(json.dumps(failure, indent=2), file=sys.stderr)
        raise
