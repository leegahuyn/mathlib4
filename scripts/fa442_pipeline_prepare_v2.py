from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path
from typing import Any

import fa442_pipeline_prepare as original
from fa442_pipeline_common import BLOCKER, REPO, line_count_bytes, sha256_bytes


def gh_json(endpoint: str) -> Any:
    cp = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github+json", endpoint],
        cwd=REPO,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
        text=True,
    )
    return json.loads(cp.stdout)


def download_run_artifacts_v2(run_id: int, destination: Path) -> list[dict[str, Any]]:
    payload = gh_json(
        f"/repos/{original.REPOSITORY}/actions/runs/{run_id}/artifacts?per_page=100"
    )
    artifacts = payload.get("artifacts", [])
    destination.mkdir(parents=True, exist_ok=True)
    manifest: list[dict[str, Any]] = []
    for artifact in artifacts:
        artifact_id = int(artifact["id"])
        name = str(artifact["name"])
        target = destination / f"{artifact_id}-{original.slugify(name)}"
        target.mkdir(parents=True, exist_ok=True)
        zip_path = target / "artifact.zip"
        try:
            with zip_path.open("wb") as fh:
                cp = subprocess.run(
                    [
                        "gh", "api", "-H", "Accept: application/vnd.github+json",
                        f"/repos/{original.REPOSITORY}/actions/artifacts/{artifact_id}/zip",
                    ],
                    cwd=REPO,
                    stdout=fh,
                    stderr=subprocess.PIPE,
                    check=True,
                )
            with zipfile.ZipFile(zip_path) as archive:
                archive.extractall(target / "content")
            zip_path.unlink(missing_ok=True)
            status = "downloaded_by_gh_api"
        except Exception as exc:
            status = f"download_failed: {exc!r}"
        manifest.append({
            "id": artifact_id,
            "name": name,
            "expired": artifact.get("expired"),
            "status": status,
            "path": str(target.relative_to(original.OUT)),
        })
    return manifest


def candidate_bytes(path: Path) -> bytes | None:
    if path.name == "artifact.zip":
        return None
    return original.candidate_bytes(path)


def scan_git_refs_v2(found: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    refs: set[str] = set()
    page = 1
    while True:
        payload = gh_json(
            f"/repos/{original.REPOSITORY}/branches?per_page=100&page={page}"
        )
        if not payload:
            break
        for row in payload:
            name = str(row.get("name", ""))
            if re.search(
                r"(?:fa42[3-9]|fa4[3-9][0-9]|functional|primality-sheaf-clean-build)",
                name,
                re.I,
            ):
                refs.add(name)
        if len(payload) < 100:
            break
        page += 1

    branch_rows: list[dict[str, Any]] = []
    for name in sorted(refs):
        remote_ref = f"refs/remotes/origin/{name}"
        cp = subprocess.run(
            [
                "git", "fetch", "origin", f"refs/heads/{name}:{remote_ref}",
                "--depth=1",
            ],
            cwd=REPO,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            text=True,
        )
        if cp.returncode != 0:
            branch_rows.append({
                "ref": name,
                "fetch": "failed",
                "stderr": cp.stderr[-1000:],
            })
            continue
        show = subprocess.run(
            [
                "git", "show",
                f"{remote_ref}:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
            ],
            cwd=REPO,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if show.returncode != 0:
            continue
        data = show.stdout
        if f"theorem {BLOCKER}".encode() not in data:
            continue
        sha = sha256_bytes(data)
        entry = found.setdefault(sha, {
            "data": data,
            "origins": [],
            "line_count": line_count_bytes(data),
        })
        entry["origins"].append(f"git:origin/{name}")
        branch_rows.append({
            "ref": f"origin/{name}",
            "fetch": "success",
            "sha256": sha,
            "line_count": line_count_bytes(data),
        })
    return branch_rows


def scan_tree_v2(root: Path, origin_name: str, found: dict[str, dict[str, Any]]) -> None:
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
        entry["origins"].append(f"{origin_name}:{path.relative_to(root)}")


def main() -> None:
    original.download_run_artifacts = download_run_artifacts_v2
    original.scan_git_refs = scan_git_refs_v2
    original.scan_tree = scan_tree_v2
    original.main()


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        original.OUT.mkdir(parents=True, exist_ok=True)
        original.write_json(original.OUT / "PREP_V2_INFRA_FAILURE.json", {
            "classification": "INFRA_FAILURE",
            "stage": "prepare-v2",
            "error": repr(exc),
        })
        raise
