from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PSV = ROOT / "PrimalitySheafVerification"
EVIDENCE = Path(os.environ.get("PASS389_EVIDENCE", "/tmp/pass389-priority"))
STATE = ROOT / "build-logs" / "pass389-priority-state.json"
CHAIN_BRANCH = os.environ.get("PASS389_CHAIN_BRANCH", "fix/fa390-pass389-autorepair-20260809")
PR9_BRANCH = os.environ.get("PASS389_PR9_BRANCH", "ci/fa319-isolated-20260807")
REPO = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
TOKEN = os.environ.get("GH_MODELS_TOKEN") or os.environ.get("GITHUB_TOKEN", "")

FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*(?:public\s+|private\s+)?axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}

TOP_DECL = re.compile(
    r"^(?:private\s+)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma|corollary|def|abbrev|instance|opaque)\b"
)
PUBLIC_PROOF_DECL = re.compile(
    r"^(?!private\b)(?:noncomputable\s+)?(?:theorem|lemma|corollary)\b"
)
ERROR_LINE = re.compile(r"\.lean:(\d+):(\d+):\s*error:")


def run(
    args: list[str],
    *,
    cwd: Path = ROOT,
    check: bool = False,
    timeout: int | None = None,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(args), flush=True)
    proc = subprocess.run(
        args,
        cwd=cwd,
        text=True,
        input=input_text,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    if check and proc.returncode != 0:
        print(proc.stdout[-12000:], file=sys.stderr)
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(args)}")
    return proc


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def api_json(path: str) -> dict:
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN is required")
    request = urllib.request.Request(
        f"https://api.github.com{path}",
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "pass389-priority-repair",
        },
    )
    with urllib.request.urlopen(request, timeout=90) as response:
        return json.loads(response.read().decode("utf-8"))


def api_bytes(path: str) -> bytes:
    request = urllib.request.Request(
        f"https://api.github.com{path}",
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "pass389-priority-repair",
        },
    )
    with urllib.request.urlopen(request, timeout=180) as response:
        return response.read()


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False
    while i < len(text):
        pair = text[i : i + 2]
        ch = text[i]
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            if escaped:
                escaped = False
                out.append(" ")
            elif ch == "\\":
                escaped = True
                out.append(" ")
            elif ch == '"':
                in_string = False
                out.append(" ")
            else:
                out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if pair == "--":
            in_line = True
            out.extend("  ")
            i += 2
        elif pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def trust_audit(path: Path) -> None:
    clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    violations = [name for name, pattern in FORBIDDEN_PATTERNS.items() if pattern.search(clean)]
    if violations:
        raise RuntimeError(f"forbidden proof escape in {path}: {violations}")


def declaration_starts(lines: list[str]) -> list[int]:
    return [i for i, line in enumerate(lines) if TOP_DECL.match(line)]


def declaration_bounds(text: str, error_line: int) -> tuple[int, int]:
    lines = text.splitlines(keepends=True)
    starts = declaration_starts([line.rstrip("\n") for line in lines])
    if not starts:
        raise RuntimeError("no declarations found")
    target = max((s for s in starts if s + 1 <= error_line), default=starts[0])
    later = [s for s in starts if s > target]
    end = min(later) if later else len(lines)
    return target, end


def header_fingerprint(text: str) -> dict[str, str]:
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if PUBLIC_PROOF_DECL.match(line)]
    result: dict[str, str] = {}
    for index, start in enumerate(starts):
        end = starts[index + 1] if index + 1 < len(starts) else len(lines)
        chunk = lines[start:end]
        header_lines: list[str] = []
        found = False
        for line in chunk[:120]:
            if ":=" in line:
                header_lines.append(line.split(":=", 1)[0].rstrip() + " :=")
                found = True
                break
            header_lines.append(line.rstrip())
            if re.search(r"\bwhere\s*$", line):
                found = True
                break
        if not found and len(header_lines) > 40:
            header_lines = header_lines[:40]
        first = lines[start]
        name_match = re.match(
            r"^(?:noncomputable\s+)?(?:theorem|lemma|corollary)\s+([^\s:{(]+)", first
        )
        name = name_match.group(1) if name_match else f"line_{start + 1}"
        normalized = "\n".join(part.strip() for part in header_lines if part.strip())
        result[f"{start + 1}:{name}"] = hashlib.sha256(normalized.encode()).hexdigest()
    return result


def ensure_headers_unchanged(before: dict[str, str], candidate_text: str) -> None:
    after = header_fingerprint(candidate_text)
    if before != after:
        missing = sorted(set(before) - set(after))[:10]
        added = sorted(set(after) - set(before))[:10]
        changed = sorted(k for k in set(before) & set(after) if before[k] != after[k])[:10]
        raise RuntimeError(
            f"public theorem headers changed; missing={missing}, added={added}, changed={changed}"
        )


def output_paths(path: Path) -> tuple[Path, Path]:
    rel = path.relative_to(ROOT).with_suffix("")
    base = ROOT / ".lake" / "build" / "lib" / "lean" / rel
    return base.with_suffix(".olean"), base.with_suffix(".ilean")


def compile_file(path: Path, *, max_errors: int, tag: str, timeout: int = 900) -> dict:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    log = EVIDENCE / f"{tag}.log"
    olean, ilean = output_paths(path)
    olean.parent.mkdir(parents=True, exist_ok=True)
    for output in (olean, ilean):
        output.unlink(missing_ok=True)
    args = [
        "lake",
        "env",
        "lean",
        f"-DmaxErrors={max_errors}",
        "-o",
        str(olean),
        "-i",
        str(ilean),
        str(path.relative_to(ROOT)),
    ]
    started = time.time()
    proc = run(args, timeout=timeout)
    log.write_text(proc.stdout, encoding="utf-8")
    text = proc.stdout
    matches = list(ERROR_LINE.finditer(text))
    first_line = int(matches[0].group(1)) if matches else None
    first_col = int(matches[0].group(2)) if matches else None
    first_block = ""
    if matches:
        start = matches[0].start()
        end = matches[1].start() if len(matches) > 1 else min(len(text), start + 10000)
        first_block = text[start:end]
    result = {
        "path": str(path.relative_to(ROOT)),
        "tag": tag,
        "exit_code": proc.returncode,
        "error_count": len(matches),
        "first_error_line": first_line,
        "first_error_col": first_col,
        "first_error": first_block[-10000:],
        "elapsed_seconds": round(time.time() - started, 2),
        "olean": str(olean.relative_to(ROOT)),
        "ilean": str(ilean.relative_to(ROOT)),
        "outputs_exist": olean.exists() and ilean.exists(),
        "source_sha256": sha256_file(path),
    }
    (EVIDENCE / f"{tag}.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    return result


def better(candidate: dict, baseline: dict) -> bool:
    if candidate["exit_code"] == 0 and candidate["error_count"] == 0:
        return True
    c_line = candidate.get("first_error_line") or 0
    b_line = baseline.get("first_error_line") or 0
    if c_line > b_line:
        return True
    if c_line == b_line and candidate["error_count"] < baseline["error_count"]:
        return True
    if (
        c_line == b_line
        and candidate["error_count"] <= baseline["error_count"]
        and candidate.get("first_error") != baseline.get("first_error")
    ):
        return True
    return False


def download_pass389_candidate(target: Path) -> dict:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    runs: list[dict] = []
    for page in range(1, 8):
        payload = api_json(f"/repos/{REPO}/actions/runs?per_page=100&page={page}")
        page_runs = payload.get("workflow_runs", [])
        if not page_runs:
            break
        for item in page_runs:
            haystack = " ".join(
                str(item.get(key, ""))
                for key in ("name", "display_title", "head_branch", "path")
            )
            if re.search(r"(?:PASS\s*389|fa389|pass389)", haystack, re.I):
                runs.append(item)
    runs.sort(key=lambda item: item.get("created_at", ""), reverse=True)
    audit = EVIDENCE / "pass389-run-candidates.json"
    audit.write_text(json.dumps(runs, indent=2), encoding="utf-8")
    if not runs:
        raise RuntimeError("no PASS 389 workflow run found")

    all_candidates: list[tuple[int, Path, dict, dict]] = []
    for run_item in runs[:12]:
        run_id = run_item["id"]
        artifacts_payload = api_json(f"/repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100")
        artifacts = [a for a in artifacts_payload.get("artifacts", []) if not a.get("expired")]
        for artifact in artifacts:
            name = str(artifact.get("name", ""))
            if not re.search(r"(?:389|functional|priority|frontier)", name, re.I):
                continue
            try:
                data = api_bytes(f"/repos/{REPO}/actions/artifacts/{artifact['id']}/zip")
            except Exception as exc:
                print(f"artifact download failed {artifact['id']}: {exc}")
                continue
            zip_path = EVIDENCE / f"artifact-{artifact['id']}.zip"
            zip_path.write_bytes(data)
            extract = EVIDENCE / f"artifact-{artifact['id']}"
            shutil.rmtree(extract, ignore_errors=True)
            extract.mkdir(parents=True)
            try:
                with zipfile.ZipFile(zip_path) as archive:
                    archive.extractall(extract)
            except zipfile.BadZipFile:
                continue
            for path in extract.rglob("*.lean"):
                if path.name == "Mock2_FunctionalAnalysis.lean" or re.search(
                    r"Mock2_FunctionalAnalysis.*389.*\.lean$", path.name, re.I
                ):
                    if path.stat().st_size > 100000:
                        all_candidates.append((path.stat().st_size, path, run_item, artifact))
    if not all_candidates:
        raise RuntimeError("PASS 389 artifacts contained no FunctionalAnalysis candidate source")
    all_candidates.sort(key=lambda row: row[0], reverse=True)
    _, source, run_item, artifact = all_candidates[0]
    shutil.copy2(source, target)
    return {
        "run_id": run_item["id"],
        "run_name": run_item.get("name"),
        "run_head_branch": run_item.get("head_branch"),
        "run_head_sha": run_item.get("head_sha"),
        "artifact_id": artifact["id"],
        "artifact_name": artifact.get("name"),
        "candidate_path": str(source),
        "candidate_sha256": sha256_file(target),
    }


def extract_code(response: str) -> str | None:
    blocks = re.findall(r"```(?:lean4?|Lean)?\s*\n(.*?)```", response, re.S)
    if blocks:
        return blocks[-1].strip() + "\n"
    begin = response.find("BEGIN_LEAN")
    end = response.find("END_LEAN")
    if begin >= 0 and end > begin:
        return response[begin + len("BEGIN_LEAN") : end].strip() + "\n"
    stripped = response.strip()
    if TOP_DECL.match(stripped.splitlines()[0] if stripped else ""):
        return stripped + "\n"
    return None


def call_model(model: str, prompt: str) -> str | None:
    if not TOKEN:
        return None
    payload = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You are a Lean 4.33.0-rc1 and current Mathlib proof repair expert. "
                    "Never weaken theorem statements or assumptions. Never use sorry, admit, "
                    "new axioms, unsafe, native_decide, or Lean.ofReduceBool."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "max_tokens": 10000,
        "temperature": 0.05,
    }
    request = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        method="POST",
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Content-Type": "application/json",
            "Accept": "application/json",
            "User-Agent": "pass389-priority-repair",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=240) as response:
            body = json.loads(response.read().decode("utf-8"))
        return body["choices"][0]["message"]["content"]
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        print(f"model {model} HTTP {exc.code}: {detail[:2000]}")
    except Exception as exc:
        print(f"model {model} failed: {exc}")
    return None


def repair_prompt(path: Path, source: str, result: dict, start: int, end: int) -> str:
    lines = source.splitlines()
    declaration = "\n".join(lines[start:end])
    context_start = max(0, start - 180)
    context_end = min(len(lines), end + 80)
    context = "\n".join(f"{i + 1}: {lines[i]}" for i in range(context_start, context_end))
    imports = "\n".join(lines[:260])
    return f"""Repair the first independent Lean error in `{path.relative_to(ROOT)}`.

Strict constraints:
- Return exactly one complete replacement for the declaration shown below, in one ```lean code block.
- Keep the declaration header, theorem statement, binders, assumptions, conclusion, namespace and public name exactly unchanged.
- Change only the implementation/proof body. Private helper declarations are not allowed in this response.
- Use existing declarations and current Mathlib APIs.
- Do not use `sorry`, `admit`, a new `axiom`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.
- The replacement must elaborate in Lean 4.33.0-rc1.

Compiler error:
```text
{result.get('first_error', '')}
```

Imports and global setup:
```lean
{imports}
```

Numbered local context:
```text
{context}
```

Declaration to replace:
```lean
{declaration}
```
"""


def repair_until_pass(path: Path, max_cycles: int, models: list[str]) -> tuple[bool, dict]:
    trust_audit(path)
    source = path.read_text(encoding="utf-8")
    frozen_headers = header_fingerprint(source)
    seen = {sha256_file(path)}
    baseline = compile_file(path, max_errors=1, tag=f"{path.stem}-frontier-000")
    same_line_accepts: dict[int, int] = {}
    accepted = 0

    for cycle in range(1, max_cycles + 1):
        if baseline["exit_code"] == 0 and baseline["error_count"] == 0:
            full = compile_file(path, max_errors=250, tag=f"{path.stem}-full-{cycle:03d}")
            if full["exit_code"] == 0 and full["error_count"] == 0:
                return True, full
            baseline = full
        line_no = baseline.get("first_error_line")
        if not line_no:
            return False, baseline
        current = path.read_text(encoding="utf-8")
        start, end = declaration_bounds(current, line_no)
        prompt = repair_prompt(path, current, baseline, start, end)
        original_lines = current.splitlines(keepends=True)
        improved = False

        for model in models:
            response = call_model(model, prompt)
            if not response:
                continue
            (EVIDENCE / f"{path.stem}-cycle-{cycle:03d}-{model.replace('/', '_')}.txt").write_text(
                response, encoding="utf-8"
            )
            replacement = extract_code(response)
            if not replacement:
                continue
            candidate_lines = original_lines[:start] + [replacement] + original_lines[end:]
            candidate_text = "".join(candidate_lines)
            candidate_sha = sha256_bytes(candidate_text.encode("utf-8"))
            if candidate_sha in seen:
                continue
            try:
                ensure_headers_unchanged(frozen_headers, candidate_text)
                tmp = EVIDENCE / f"candidate-{path.stem}-{cycle:03d}.lean"
                tmp.write_text(candidate_text, encoding="utf-8")
                trust_audit(tmp)
            except Exception as exc:
                print(f"rejected {model}: {exc}")
                continue

            backup = path.read_bytes()
            path.write_text(candidate_text, encoding="utf-8")
            candidate = compile_file(
                path,
                max_errors=1,
                tag=f"{path.stem}-candidate-{cycle:03d}-{model.replace('/', '_')}",
            )
            accept = better(candidate, baseline)
            c_line = candidate.get("first_error_line") or 0
            b_line = baseline.get("first_error_line") or 0
            if accept and c_line == b_line:
                used = same_line_accepts.get(b_line, 0)
                if used >= 2:
                    accept = False
                else:
                    same_line_accepts[b_line] = used + 1
            if accept:
                print(
                    f"accepted {model}: line {b_line} -> {c_line}, "
                    f"errors {baseline['error_count']} -> {candidate['error_count']}"
                )
                seen.add(candidate_sha)
                baseline = candidate
                accepted += 1
                improved = True
                if accepted % 6 == 0:
                    full = compile_file(
                        path, max_errors=250, tag=f"{path.stem}-checkpoint-{accepted:03d}"
                    )
                    if full["exit_code"] == 0 and full["error_count"] == 0:
                        return True, full
                    # Keep the frontier result for proof-local progress even if full count is larger.
                break
            path.write_bytes(backup)

        if not improved:
            # Ask one stronger model with a wider declaration-centered prompt before stopping.
            wider = prompt + "\nThe previous candidates did not advance the first compiler error. Re-derive the proof from the exact goal and use explicit type annotations, `change`, `simpa only`, or `ext` as appropriate."
            response = call_model("openai/gpt-5", wider)
            replacement = extract_code(response or "")
            if replacement:
                candidate_text = "".join(original_lines[:start] + [replacement] + original_lines[end:])
                try:
                    ensure_headers_unchanged(frozen_headers, candidate_text)
                    tmp = EVIDENCE / f"candidate-{path.stem}-{cycle:03d}-gpt5.lean"
                    tmp.write_text(candidate_text, encoding="utf-8")
                    trust_audit(tmp)
                    backup = path.read_bytes()
                    path.write_text(candidate_text, encoding="utf-8")
                    candidate = compile_file(path, max_errors=1, tag=f"{path.stem}-candidate-{cycle:03d}-gpt5")
                    if better(candidate, baseline):
                        baseline = candidate
                        accepted += 1
                        improved = True
                    else:
                        path.write_bytes(backup)
                except Exception as exc:
                    print(f"strong-model candidate rejected: {exc}")
            if not improved:
                print(f"no improving candidate at cycle {cycle}; stopping this run")
                break

    full = compile_file(path, max_errors=250, tag=f"{path.stem}-final-frontier")
    return full["exit_code"] == 0 and full["error_count"] == 0, full


def verify_twice(path: Path) -> tuple[bool, list[dict]]:
    results: list[dict] = []
    for index in (1, 2):
        result = compile_file(path, max_errors=250, tag=f"{path.stem}-direct-pass-{index}")
        results.append(result)
        if result["exit_code"] != 0 or result["error_count"] != 0 or not result["outputs_exist"]:
            return False, results
    return True, results


def actual_mock3_files() -> list[Path]:
    return sorted(
        path
        for path in PSV.glob("Mock3*.lean")
        if path.name not in {"Mock3.olean", "Mock3.ilean"}
    )


def git_commit_to_branch(paths: list[Path], branch: str, message: str) -> str:
    run(["git", "config", "user.name", "chatgpt-pass389-repair"], check=True)
    run(["git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com"], check=True)
    for path in paths:
        run(["git", "add", str(path.relative_to(ROOT))], check=True)
    diff = run(["git", "diff", "--cached", "--quiet"])
    if diff.returncode == 0:
        return run(["git", "rev-parse", "HEAD"], check=True).stdout.strip()
    run(["git", "commit", "-m", message], check=True)
    sha = run(["git", "rev-parse", "HEAD"], check=True).stdout.strip()
    run(["git", "push", "origin", f"HEAD:refs/heads/{branch}"], check=True, timeout=300)
    return sha


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fa-cycles", type=int, default=36)
    parser.add_argument("--downstream-cycles", type=int, default=18)
    args = parser.parse_args()

    EVIDENCE.mkdir(parents=True, exist_ok=True)
    STATE.parent.mkdir(parents=True, exist_ok=True)
    fa = PSV / "Mock2_FunctionalAnalysis.lean"
    state: dict = {
        "baseline": "PASS 389",
        "status": "RUNNING",
        "repository": REPO,
        "chain_branch": CHAIN_BRANCH,
        "pr9_branch": PR9_BRANCH,
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "targets": {},
    }

    previous_state = {}
    if STATE.exists():
        try:
            previous_state = json.loads(STATE.read_text(encoding="utf-8"))
        except Exception:
            previous_state = {}

    if previous_state.get("baseline") == "PASS 389" and fa.exists() and fa.stat().st_size > 100000:
        state["bootstrap"] = {"mode": "checked-in-chain-source", "sha256": sha256_file(fa)}
    else:
        state["bootstrap"] = download_pass389_candidate(fa)
    trust_audit(fa)

    models = [
        item.strip()
        for item in os.environ.get(
            "PASS389_MODELS",
            "openai/gpt-5-mini,openai/gpt-4.1,deepseek/DeepSeek-V3-0324,xai/grok-3-mini",
        ).split(",")
        if item.strip()
    ]

    fa_ok, fa_frontier = repair_until_pass(fa, args.fa_cycles, models)
    state["targets"][fa.name] = {"repair_pass": fa_ok, "frontier": fa_frontier}
    if fa_ok:
        fa_ok, fa_runs = verify_twice(fa)
        state["targets"][fa.name]["direct_runs"] = fa_runs
        state["targets"][fa.name]["two_pass"] = fa_ok

    touched = [fa, STATE]
    if not fa_ok:
        state["status"] = "FA_INCOMPLETE"
        state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        sha = git_commit_to_branch(touched, CHAIN_BRANCH, "fix: advance PASS 389 FunctionalAnalysis frontier")
        state["published_commit"] = sha
        STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        print(json.dumps(state, indent=2))
        return 2

    ordered: list[Path] = []
    integrated = PSV / "Mock2_FunctionalAnalysis_Integrated.lean"
    if integrated.exists():
        ordered.append(integrated)
    ordered.extend(actual_mock3_files())
    qym = PSV / "QYM.lean"
    if qym.exists():
        ordered.append(qym)

    for target in ordered:
        trust_audit(target)
        ok, frontier = repair_until_pass(target, args.downstream_cycles, models)
        state["targets"][target.name] = {"repair_pass": ok, "frontier": frontier}
        touched.append(target)
        if ok:
            ok, direct = verify_twice(target)
            state["targets"][target.name]["direct_runs"] = direct
            state["targets"][target.name]["two_pass"] = ok
        if not ok:
            state["status"] = f"{target.name}_INCOMPLETE"
            state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
            sha = git_commit_to_branch(touched + [STATE], CHAIN_BRANCH, f"fix: advance PASS 389 {target.stem} frontier")
            state["published_commit"] = sha
            STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
            print(json.dumps(state, indent=2))
            return 3

    required = [fa]
    if integrated.exists():
        required.append(integrated)
    required.extend(actual_mock3_files())
    if qym.exists():
        required.append(qym)
    all_ok = all(state["targets"].get(path.name, {}).get("two_pass") for path in required)
    if not all_ok:
        raise RuntimeError("internal final-gate mismatch")

    state["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
    state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    marker = ROOT / "build-logs" / "PR9_FA_INTEGRATED_MOCK3_QYM_FINAL_2X_PASS.json"
    marker.write_text(json.dumps(state, indent=2), encoding="utf-8")
    touched.extend([STATE, marker])
    STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")

    # The current job has independently compiled every target twice. Publish the checked-in
    # sources to PR #9, but never merge the PR.
    sha = git_commit_to_branch(touched, PR9_BRANCH, "fix: materialize PASS 389 FA Mock3 QYM two-pass sources")
    state["published_commit"] = sha
    STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
    print(json.dumps(state, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
