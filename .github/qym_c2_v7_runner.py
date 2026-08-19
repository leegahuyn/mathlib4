#!/usr/bin/env python3
from __future__ import annotations

import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

REPO = os.environ.get("REPO", "leegahuyn/mathlib4")
BRANCH = os.environ.get("BRANCH", "gpt/qym-gb85-c2-v6-mulinv-20260819")
QYM = Path(os.environ.get("QYM", "PrimalitySheafVerification/QYM.lean"))
OUT = Path(os.environ.get("OUT", "/tmp/qym-gb85-c2-mulinv-v7"))
BASE = Path(os.environ.get("BASE", "/tmp/qym-gb85-c2-mulinv-v7-base"))
ARTIFACT_ID = os.environ.get("ARTIFACT_ID", "9354072137")
BASE_SHA256 = os.environ.get(
    "BASE_SHA256",
    "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210",
)
BASE_BLOB = os.environ.get("BASE_BLOB", "bd28d0436230a8f0bcb01806dac01787542256b8")
BASE_ERRORS = int(os.environ.get("BASE_ERRORS", "85"))
PATCH_SCRIPT = Path(".github/qym_patch_gb85_c2_mulinv_v6.py")
VARIANTS = (
    "ofreal_apply_mulinv_simpa",
    "ofreal_apply_mulinv_rw",
    "ofreal_apply_mulinv_change",
)
DIAGNOSTIC_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*"
    r"(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run(
    args: list[str],
    *,
    stdout_path: Path | None = None,
    check: bool = False,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    if stdout_path is None:
        completed = subprocess.run(args, env=merged_env, check=False)
    else:
        stdout_path.parent.mkdir(parents=True, exist_ok=True)
        with stdout_path.open("wb") as handle:
            completed = subprocess.run(
                args,
                stdout=handle,
                stderr=subprocess.STDOUT,
                env=merged_env,
                check=False,
            )
    if check and completed.returncode != 0:
        raise SystemExit(f"command failed ({completed.returncode}): {' '.join(args)}")
    return completed


def parse_diagnostics(log_path: Path) -> tuple[list[dict[str, object]], list[str]]:
    raw = log_path.read_bytes() if log_path.is_file() else b""
    text = raw.decode(errors="replace")
    rows: list[dict[str, object]] = []
    for match in DIAGNOSTIC_RE.finditer(text):
        row: dict[str, object] = match.groupdict()
        row["line"] = int(str(row["line"]))
        row["column"] = int(str(row["column"]))
        rows.append(row)
    return rows, PANIC_RE.findall(text)


def recover() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    BASE.mkdir(parents=True, exist_ok=True)
    archive = OUT / "gb85.zip"
    run(
        [
            "gh",
            "api",
            "-H",
            "Accept: application/vnd.github+json",
            f"repos/{REPO}/actions/artifacts/{ARTIFACT_ID}/zip",
        ],
        stdout_path=archive,
        check=True,
    )
    with zipfile.ZipFile(archive) as zf:
        zf.extractall(BASE)

    sources: list[Path] = []
    for path in BASE.rglob("*.lean"):
        raw = path.read_bytes()
        if sha256_bytes(raw) == BASE_SHA256 and git_blob(raw) == BASE_BLOB:
            sources.append(path)
    if len(sources) != 1:
        raise SystemExit(f"exact GB85 source count={len(sources)}")

    results: list[tuple[Path, dict[str, object]]] = []
    for path in BASE.rglob("RESULT.json"):
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if (
            value.get("candidate_qym_sha256") == BASE_SHA256
            and value.get("candidate_qym_blob") == BASE_BLOB
            and int(value.get("error_headers", -1)) == BASE_ERRORS
            and int(value.get("panic_lines", -1)) == 0
            and bool(value.get("full_compile_executed", True))
        ):
            results.append((path, value))
    if len(results) != 1:
        raise SystemExit(f"verified GB85 RESULT count={len(results)}")

    target = OUT / "QYM.GB85.lean"
    shutil.copy2(sources[0], target)
    write_json(OUT / "GB85_RESULT.json", results[0][1])
    summary = {
        "source": str(sources[0]),
        "sha256": BASE_SHA256,
        "blob": BASE_BLOB,
        "errors": BASE_ERRORS,
        "result": str(results[0][0]),
    }
    write_json(OUT / "RECOVERY.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))


def compile_candidate(variant: str, baseline: Path) -> dict[str, object]:
    directory = OUT / variant
    directory.mkdir(parents=True, exist_ok=True)
    shutil.copy2(baseline, QYM)

    patch_result_path = directory / "PATCH_RESULT.json"
    patch = run(
        [sys.executable, "-B", str(PATCH_SCRIPT), variant, str(QYM)],
        stdout_path=patch_result_path,
    )
    if patch.returncode != 0:
        raise SystemExit(f"patch failed for {variant}")
    patch_result = json.loads(patch_result_path.read_text(encoding="utf-8"))
    if patch_result.get("input_sha256") != BASE_SHA256:
        raise SystemExit(f"input SHA mismatch for {variant}")
    if patch_result.get("input_blob") != BASE_BLOB:
        raise SystemExit(f"input blob mismatch for {variant}")
    if sum(int(value) for value in patch_result.get("forbidden", {}).values()) != 0:
        raise SystemExit(f"forbidden construct detected for {variant}")
    source_path = directory / "QYM.candidate.lean"
    shutil.copy2(QYM, source_path)

    runner_temp = Path(os.environ.get("RUNNER_TEMP", "/tmp"))
    local_olean = runner_temp / f"{variant}.local.olean"
    local_ilean = runner_temp / f"{variant}.local.ilean"
    local_log = directory / "local.log"
    for path in (local_olean, local_ilean):
        path.unlink(missing_ok=True)
    local = run(
        [
            "lake",
            "env",
            "lean",
            "-DmaxErrors=1",
            "-DwarningAsError=false",
            "-o",
            str(local_olean),
            "-i",
            str(local_ilean),
            str(QYM),
        ],
        stdout_path=local_log,
    )
    (directory / "local.exit").write_text(f"{local.returncode}\n", encoding="utf-8")
    local_rows, local_panics = parse_diagnostics(local_log)
    local_errors = [row for row in local_rows if row["severity"] == "error"]
    first_local = local_errors[0] if local_errors else None
    gate_line = int(patch_result["gate_line"])
    c2_fixed = not local_panics and (
        local.returncode == 0
        or (first_local is not None and int(first_local["line"]) >= gate_line)
    )
    local_result = {
        "variant": variant,
        "exit": local.returncode,
        "gate_line": gate_line,
        "first_error": first_local,
        "panic_lines": len(local_panics),
        "c2_fixed": c2_fixed,
    }
    write_json(directory / "LOCAL_RESULT.json", local_result)

    executed = False
    full_returncode: int | None = None
    full_log = directory / "full.log"
    full_olean = runner_temp / f"{variant}.QYM.olean"
    full_ilean = runner_temp / f"{variant}.QYM.ilean"
    for path in (full_olean, full_ilean):
        path.unlink(missing_ok=True)
    if c2_fixed:
        full = run(
            [
                "lake",
                "env",
                "lean",
                "-DmaxErrors=10000",
                "-DwarningAsError=false",
                "-o",
                str(full_olean),
                "-i",
                str(full_ilean),
                str(QYM),
            ],
            stdout_path=full_log,
        )
        executed = True
        full_returncode = full.returncode
        (directory / "full.exit").write_text(
            f"{full.returncode}\n", encoding="utf-8"
        )

    rows, panics = parse_diagnostics(full_log) if executed else ([], [])
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    semantic_pass = (
        executed
        and full_returncode == 0
        and not errors
        and not panics
        and full_olean.is_file()
        and full_olean.stat().st_size > 0
        and full_ilean.is_file()
        and full_ilean.stat().st_size > 0
    )
    strict_improvement = executed and (
        semantic_pass
        or (
            full_returncode == 1
            and not panics
            and 0 < len(errors) < BASE_ERRORS
        )
    )
    if semantic_pass:
        shutil.copy2(full_olean, directory / "QYM.olean")
        shutil.copy2(full_ilean, directory / "QYM.ilean")

    raw_log = full_log.read_bytes() if executed and full_log.is_file() else b""
    result: dict[str, object] = {
        "schema": "qym-gb85-c2-mulinv-v7-result",
        "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "variant": variant,
        "baseline_qym_sha256": BASE_SHA256,
        "baseline_qym_blob": BASE_BLOB,
        "baseline_error_headers": BASE_ERRORS,
        "candidate_qym_sha256": patch_result["candidate_sha256"],
        "candidate_qym_blob": patch_result["candidate_blob"],
        "forbidden": patch_result["forbidden"],
        "full_compile_executed": executed,
        "exit": full_returncode,
        "error_headers": len(errors) if executed else None,
        "warning_headers": len(warnings) if executed else None,
        "panic_lines": len(panics) if executed else None,
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(
            sorted(collections.Counter(str(row.get("code") or "uncoded") for row in errors).items())
        )
        if executed
        else {},
        "log_sha256": sha256_bytes(raw_log) if executed else None,
        "semantic_pass": semantic_pass,
        "strict_improvement": strict_improvement,
        "local": local_result,
        "source": str(source_path),
    }
    write_json(directory / "RESULT.json", result)
    (directory / "diagnostics.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )
    (directory / "error-headers.txt").write_text(
        "".join(
            f"{row['file']}:{row['line']}:{row['column']}: error"
            f"{('(' + str(row['code']) + ')') if row.get('code') else ''}: "
            f"{row['message']}\n"
            for row in errors
        ),
        encoding="utf-8",
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


def rank(row: dict[str, object]) -> tuple[object, ...]:
    first = row.get("first_error") or {}
    assert isinstance(first, dict)
    errors = row.get("error_headers")
    panics = row.get("panic_lines")
    return (
        0 if row.get("semantic_pass") else 1,
        int(errors) if errors is not None else 10**9,
        int(panics) if panics is not None else 10**9,
        -int(first.get("line") or 0),
        str(row.get("variant") or ""),
    )


def promote(best: dict[str, object], selection: dict[str, object]) -> None:
    source = Path(str(best["source"]))
    best_copy = OUT / "QYM.C2.V7.BEST.lean"
    shutil.copy2(source, best_copy)
    result_path = OUT / "C2_V7_RESULT.json"
    selection_path = OUT / "SELECTION.json"
    write_json(result_path, best)
    write_json(selection_path, selection)

    expected = str(best["candidate_qym_sha256"])
    if sha256_bytes(best_copy.read_bytes()) != expected:
        raise SystemExit("selected source SHA mismatch")
    if not bool(best.get("strict_improvement")):
        raise SystemExit("selected source is not a strict improvement")
    if int(best.get("panic_lines") or 0) != 0:
        raise SystemExit("selected source has panic lines")
    errors = int(best.get("error_headers") or 0)
    if not bool(best.get("semantic_pass")) and errors >= BASE_ERRORS:
        raise SystemExit("selected source does not reduce errors")

    github_sha = os.environ.get("GITHUB_SHA")
    if not github_sha:
        raise SystemExit("GITHUB_SHA missing")
    run(["git", "fetch", "origin", BRANCH], check=True)
    remote_head = subprocess.check_output(
        ["git", "rev-parse", f"origin/{BRANCH}"], text=True
    ).strip()
    if remote_head != github_sha:
        raise SystemExit(f"branch moved during run: {remote_head} != {github_sha}")
    run(["git", "checkout", "-B", BRANCH, github_sha], check=True)

    frontier = Path(".github/qym-frontier")
    frontier.mkdir(parents=True, exist_ok=True)
    shutil.copy2(best_copy, frontier / "QYM_C2_V7_BEST.lean")
    shutil.copy2(result_path, frontier / "C2_V7_RESULT.json")
    shutil.copy2(selection_path, frontier / "C2_V7_SELECTION.json")
    shutil.copy2(best_copy, QYM)

    run(["git", "config", "user.name", "github-actions[bot]"], check=True)
    run(
        [
            "git",
            "config",
            "user.email",
            "41898282+github-actions[bot]@users.noreply.github.com",
        ],
        check=True,
    )
    run(
        [
            "git",
            "add",
            str(QYM),
            str(frontier / "QYM_C2_V7_BEST.lean"),
            str(frontier / "C2_V7_RESULT.json"),
            str(frontier / "C2_V7_SELECTION.json"),
        ],
        check=True,
    )
    label = "PASS" if bool(best.get("semantic_pass")) else f"{errors}-error"
    run(["git", "commit", "-m", f"QYM C2 v7: promote verified {label} frontier"], check=True)
    run(["git", "push", "origin", f"HEAD:{BRANCH}"], check=True)


def tournament() -> None:
    baseline = OUT / "QYM.GB85.lean"
    if not baseline.is_file():
        raise SystemExit("recovered GB85 source is missing")
    raw = baseline.read_bytes()
    if sha256_bytes(raw) != BASE_SHA256 or git_blob(raw) != BASE_BLOB:
        raise SystemExit("recovered GB85 source changed")
    if not PATCH_SCRIPT.is_file():
        raise SystemExit("patch script is missing")

    checked_in = OUT / "QYM.checked-in.lean"
    shutil.copy2(QYM, checked_in)
    results: list[dict[str, object]] = []
    try:
        for variant in VARIANTS:
            results.append(compile_candidate(variant, baseline))
    finally:
        shutil.copy2(checked_in, QYM)

    results.sort(key=rank)
    valid = [row for row in results if bool(row.get("strict_improvement"))]
    best = valid[0] if valid else None
    selection: dict[str, object] = {
        "schema": "qym-gb85-c2-mulinv-v7-selection",
        "baseline_error_headers": BASE_ERRORS,
        "best": best,
        "all": results,
        "promoted": best is not None,
    }
    write_json(OUT / "SELECTION.json", selection)
    print(json.dumps(selection, indent=2, sort_keys=True))
    if best is None:
        raise SystemExit("no corrected C2 candidate strictly improved GB85")
    promote(best, selection)


def main() -> None:
    if len(sys.argv) != 2 or sys.argv[1] not in {"recover", "tournament"}:
        raise SystemExit("usage: qym_c2_v7_runner.py recover|tournament")
    if sys.argv[1] == "recover":
        recover()
    else:
        tournament()


if __name__ == "__main__":
    main()
