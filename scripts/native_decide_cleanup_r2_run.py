#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time

ERROR_RE = re.compile(r"^(.*\.lean):(\d+):(\d+): error(?:\(([^)]+)\))?:\s*(.*)$")
WARNING_RE = re.compile(r"^.*\.lean:\d+:\d+: warning")
PANIC_RE = re.compile(r"internal error|uncaught exception|panic(!|:| )", re.I)


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: pathlib.Path) -> str:
    return subprocess.check_output(["git", "hash-object", str(path)], text=True).strip()


def run_lean(source: pathlib.Path, out: pathlib.Path, label: str) -> dict[str, object]:
    log = out / f"{label}.log"
    olean = out / f"{label}.olean"
    ilean = out / f"{label}.ilean"
    start = time.time()
    with log.open("w") as handle:
        completed = subprocess.run(
            [
                "lake", "env", "lean",
                "-DmaxErrors=10000", "-DwarningAsError=false",
                "-o", str(olean), "-i", str(ilean), str(source),
            ],
            stdout=handle,
            stderr=subprocess.STDOUT,
            check=False,
        )
    text = log.read_text(errors="replace")
    errors: list[dict[str, object]] = []
    for line in text.splitlines():
        match = ERROR_RE.match(line)
        if match:
            errors.append(
                {
                    "file": match.group(1),
                    "line": int(match.group(2)),
                    "column": int(match.group(3)),
                    "code": match.group(4),
                    "message": match.group(5),
                }
            )
    warnings = sum(bool(WARNING_RE.match(line)) for line in text.splitlines())
    panics = sum(bool(PANIC_RE.search(line)) for line in text.splitlines())
    return {
        "source": str(source),
        "source_sha256": sha256(source),
        "source_blob": git_blob(source),
        "exit": completed.returncode,
        "error_headers": len(errors),
        "warning_headers": warnings,
        "panic_lines": panics,
        "first_error": errors[0] if errors else None,
        "errors": errors,
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
        "elapsed_seconds": int(time.time() - start),
    }


def main() -> None:
    if len(sys.argv) != 7:
        raise SystemExit(
            "usage: run.py VARIANT GENERATOR SPT1_SOURCE MOCK1A_SOURCE OUT WORKTREE_ROOT"
        )
    variant = sys.argv[1]
    generator = pathlib.Path(sys.argv[2])
    spt1_source = pathlib.Path(sys.argv[3])
    mock1a_source = pathlib.Path(sys.argv[4])
    out = pathlib.Path(sys.argv[5])
    worktree = pathlib.Path(sys.argv[6])
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True, exist_ok=True)
    candidate_dir = out / "candidate"
    candidate_dir.mkdir(parents=True, exist_ok=True)
    spt1_candidate = candidate_dir / "Spt1.lean"
    mock1a_candidate = candidate_dir / "Mock1_Advanced.lean"

    with (out / "generator.log").open("w") as handle:
        subprocess.run(
            [
                sys.executable, "-B", str(generator), variant,
                str(spt1_source), str(mock1a_source),
                str(spt1_candidate), str(mock1a_candidate),
            ],
            stdout=handle,
            stderr=subprocess.STDOUT,
            check=True,
        )
    remaining = {
        "Spt1": spt1_candidate.read_text().count("native_decide"),
        "Mock1_Advanced": mock1a_candidate.read_text().count("native_decide"),
    }
    if any(remaining.values()):
        raise SystemExit(f"forbidden token remains: {remaining}")

    canonical_spt1 = worktree / "PrimalitySheafVerification/Spt1.lean"
    canonical_mock1a = worktree / "PrimalitySheafVerification/Mock1_Advanced.lean"
    shutil.copy2(spt1_candidate, canonical_spt1)
    shutil.copy2(mock1a_candidate, canonical_mock1a)

    spt1_result = run_lean(canonical_spt1, out, "Spt1")
    mock1a_result = run_lean(canonical_mock1a, out, "Mock1_Advanced")
    total_errors = int(spt1_result["error_headers"]) + int(mock1a_result["error_headers"])
    total_panics = int(spt1_result["panic_lines"]) + int(mock1a_result["panic_lines"])
    passed = (
        total_errors == 0
        and total_panics == 0
        and spt1_result["exit"] == 0
        and mock1a_result["exit"] == 0
        and spt1_result["olean_exists"] is True
        and spt1_result["ilean_exists"] is True
        and mock1a_result["olean_exists"] is True
        and mock1a_result["ilean_exists"] is True
    )
    result = {
        "schema": "final13-native-decide-cleanup-r2-candidate-v1",
        "authority": "actual direct Lean on both modified canonical paths",
        "variant": variant,
        "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "pass": passed,
        "remaining_native_decide": remaining,
        "total_error_headers": total_errors,
        "total_panic_lines": total_panics,
        "files": {
            "Spt1": spt1_result,
            "Mock1_Advanced": mock1a_result,
        },
    }
    (out / "RESULT.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "variant": variant,
        "pass": passed,
        "total_error_headers": total_errors,
        "total_panic_lines": total_panics,
        "Spt1": {k: v for k, v in spt1_result.items() if k != "errors"},
        "Mock1_Advanced": {k: v for k, v in mock1a_result.items() if k != "errors"},
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
