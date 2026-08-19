#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import zipfile

REPO = os.environ.get("REPO", "leegahuyn/mathlib4")
QYM = Path(os.environ.get("QYM", "PrimalitySheafVerification/QYM.lean"))
OUT = Path(os.environ.get("OUT", "/tmp/qym-gb85-c2-v9"))
ARTIFACT_ID = os.environ.get("BASELINE_ARTIFACT", "9354072137")
BASE_SOURCE_NAME = "QYM.candidate-C04-mul_inv_using_bang.lean"
BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"
BASE_ERRORS = 85
BASE_RUN_ID = "32218198562"
VARIANT = "change_pointwise_keep_trace"
PATCHER = Path(".github/qym_patch_gb85_c2_v9.py")

DIAG_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_checked(command: list[str], *, stdout=None) -> None:
    subprocess.run(command, check=True, stdout=stdout)


def recover_baseline() -> Path:
    OUT.mkdir(parents=True, exist_ok=True)
    base_dir = OUT / "baseline"
    if base_dir.exists():
        shutil.rmtree(base_dir)
    base_dir.mkdir(parents=True)
    archive = OUT / "gb85.zip"
    with archive.open("wb") as handle:
        run_checked(
            [
                "gh",
                "api",
                "-H",
                "Accept: application/vnd.github+json",
                f"repos/{REPO}/actions/artifacts/{ARTIFACT_ID}/zip",
            ],
            stdout=handle,
        )
    with zipfile.ZipFile(archive) as zf:
        zf.extractall(base_dir)

    sources = list(base_dir.rglob(BASE_SOURCE_NAME))
    results = list(base_dir.rglob("RESULT.json"))
    if len(sources) != 1 or len(results) != 1:
        raise RuntimeError(
            f"expected one GB85 source/result; got sources={len(sources)} results={len(results)}"
        )

    source = sources[0]
    raw = source.read_bytes()
    result = json.loads(results[0].read_text(encoding="utf-8"))
    checks = {
        "sha256": sha256(raw) == BASE_SHA256,
        "blob": git_blob(raw) == BASE_BLOB,
        "result_sha256": result.get("candidate_qym_sha256") == BASE_SHA256,
        "result_blob": result.get("candidate_qym_blob") == BASE_BLOB,
        "errors": int(result.get("error_headers", -1)) == BASE_ERRORS,
        "exit": int(result.get("exit", -1)) == 1,
        "panic": int(result.get("panic_lines", -1)) == 0,
        "run_id": str(result.get("run_id")) == BASE_RUN_ID,
    }
    write_json(OUT / "BASELINE_CHECK.json", {"checks": checks, "result": result})
    if not all(checks.values()):
        raise RuntimeError(f"GB85 baseline verification failed: {checks}")

    frozen = OUT / "QYM.GB85.lean"
    shutil.copy2(source, frozen)
    return frozen


def parse_log(log_path: Path) -> tuple[list[dict[str, object]], list[str]]:
    raw = log_path.read_bytes() if log_path.exists() else b""
    text = raw.decode(errors="replace")
    rows: list[dict[str, object]] = []
    for match in DIAG_RE.finditer(text):
        row: dict[str, object] = match.groupdict()
        row["line"] = int(str(row["line"]))
        row["column"] = int(str(row["column"]))
        rows.append(row)
    return rows, PANIC_RE.findall(text)


def compile_candidate(candidate: Path, phase: str, max_errors: int) -> dict[str, object]:
    shutil.copy2(candidate, QYM)
    log_path = OUT / f"{VARIANT}.{phase}.log"
    time_path = OUT / f"{VARIANT}.{phase}.time"
    exit_path = OUT / f"{VARIANT}.{phase}.exit"
    olean = OUT / f"{VARIANT}.{phase}.olean"
    ilean = OUT / f"{VARIANT}.{phase}.ilean"
    for path in (olean, ilean):
        path.unlink(missing_ok=True)

    command = [
        "/usr/bin/time",
        "-v",
        "-o",
        str(time_path),
        "lake",
        "env",
        "lean",
        f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false",
        "-o",
        str(olean),
        "-i",
        str(ilean),
        str(QYM),
    ]
    with log_path.open("wb") as handle:
        process = subprocess.run(command, stdout=handle, stderr=subprocess.STDOUT)
    exit_path.write_text(str(process.returncode) + "\n", encoding="utf-8")

    rows, panics = parse_log(log_path)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    (OUT / f"{VARIANT}.{phase}.diagnostics.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )
    raw_log = log_path.read_bytes()
    return {
        "phase": phase,
        "variant": VARIANT,
        "exit": process.returncode,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(
            sorted(
                collections.Counter(
                    str(row.get("code") or "uncoded") for row in errors
                ).items()
            )
        ),
        "log_sha256": sha256(raw_log),
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
        "olean_sha256": sha256(olean.read_bytes()) if olean.is_file() else None,
        "ilean_sha256": sha256(ilean.read_bytes()) if ilean.is_file() else None,
    }


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    canonical = OUT / "QYM.checked-in.lean"
    shutil.copy2(QYM, canonical)
    try:
        baseline = recover_baseline()
        candidate = OUT / f"QYM.candidate-{VARIANT}.lean"
        shutil.copy2(baseline, candidate)

        patch_path = OUT / "PATCH_RESULT.json"
        with patch_path.open("wb") as handle:
            run_checked(
                [sys.executable, "-B", str(PATCHER), VARIANT, str(candidate)],
                stdout=handle,
            )
        patch = json.loads(patch_path.read_text(encoding="utf-8"))
        raw = candidate.read_bytes()
        if patch.get("input_sha256") != BASE_SHA256 or patch.get("input_blob") != BASE_BLOB:
            raise RuntimeError("patch input identity mismatch")
        if patch.get("candidate_sha256") != sha256(raw) or patch.get("candidate_blob") != git_blob(raw):
            raise RuntimeError("patch output identity mismatch")
        if any(int(value) != 0 for value in (patch.get("forbidden") or {}).values()):
            raise RuntimeError("forbidden audit failure")

        local = compile_candidate(candidate, "local", 1)
        gate_line = int(patch["gate_line"])
        first_local = local.get("first_error") or {}
        first_local_line = int(first_local.get("line") or 10**9)
        local_gate_pass = (
            int(local.get("panic_lines", 1)) == 0
            and (
                int(local.get("exit", 1)) == 0
                or first_local_line >= gate_line
            )
        )
        local["gate_line"] = gate_line
        local["producer_fixed"] = local_gate_pass
        write_json(OUT / "LOCAL_RESULT.json", local)

        selection: dict[str, object] = {
            "schema": "qym-gb85-c2-v9-selection-v1",
            "baseline": {
                "artifact_id": int(ARTIFACT_ID),
                "run_id": int(BASE_RUN_ID),
                "error_headers": BASE_ERRORS,
                "qym_sha256": BASE_SHA256,
                "qym_blob": BASE_BLOB,
            },
            "variant": VARIANT,
            "patch": patch,
            "local": local,
            "local_gate_pass": local_gate_pass,
            "full_compile_executed": False,
            "strict_improvement_found": False,
        }
        if not local_gate_pass:
            write_json(OUT / "SELECTION.json", selection)
            print(json.dumps(selection, indent=2, sort_keys=True))
            return 2

        full = compile_candidate(candidate, "full", 10000)
        semantic_pass = (
            int(full["exit"]) == 0
            and int(full["error_headers"]) == 0
            and int(full["panic_lines"]) == 0
            and bool(full["olean_exists"])
            and bool(full["ilean_exists"])
        )
        strict_improvement = semantic_pass or (
            int(full["exit"]) == 1
            and int(full["panic_lines"]) == 0
            and 0 < int(full["error_headers"]) < BASE_ERRORS
        )
        full.update({
            "schema": "qym-gb85-c2-v9-full-result-v1",
            "semantic_pass": semantic_pass,
            "strict_improvement": strict_improvement,
            "baseline_error_headers": BASE_ERRORS,
            "candidate_qym_sha256": patch["candidate_sha256"],
            "candidate_qym_blob": patch["candidate_blob"],
            "run_id": os.environ.get("GITHUB_RUN_ID"),
            "trigger_sha": os.environ.get("GITHUB_SHA"),
        })
        write_json(OUT / "FULL_RESULT.json", full)
        selection.update({
            "full_compile_executed": True,
            "full": full,
            "strict_improvement_found": strict_improvement,
        })
        write_json(OUT / "SELECTION.json", selection)
        print(json.dumps(selection, indent=2, sort_keys=True))

        if not strict_improvement:
            return 2
        shutil.copy2(candidate, OUT / "QYM.best.lean")
        write_json(OUT / "BEST_RESULT.json", full)
        return 0
    except Exception as exc:
        (OUT / "FATAL.txt").write_text(
            f"{type(exc).__name__}: {exc}\n", encoding="utf-8"
        )
        raise
    finally:
        if canonical.exists():
            shutil.copy2(canonical, QYM)


if __name__ == "__main__":
    raise SystemExit(main())
