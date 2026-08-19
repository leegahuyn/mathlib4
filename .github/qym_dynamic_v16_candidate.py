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
import time

QYM = Path("PrimalitySheafVerification/QYM.lean")
STATUS = Path(".github/qym-frontier/V14B_LIVE_STATUS.json")
PATCHER = Path(".github/qym_patch_dynamic_v16_groupoid.py")
VARIANTS = {"explicit_helpers", "fact_bridge", "inline_duplicate"}
DIAG = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def dump(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_log(log: Path, variant: str, phase: str, returncode: int, elapsed: float) -> dict:
    raw = log.read_bytes()
    text = raw.decode("utf-8", errors="replace")
    diagnostics: list[dict] = []
    for match in DIAG.finditer(text):
        row = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        diagnostics.append(row)
    errors = [row for row in diagnostics if row["severity"] == "error"]
    warnings = [row for row in diagnostics if row["severity"] == "warning"]
    return {
        "variant": variant,
        "phase": phase,
        "exit": returncode,
        "elapsed_seconds": round(elapsed, 3),
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(PANIC.findall(text)),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "errors": errors,
        "error_codes": dict(
            sorted(collections.Counter((row.get("code") or "uncoded") for row in errors).items())
        ),
        "log_sha256": sha(raw),
    }


def compile_qym(out: Path, variant: str, phase: str, max_errors: int) -> dict:
    log = out / f"{phase}.log"
    olean = out / f"{phase}.olean"
    ilean = out / f"{phase}.ilean"
    cmd = [
        "lake", "env", "lean", f"-DmaxErrors={max_errors}", "-DwarningAsError=false",
        "-o", str(olean), "-i", str(ilean), str(QYM),
    ]
    started = time.monotonic()
    with log.open("wb") as handle:
        proc = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT)
    result = parse_log(log, variant, phase, proc.returncode, time.monotonic() - started)
    result.update({
        "command": cmd,
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
        "olean_bytes": olean.stat().st_size if olean.is_file() else 0,
        "ilean_bytes": ilean.stat().st_size if ilean.is_file() else 0,
    })
    dump(out / f"{phase.upper()}_RESULT.json", result)
    return result


def main() -> int:
    if len(sys.argv) != 2 or sys.argv[1] not in VARIANTS:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} VARIANT")
    variant = sys.argv[1]
    run_id = os.environ.get("GITHUB_RUN_ID", "manual")
    out = Path(os.environ.get("OUT_ROOT", "/tmp/qym-dynamic-v16")) / variant
    out.mkdir(parents=True, exist_ok=True)

    status = json.loads(STATUS.read_text(encoding="utf-8"))
    if status.get("status") != "PROMOTED_FROM_GB77":
        raise SystemExit(f"V14b promotion authority missing: {status}")
    base_errors = int(status["error_headers"])
    base_sha = str(status["qym_sha256"])
    base_blob = str(status["qym_blob"])
    sidecar = Path(f".github/qym-frontier/QYM_GB{base_errors}_BEST.lean")
    qym_raw = QYM.read_bytes()
    sidecar_raw = sidecar.read_bytes()
    gate = {
        "status": status,
        "qym_sha256": sha(qym_raw),
        "qym_blob": blob(qym_raw),
        "sidecar": str(sidecar),
        "sidecar_sha256": sha(sidecar_raw),
        "sidecar_blob": blob(sidecar_raw),
        "qym_equals_sidecar": qym_raw == sidecar_raw,
    }
    dump(out / "AUTHORITY_GATE.json", gate)
    if not (
        gate["qym_sha256"] == base_sha
        and gate["qym_blob"] == base_blob
        and gate["sidecar_sha256"] == base_sha
        and gate["sidecar_blob"] == base_blob
        and gate["qym_equals_sidecar"]
    ):
        raise SystemExit(f"dynamic authority gate failed: {gate}")

    original = out / f"QYM.GB{base_errors}.authority.lean"
    candidate = out / "QYM.candidate.lean"
    shutil.copy2(QYM, original)
    result: dict = {
        "schema": "qym-dynamic-v16-groupoid-result-v1",
        "run_id": int(run_id) if run_id.isdigit() else run_id,
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "branch": os.environ.get("GITHUB_REF_NAME"),
        "variant": variant,
        "baseline_error_headers": base_errors,
        "baseline_qym_sha256": base_sha,
        "baseline_qym_blob": base_blob,
        "target_cluster": "ConditionalSmoothAtlas parameterized instances",
        "full_compile_executed": False,
        "strict_improvement": False,
        "semantic_pass": False,
    }

    try:
        patch_log = out / "PATCH_RESULT.json"
        cmd = [
            sys.executable, "-B", str(PATCHER), variant, str(original), str(candidate),
            base_sha, base_blob, str(base_errors),
        ]
        with patch_log.open("wb") as handle:
            subprocess.run(cmd, check=True, stdout=handle, stderr=subprocess.STDOUT)
        patch = json.loads(patch_log.read_text(encoding="utf-8"))
        forbidden = patch.get("forbidden") or {}
        if any(int(value) for value in forbidden.values()):
            raise SystemExit(f"forbidden proof escape in candidate: {forbidden}")
        candidate_raw = candidate.read_bytes()
        result.update({
            "patch": patch,
            "forbidden": forbidden,
            "candidate_qym_sha256": sha(candidate_raw),
            "candidate_qym_blob": blob(candidate_raw),
        })

        shutil.copy2(candidate, QYM)
        local = compile_qym(out, variant, "local", 8)
        lo = int(patch["section_start_line"])
        hi = int(patch["section_end_line"])
        section_errors = [error for error in local["errors"] if lo <= int(error["line"]) <= hi]
        earlier_errors = [error for error in local["errors"] if int(error["line"]) < lo]
        first = local.get("first_error")
        advanced = first is None or int(first["line"]) > hi
        local_gate_pass = (
            int(local["panic_lines"]) == 0
            and not section_errors
            and not earlier_errors
            and advanced
        )
        result.update({
            "local": local,
            "section_errors": section_errors,
            "earlier_errors": earlier_errors,
            "local_gate_pass": local_gate_pass,
            "first_blocker_advanced": advanced,
        })

        if local_gate_pass:
            full = compile_qym(out, variant, "full", 10000)
            semantic = (
                int(full["exit"]) == 0
                and int(full["error_headers"]) == 0
                and int(full["panic_lines"]) == 0
                and bool(full["olean_exists"])
                and bool(full["ilean_exists"])
            )
            strict = semantic or (
                int(full["panic_lines"]) == 0
                and int(full["error_headers"]) < base_errors
            )
            result.update({
                "full_compile_executed": True,
                "full": full,
                "exit": full["exit"],
                "error_headers": full["error_headers"],
                "warning_headers": full["warning_headers"],
                "panic_lines": full["panic_lines"],
                "first_error": full["first_error"],
                "last_error": full["last_error"],
                "error_codes": full["error_codes"],
                "log_sha256": full["log_sha256"],
                "semantic_pass": semantic,
                "strict_improvement": strict,
            })
        dump(out / "RESULT.json", result)
        return 0
    finally:
        shutil.copy2(original, QYM)


if __name__ == "__main__":
    raise SystemExit(main())
