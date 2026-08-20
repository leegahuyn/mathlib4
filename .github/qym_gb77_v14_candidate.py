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
SIDECAR = Path(".github/qym-frontier/QYM_GB77_BEST.lean")
PATCHER = Path(".github/qym_patch_gb77_v14_right_normal_im.py")
BASE_SHA = "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd"
BASE_BLOB = "c6e8883353b350f22b7f48d955fc5cfa4e61f88f"
BASE_ERRORS = 77
BASE_WARNINGS = 360
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


def parse_log(log: Path, variant: str, phase: str, proc: subprocess.CompletedProcess[bytes], elapsed: float) -> dict:
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
        "exit": proc.returncode,
        "elapsed_seconds": round(elapsed, 3),
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(PANIC.findall(text)),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "errors": errors,
        "error_codes": dict(sorted(collections.Counter((row.get("code") or "uncoded") for row in errors).items())),
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
    result = parse_log(log, variant, phase, proc, time.monotonic() - started)
    result["command"] = cmd
    result["olean_exists"] = olean.is_file() and olean.stat().st_size > 0
    result["ilean_exists"] = ilean.is_file() and ilean.stat().st_size > 0
    result["olean_bytes"] = olean.stat().st_size if olean.is_file() else 0
    result["ilean_bytes"] = ilean.stat().st_size if ilean.is_file() else 0
    dump(out / f"{phase.upper()}_RESULT.json", result)
    return result


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} VARIANT")
    variant = sys.argv[1]
    run_id = os.environ.get("GITHUB_RUN_ID", "manual")
    out = Path(os.environ.get("OUT_ROOT", "/tmp/qym-gb77-v14")) / variant
    out.mkdir(parents=True, exist_ok=True)

    qym_raw = QYM.read_bytes()
    sidecar_raw = SIDECAR.read_bytes()
    gate = {
        "qym_sha256": sha(qym_raw),
        "qym_blob": blob(qym_raw),
        "sidecar_sha256": sha(sidecar_raw),
        "sidecar_blob": blob(sidecar_raw),
        "qym_equals_sidecar": qym_raw == sidecar_raw,
        "expected_sha256": BASE_SHA,
        "expected_blob": BASE_BLOB,
    }
    dump(out / "AUTHORITY_GATE.json", gate)
    if not (
        gate["qym_sha256"] == BASE_SHA
        and gate["qym_blob"] == BASE_BLOB
        and gate["sidecar_sha256"] == BASE_SHA
        and gate["sidecar_blob"] == BASE_BLOB
        and gate["qym_equals_sidecar"]
    ):
        raise SystemExit(f"exact GB77 authority gate failed: {gate}")

    original = out / "QYM.GB77.authority.lean"
    candidate = out / "QYM.candidate.lean"
    shutil.copy2(QYM, original)
    shutil.copy2(QYM, candidate)

    result: dict = {
        "schema": "qym-gb77-v14-right-normal-im-result-v1",
        "run_id": int(run_id) if run_id.isdigit() else run_id,
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "branch": os.environ.get("GITHUB_REF_NAME"),
        "variant": variant,
        "baseline_error_headers": BASE_ERRORS,
        "baseline_warning_headers": BASE_WARNINGS,
        "baseline_qym_sha256": BASE_SHA,
        "baseline_qym_blob": BASE_BLOB,
        "target_declaration": "conj_mul_hyperbolicRightNormal_im",
        "full_compile_executed": False,
        "strict_improvement": False,
        "semantic_pass": False,
    }

    try:
        patch_log = out / "PATCH_RESULT.json"
        with patch_log.open("wb") as handle:
            subprocess.run(
                [sys.executable, "-B", str(PATCHER), variant, str(candidate), BASE_SHA],
                check=True,
                stdout=handle,
                stderr=subprocess.STDOUT,
            )
        patch = json.loads(patch_log.read_text(encoding="utf-8"))
        result["patch"] = patch
        result["candidate_qym_sha256"] = sha(candidate.read_bytes())
        result["candidate_qym_blob"] = blob(candidate.read_bytes())
        if any(int(v) for v in patch["forbidden"].values()):
            raise SystemExit(f"forbidden proof escape in candidate: {patch['forbidden']}")

        shutil.copy2(candidate, QYM)
        local = compile_qym(out, variant, "local", 6)
        lo = int(patch["target_start_line"])
        hi = int(patch["target_end_line"])
        next_line = int(patch["next_declaration_line"])
        target_errors = [e for e in local["errors"] if lo <= int(e["line"]) <= hi]
        earlier_errors = [e for e in local["errors"] if int(e["line"]) < lo]
        first = local.get("first_error")
        advanced = first is None or int(first["line"]) >= next_line
        local_gate_pass = int(local["panic_lines"]) == 0 and not target_errors and not earlier_errors and advanced
        result.update({
            "local": local,
            "target_errors": target_errors,
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
                and int(full["error_headers"]) < BASE_ERRORS
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
