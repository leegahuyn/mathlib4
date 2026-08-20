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
GB77 = Path(".github/qym-frontier/QYM_GB77_BEST.lean")
RIGHT_PATCHER = Path(".github/qym_patch_gb77_v15.py")
GROUPOID_PATCHER = Path(".github/qym_patch_gb77_fixedorigin_v16_groupoid.py")
INVERSE_PATCHER = Path(".github/qym_patch_gb77_fixedorigin_v17_inverse_eta.py")
FIXED_SHA = "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd"
FIXED_BLOB = "c6e8883353b350f22b7f48d955fc5cfa4e61f88f"
PARENT_SHA = "fada22264b6618467f89d436ddacff27453db1242769717d5e7a386682d4efb3"
PARENT_BLOB = "29d446743036dccd5d9ad8757c351b39d526cfa9"
GROUPOID_VARIANTS = {"explicit_helpers", "fact_bridge", "inline_duplicate"}
INVERSE_VARIANTS = {
    "explicit_simpa", "explicit_cases",
    "opaque_instance_simpa", "opaque_instance_cases",
}
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


def run_json(cmd: list[str], path: Path) -> dict:
    with path.open("wb") as handle:
        subprocess.run(cmd, check=True, stdout=handle, stderr=subprocess.STDOUT)
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> int:
    if len(sys.argv) != 2 or "__" not in sys.argv[1]:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} GROUPOID__INVERSE")
    combined = sys.argv[1]
    groupoid_variant, inverse_variant = combined.split("__", 1)
    if groupoid_variant not in GROUPOID_VARIANTS or inverse_variant not in INVERSE_VARIANTS:
        raise SystemExit(f"unknown combined variant: {combined}")

    out = Path(os.environ.get("OUT_ROOT", "/tmp/qym-gb77-fixedorigin-v17")) / combined
    out.mkdir(parents=True, exist_ok=True)
    fixed = GB77.read_bytes()
    canonical_before = QYM.read_bytes()
    gate = {
        "fixed_origin_path": str(GB77),
        "fixed_origin_sha256": sha(fixed),
        "fixed_origin_blob": blob(fixed),
        "expected_fixed_sha256": FIXED_SHA,
        "expected_fixed_blob": FIXED_BLOB,
        "canonical_before_sha256": sha(canonical_before),
        "canonical_before_blob": blob(canonical_before),
    }
    dump(out / "AUTHORITY_GATE.json", gate)
    if gate["fixed_origin_sha256"] != FIXED_SHA or gate["fixed_origin_blob"] != FIXED_BLOB:
        raise SystemExit(f"exact GB77 fixed-origin gate failed: {gate}")

    original = out / "QYM.canonical.before.lean"
    parent = out / "QYM.GB77_plus_rightnormal.lean"
    groupoid = out / "QYM.groupoid.lean"
    candidate = out / "QYM.candidate.lean"
    shutil.copy2(QYM, original)
    shutil.copy2(GB77, parent)
    run_value = os.environ.get("GITHUB_RUN_ID", "manual")
    result: dict = {
        "schema": "qym-gb77-fixedorigin-v17-inverse-eta-result-v1",
        "run_id": int(run_value) if run_value.isdigit() else run_value,
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "branch": os.environ.get("GITHUB_REF_NAME"),
        "variant": combined,
        "groupoid_variant": groupoid_variant,
        "inverse_eta_variant": inverse_variant,
        "baseline_error_headers": 77,
        "baseline_warning_headers": 360,
        "baseline_qym_sha256": FIXED_SHA,
        "baseline_qym_blob": FIXED_BLOB,
        "verified_rightnormal_parent_errors": 76,
        "verified_rightnormal_parent_sha256": PARENT_SHA,
        "verified_rightnormal_parent_blob": PARENT_BLOB,
        "full_compile_executed": False,
        "strict_improvement": False,
        "semantic_pass": False,
    }

    try:
        right_patch = run_json(
            [sys.executable, "-B", str(RIGHT_PATCHER),
             "normsq_simp_then_rw", str(parent), FIXED_SHA],
            out / "RIGHT_NORMAL_PATCH_RESULT.json",
        )
        parent_raw = parent.read_bytes()
        if sha(parent_raw) != PARENT_SHA or blob(parent_raw) != PARENT_BLOB:
            raise SystemExit(
                f"verified 76-parent reconstruction mismatch sha={sha(parent_raw)} blob={blob(parent_raw)}"
            )

        groupoid_patch = run_json(
            [sys.executable, "-B", str(GROUPOID_PATCHER),
             groupoid_variant, str(parent), str(groupoid)],
            out / "GROUPOID_PATCH_RESULT.json",
        )
        inverse_patch = run_json(
            [sys.executable, "-B", str(INVERSE_PATCHER),
             inverse_variant, str(groupoid), str(candidate)],
            out / "INVERSE_ETA_PATCH_RESULT.json",
        )
        candidate_raw = candidate.read_bytes()
        forbidden = inverse_patch.get("forbidden") or {}
        if any(int(value) for value in forbidden.values()):
            raise SystemExit(f"forbidden proof escape in candidate: {forbidden}")
        result.update({
            "right_normal_patch": right_patch,
            "groupoid_patch": groupoid_patch,
            "inverse_eta_patch": inverse_patch,
            "patch": inverse_patch,
            "candidate_qym_sha256": sha(candidate_raw),
            "candidate_qym_blob": blob(candidate_raw),
            "forbidden": forbidden,
        })

        shutil.copy2(candidate, QYM)
        local = compile_qym(out, combined, "local", 32)
        lo = int(groupoid_patch["section_start_line"])
        hi = int(inverse_patch["section_end_line"])
        target_errors = [row for row in local["errors"] if lo <= int(row["line"]) <= hi]
        earlier_errors = [row for row in local["errors"] if int(row["line"]) < lo]
        first = local.get("first_error")
        advanced = first is None or int(first["line"]) > hi
        local_gate_pass = int(local["panic_lines"]) == 0 and not target_errors and not earlier_errors and advanced
        result.update({
            "local": local,
            "target_errors": target_errors,
            "earlier_errors": earlier_errors,
            "local_gate_start_line": lo,
            "local_gate_end_line": hi,
            "local_gate_pass": local_gate_pass,
            "first_blocker_advanced_beyond_inverse_eta": advanced,
        })

        if local_gate_pass:
            full = compile_qym(out, combined, "full", 10000)
            semantic = (
                int(full["exit"]) == 0
                and int(full["error_headers"]) == 0
                and int(full["panic_lines"]) == 0
                and bool(full["olean_exists"])
                and bool(full["ilean_exists"])
            )
            strict = semantic or (int(full["panic_lines"]) == 0 and int(full["error_headers"]) < 76)
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
