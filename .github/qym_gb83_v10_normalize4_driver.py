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

QYM = Path(os.environ.get("QYM", "PrimalitySheafVerification/QYM.lean"))
OUT = Path(os.environ.get("OUT", "/tmp/qym-gb83-v10-normalize4"))
BASE_SHA256 = "ea7c26fd104104e852a6c678017b1fb0c76abb062edd758228c4bbe506dbe8d1"
BASE_BLOB = "43aee9530d6c665fbc5e082b3a5b3ef3367f069b"
BASE_ERRORS = 83
BASE_RUN_ID = "32245256779"
BASE_JOB_ID = "96044280200"
VARIANTS = ("rw_det_coe", "rw_det_change", "congr_det_gl")
PATCHER = Path(".github/qym_patch_gb83_v10_normalize4.py")

DIAG_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_log(path: Path) -> tuple[list[dict[str, object]], list[str]]:
    raw = path.read_bytes() if path.exists() else b""
    text = raw.decode(errors="replace")
    rows: list[dict[str, object]] = []
    for match in DIAG_RE.finditer(text):
        row: dict[str, object] = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    return rows, PANIC_RE.findall(text)


def compile_candidate(candidate: Path, variant: str, phase: str, max_errors: int) -> dict[str, object]:
    shutil.copy2(candidate, QYM)
    log_path = OUT / f"{variant}.{phase}.log"
    time_path = OUT / f"{variant}.{phase}.time"
    exit_path = OUT / f"{variant}.{phase}.exit"
    olean = OUT / f"{variant}.{phase}.olean"
    ilean = OUT / f"{variant}.{phase}.ilean"
    command = [
        "/usr/bin/time", "-v", "-o", str(time_path),
        "lake", "env", "lean", f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false", "-o", str(olean), "-i", str(ilean), str(QYM),
    ]
    with log_path.open("wb") as handle:
        proc = subprocess.run(command, stdout=handle, stderr=subprocess.STDOUT)
    exit_path.write_text(str(proc.returncode) + "\n", encoding="utf-8")
    rows, panics = parse_log(log_path)
    errors = [r for r in rows if r["severity"] == "error"]
    warnings = [r for r in rows if r["severity"] == "warning"]
    return {
        "phase": phase,
        "variant": variant,
        "exit": proc.returncode,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter(str(r.get("code") or "uncoded") for r in errors).items())),
        "log_sha256": sha256(log_path.read_bytes()),
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
        base = canonical.read_bytes()
        baseline_check = {
            "source_sha256": sha256(base),
            "source_blob": git_blob(base),
            "expected_sha256": BASE_SHA256,
            "expected_blob": BASE_BLOB,
            "errors": BASE_ERRORS,
            "run_id": BASE_RUN_ID,
            "job_id": BASE_JOB_ID,
            "sha_ok": sha256(base) == BASE_SHA256,
            "blob_ok": git_blob(base) == BASE_BLOB,
        }
        write_json(OUT / "BASELINE_CHECK.json", baseline_check)
        if not baseline_check["sha_ok"] or not baseline_check["blob_ok"]:
            raise RuntimeError(f"GB83 checked-in baseline mismatch: {baseline_check}")

        candidates: list[dict[str, object]] = []
        for variant in VARIANTS:
            candidate = OUT / f"QYM.candidate-{variant}.lean"
            shutil.copy2(canonical, candidate)
            patch_path = OUT / f"{variant}.PATCH_RESULT.json"
            with patch_path.open("wb") as handle:
                subprocess.run(
                    [sys.executable, "-B", str(PATCHER), variant, str(candidate)],
                    check=True, stdout=handle,
                )
            patch = json.loads(patch_path.read_text(encoding="utf-8"))
            raw = candidate.read_bytes()
            if patch.get("input_sha256") != BASE_SHA256 or patch.get("input_blob") != BASE_BLOB:
                raise RuntimeError(f"{variant}: input authority mismatch")
            if patch.get("candidate_sha256") != sha256(raw) or patch.get("candidate_blob") != git_blob(raw):
                raise RuntimeError(f"{variant}: output digest mismatch")
            if any(int(v) != 0 for v in (patch.get("forbidden") or {}).values()):
                raise RuntimeError(f"{variant}: forbidden-token audit failed")
            local = compile_candidate(candidate, variant, "local", 1)
            first = local.get("first_error") or {}
            first_line = int(first.get("line") or 10**9)
            gate_line = int(patch["gate_line"])
            gate_pass = int(local["panic_lines"]) == 0 and first_line >= gate_line
            local["gate_line"] = gate_line
            local["normalize4_fixed"] = gate_pass
            write_json(OUT / f"{variant}.LOCAL_RESULT.json", local)
            row = {"variant": variant, "candidate": str(candidate), "patch": patch,
                   "local": local, "local_gate_pass": gate_pass}
            candidates.append(row)

        strict_rows: list[dict[str, object]] = []
        candidates.sort(key=lambda r: (
            0 if r["local_gate_pass"] else 1,
            -int((r["local"].get("first_error") or {}).get("line") or 10**9),
            str(r["variant"]),
        ))
        for row in candidates:
            if not row["local_gate_pass"]:
                continue
            variant = str(row["variant"])
            full = compile_candidate(Path(str(row["candidate"])), variant, "full", 10000)
            semantic_pass = (
                int(full["exit"]) == 0 and int(full["error_headers"]) == 0 and
                int(full["panic_lines"]) == 0 and bool(full["olean_exists"]) and bool(full["ilean_exists"])
            )
            strict = semantic_pass or (
                int(full["panic_lines"]) == 0 and int(full["error_headers"]) < BASE_ERRORS
            )
            full.update({
                "semantic_pass": semantic_pass,
                "strict_improvement": strict,
                "baseline_error_headers": BASE_ERRORS,
                "baseline_qym_sha256": BASE_SHA256,
                "baseline_qym_blob": BASE_BLOB,
                "candidate_qym_sha256": row["patch"]["candidate_sha256"],
                "candidate_qym_blob": row["patch"]["candidate_blob"],
                "run_id": os.environ.get("GITHUB_RUN_ID"),
                "trigger_sha": os.environ.get("GITHUB_SHA"),
            })
            row["full"] = full
            write_json(OUT / f"{variant}.FULL_RESULT.json", full)
            if strict:
                strict_rows.append(row)
                break

        selection: dict[str, object] = {
            "schema": "qym-gb83-v10-normalize4-selection-v1",
            "baseline": {
                "run_id": int(BASE_RUN_ID), "job_id": int(BASE_JOB_ID),
                "error_headers": BASE_ERRORS, "qym_sha256": BASE_SHA256, "qym_blob": BASE_BLOB,
            },
            "candidates": candidates,
            "strict_improvement_found": bool(strict_rows),
        }
        if strict_rows:
            best = min(strict_rows, key=lambda r: (
                0 if r["full"]["semantic_pass"] else 1,
                int(r["full"]["error_headers"]), int(r["full"]["panic_lines"]),
                -int((r["full"].get("first_error") or {}).get("line") or 10**9),
            ))
            selection["best_variant"] = best["variant"]
            selection["best"] = best["full"]
            shutil.copy2(Path(str(best["candidate"])), OUT / "QYM.best.lean")
            write_json(OUT / "BEST_RESULT.json", best["full"])
            write_json(OUT / "SELECTION.json", selection)
            print(json.dumps(selection, indent=2, sort_keys=True))
            return 0
        write_json(OUT / "SELECTION.json", selection)
        print(json.dumps(selection, indent=2, sort_keys=True))
        return 2
    except Exception as exc:
        (OUT / "FATAL.txt").write_text(f"{type(exc).__name__}: {exc}\n", encoding="utf-8")
        raise
    finally:
        if canonical.exists():
            shutil.copy2(canonical, QYM)


if __name__ == "__main__":
    raise SystemExit(main())
