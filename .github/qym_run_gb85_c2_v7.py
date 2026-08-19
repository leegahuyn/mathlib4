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
from typing import Any

BASELINE_SHA256 = "f4c9b27a297be772bf863001175d540fd024e22ce0bec06af75f47ef48c23bba1"
BASELINE_BLOB = "bd28d043181c53d405eed7659d7018fa2298a33d"
BASELINE_ERRORS = 85
VARIANTS = ("cases_explicit", "cases_change", "intrinsic_detpos")
DIAGNOSTIC_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_diagnostics(raw: bytes) -> tuple[list[dict[str, Any]], list[str]]:
    text = raw.decode(errors="replace")
    rows: list[dict[str, Any]] = []
    for match in DIAGNOSTIC_RE.finditer(text):
        row = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    panics = PANIC_RE.findall(text)
    return rows, panics


def run_command(
    command: list[str],
    log_path: Path,
    *,
    timeout: int,
    cwd: Path,
) -> tuple[int, float]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        raw = completed.stdout or b""
        rc = int(completed.returncode)
    except subprocess.TimeoutExpired as exc:
        raw = (exc.stdout or b"") + b"\nDRIVER_TIMEOUT\n"
        rc = 124
    elapsed = time.monotonic() - started
    log_path.write_bytes(raw)
    return rc, elapsed


def summarize(
    *,
    raw: bytes,
    rc: int,
    patch: dict[str, Any],
    variant: str,
    phase: str,
    elapsed_seconds: float,
) -> dict[str, Any]:
    rows, panics = parse_diagnostics(raw)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    semantic_pass = rc == 0 and not errors and not panics
    result = {
        "schema": "qym-gb85-c2-v7-result",
        "phase": phase,
        "variant": variant,
        "baseline_qym_sha256": BASELINE_SHA256,
        "baseline_qym_blob": BASELINE_BLOB,
        "baseline_error_headers": BASELINE_ERRORS,
        "candidate_qym_sha256": patch["candidate_sha256"],
        "candidate_qym_blob": patch["candidate_blob"],
        "bytes": patch["bytes"],
        "lf": patch["lf"],
        "gate_line": patch["gate_line"],
        "forbidden": patch["forbidden"],
        "exit": rc,
        "elapsed_seconds": elapsed_seconds,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter(
            row["code"] or "uncoded" for row in errors
        ).items())),
        "log_sha256": hashlib.sha256(raw).hexdigest(),
        "semantic_pass": semantic_pass,
    }
    result["strict_improvement"] = semantic_pass or (
        not panics and len(errors) < BASELINE_ERRORS
    )
    return result


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit(
            "usage: qym_run_gb85_c2_v7.py REPO_ROOT BASE_SOURCE QYM OUT_DIR"
        )

    repo = Path(sys.argv[1]).resolve()
    baseline = Path(sys.argv[2]).resolve()
    qym = Path(sys.argv[3]).resolve()
    out = Path(sys.argv[4]).resolve()
    out.mkdir(parents=True, exist_ok=True)

    baseline_raw = baseline.read_bytes()
    if hashlib.sha256(baseline_raw).hexdigest() != BASELINE_SHA256:
        raise SystemExit("driver baseline SHA256 mismatch")
    if git_blob(baseline_raw) != BASELINE_BLOB:
        raise SystemExit("driver baseline Git blob mismatch")

    canonical_raw = qym.read_bytes()
    runner_temp = Path(os.environ.get("RUNNER_TEMP", "/tmp"))
    all_results: list[dict[str, Any]] = []
    full_results: list[dict[str, Any]] = []

    try:
        for variant in VARIANTS:
            variant_dir = out / variant
            variant_dir.mkdir(parents=True, exist_ok=True)
            qym.write_bytes(baseline_raw)

            patch_log = variant_dir / "patch.stdout"
            patch_cmd = [
                sys.executable,
                "-B",
                str(repo / ".github/qym_patch_gb85_c2_cases_v7.py"),
                variant,
                str(qym),
            ]
            patch_rc, patch_elapsed = run_command(
                patch_cmd, patch_log, timeout=120, cwd=repo
            )
            (variant_dir / "patch.exit").write_text(f"{patch_rc}\n")
            if patch_rc != 0:
                all_results.append({
                    "variant": variant,
                    "phase": "patch",
                    "exit": patch_rc,
                    "elapsed_seconds": patch_elapsed,
                    "strict_improvement": False,
                    "failure": patch_log.read_text(errors="replace")[-4000:],
                })
                continue

            try:
                patch = json.loads(patch_log.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                all_results.append({
                    "variant": variant,
                    "phase": "patch-json",
                    "exit": 1,
                    "strict_improvement": False,
                    "failure": str(exc),
                })
                continue

            candidate_raw = qym.read_bytes()
            if hashlib.sha256(candidate_raw).hexdigest() != patch["candidate_sha256"]:
                raise SystemExit(f"{variant}: candidate SHA256 mismatch")
            if git_blob(candidate_raw) != patch["candidate_blob"]:
                raise SystemExit(f"{variant}: candidate Git blob mismatch")
            candidate_path = variant_dir / f"QYM.candidate-{variant}.lean"
            candidate_path.write_bytes(candidate_raw)
            write_json(variant_dir / "PATCH_RESULT.json", patch)

            local_log = variant_dir / "local.log"
            local_olean = runner_temp / f"QYM-gb85-c2-v7-{variant}-local.olean"
            local_ilean = runner_temp / f"QYM-gb85-c2-v7-{variant}-local.ilean"
            local_cmd = [
                "lake", "env", "lean",
                "-DmaxErrors=1",
                "-DwarningAsError=false",
                "-o", str(local_olean),
                "-i", str(local_ilean),
                str(qym.relative_to(repo)),
            ]
            local_rc, local_elapsed = run_command(
                local_cmd, local_log, timeout=1800, cwd=repo
            )
            (variant_dir / "local.exit").write_text(f"{local_rc}\n")
            local_raw = local_log.read_bytes()
            local_result = summarize(
                raw=local_raw,
                rc=local_rc,
                patch=patch,
                variant=variant,
                phase="local",
                elapsed_seconds=local_elapsed,
            )
            first = local_result["first_error"]
            local_result["producer_fixed"] = (
                local_result["panic_lines"] == 0
                and (first is None or int(first["line"]) >= int(patch["gate_line"]))
            )
            write_json(variant_dir / "LOCAL_RESULT.json", local_result)
            all_results.append(local_result)
            if not local_result["producer_fixed"]:
                continue

            full_log = variant_dir / "full.log"
            full_olean = variant_dir / "QYM.olean"
            full_ilean = variant_dir / "QYM.ilean"
            full_cmd = [
                "/usr/bin/time", "-v", "-o", str(variant_dir / "full.time"),
                "lake", "env", "lean",
                "-DmaxErrors=10000",
                "-DwarningAsError=false",
                "-o", str(full_olean),
                "-i", str(full_ilean),
                str(qym.relative_to(repo)),
            ]
            full_rc, full_elapsed = run_command(
                full_cmd, full_log, timeout=7200, cwd=repo
            )
            (variant_dir / "full.exit").write_text(f"{full_rc}\n")
            full_raw = full_log.read_bytes()
            full_result = summarize(
                raw=full_raw,
                rc=full_rc,
                patch=patch,
                variant=variant,
                phase="full",
                elapsed_seconds=full_elapsed,
            )
            if full_result["semantic_pass"]:
                if not full_olean.is_file() or full_olean.stat().st_size == 0:
                    raise SystemExit(f"{variant}: PASS without QYM.olean")
                if not full_ilean.is_file() or full_ilean.stat().st_size == 0:
                    raise SystemExit(f"{variant}: PASS without QYM.ilean")
                full_result["olean_sha256"] = hashlib.sha256(
                    full_olean.read_bytes()
                ).hexdigest()
                full_result["ilean_sha256"] = hashlib.sha256(
                    full_ilean.read_bytes()
                ).hexdigest()
            write_json(variant_dir / "FULL_RESULT.json", full_result)
            rows, panics = parse_diagnostics(full_raw)
            errors = [row for row in rows if row["severity"] == "error"]
            (variant_dir / "error-headers.txt").write_text(
                "".join(
                    f"{row['file']}:{row['line']}:{row['column']}: error"
                    f"{('(' + row['code'] + ')') if row['code'] else ''}: "
                    f"{row['message']}\n"
                    for row in errors
                ),
                encoding="utf-8",
            )
            (variant_dir / "panic-lines.txt").write_text(
                "".join(line + "\n" for line in panics), encoding="utf-8"
            )
            full_results.append(full_result)
            all_results.append(full_result)

        def rank(result: dict[str, Any]) -> tuple[Any, ...]:
            first_line = int((result.get("first_error") or {}).get("line") or 10**9)
            return (
                0 if result.get("semantic_pass") else 1,
                int(result.get("error_headers", 10**9)),
                int(result.get("panic_lines", 10**9)),
                -first_line,
                int(result.get("warning_headers", 10**9)),
                str(result.get("variant", "")),
            )

        full_results.sort(key=rank)
        best = full_results[0] if full_results else None
        selection = {
            "schema": "qym-gb85-c2-v7-selection",
            "github_run_id": os.environ.get("GITHUB_RUN_ID"),
            "github_sha": os.environ.get("GITHUB_SHA"),
            "baseline": {
                "sha256": BASELINE_SHA256,
                "blob": BASELINE_BLOB,
                "error_headers": BASELINE_ERRORS,
            },
            "best": best,
            "all": all_results,
            "strict_improvement": bool(best and best.get("strict_improvement")),
        }
        write_json(out / "SELECTION.json", selection)

        if not best or not best.get("strict_improvement"):
            raise SystemExit("no verified strict improvement from the 85-error baseline")

        best_variant = str(best["variant"])
        best_dir = out / best_variant
        best_source = best_dir / f"QYM.candidate-{best_variant}.lean"
        shutil.copy2(best_source, out / "QYM.best.lean")
        shutil.copy2(best_dir / "FULL_RESULT.json", out / "BEST_RESULT.json")
        shutil.copy2(best_dir / "error-headers.txt", out / "BEST_error-headers.txt")
        shutil.copy2(best_dir / "panic-lines.txt", out / "BEST_panic-lines.txt")
        if (best_dir / "QYM.olean").is_file():
            shutil.copy2(best_dir / "QYM.olean", out / "QYM.best.olean")
        if (best_dir / "QYM.ilean").is_file():
            shutil.copy2(best_dir / "QYM.ilean", out / "QYM.best.ilean")
        print(json.dumps(selection, indent=2, sort_keys=True))
    finally:
        qym.write_bytes(canonical_raw)


if __name__ == "__main__":
    main()
