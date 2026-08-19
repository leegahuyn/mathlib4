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
OUT = Path(os.environ.get("OUT", "/tmp/qym-gb78-v12"))
ARTIFACT_ID = os.environ.get("BASELINE_ARTIFACT", "9371708709")
BASE_SOURCE_NAME = "QYM.best.lean"
BASE_RESULT_NAME = "BEST_RESULT.json"
BASE_SHA256 = "1a45a5cad7243eab3ad276f6add587a3a890819ecee30ef689d2295364db41b4"
BASE_BLOB = "1d9a5b94f7f7a02a996fbeced521c915194d751d"
BASE_ERRORS = 78
BASE_RUN_ID = "32266408007"
VARIANTS = ("direct_hstar", "structural_hstar", "structural_rw_hstar")
PATCHER = Path(".github/qym_gb78_v12_normal_patch.py")

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


def recover_baseline() -> Path:
    OUT.mkdir(parents=True, exist_ok=True)
    archive = OUT / "gb78-authority.zip"
    with archive.open("wb") as handle:
        subprocess.run([
            "gh", "api", "-H", "Accept: application/vnd.github+json",
            f"repos/{REPO}/actions/artifacts/{ARTIFACT_ID}/zip",
        ], check=True, stdout=handle)
    base_dir = OUT / "authority"
    if base_dir.exists():
        shutil.rmtree(base_dir)
    base_dir.mkdir()
    with zipfile.ZipFile(archive) as zf:
        zf.extractall(base_dir)
    sources = list(base_dir.rglob(BASE_SOURCE_NAME))
    results = list(base_dir.rglob(BASE_RESULT_NAME))
    if len(sources) != 1 or len(results) != 1:
        raise RuntimeError(f"authority members mismatch: sources={len(sources)} results={len(results)}")
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
        "phase": result.get("phase") == "full",
    }
    write_json(OUT / "BASELINE_CHECK.json", {"checks": checks, "result": result})
    if not all(checks.values()):
        raise RuntimeError(f"GB78 authority verification failed: {checks}")
    frozen = OUT / "QYM.GB78.lean"
    shutil.copy2(source, frozen)
    return frozen


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
    log = OUT / f"{variant}.{phase}.log"
    time_file = OUT / f"{variant}.{phase}.time"
    olean = OUT / f"{variant}.{phase}.olean"
    ilean = OUT / f"{variant}.{phase}.ilean"
    cmd = [
        "/usr/bin/time", "-v", "-o", str(time_file),
        "lake", "env", "lean", f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false", "-o", str(olean), "-i", str(ilean), str(QYM),
    ]
    with log.open("wb") as handle:
        proc = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT)
    rows, panics = parse_log(log)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    result: dict[str, object] = {
        "variant": variant,
        "phase": phase,
        "exit": proc.returncode,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter(str(row.get("code") or "uncoded") for row in errors).items())),
        "log_sha256": sha256(log.read_bytes()),
        "candidate_qym_sha256": sha256(candidate.read_bytes()),
        "candidate_qym_blob": git_blob(candidate.read_bytes()),
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
    }
    write_json(OUT / f"{variant}.{phase}.json", result)
    return result


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    checked_in = OUT / "QYM.checked-in.lean"
    shutil.copy2(QYM, checked_in)
    try:
        baseline = recover_baseline()
        candidates: list[dict[str, object]] = []
        for variant in VARIANTS:
            candidate = OUT / f"QYM.candidate-{variant}.lean"
            shutil.copy2(baseline, candidate)
            patch_file = OUT / f"{variant}.PATCH_RESULT.json"
            with patch_file.open("wb") as handle:
                subprocess.run([sys.executable, "-B", str(PATCHER), variant, str(candidate)], check=True, stdout=handle)
            patch = json.loads(patch_file.read_text(encoding="utf-8"))
            raw = candidate.read_bytes()
            if patch.get("candidate_sha256") != sha256(raw) or patch.get("candidate_blob") != git_blob(raw):
                raise RuntimeError(f"{variant}: patch identity mismatch")
            if any(int(v) != 0 for v in (patch.get("forbidden") or {}).values()):
                raise RuntimeError(f"{variant}: forbidden audit failure")
            local = compile_candidate(candidate, variant, "local", 1)
            first = local.get("first_error") or {}
            first_line = int(first.get("line") or 10**9)
            gate_line = int(patch["gate_line"])
            local_pass = int(local.get("panic_lines", 1)) == 0 and first_line >= gate_line
            local["gate_line"] = gate_line
            local["normal_cluster_fixed"] = local_pass
            write_json(OUT / f"{variant}.LOCAL_RESULT.json", local)
            candidates.append({
                "variant": variant,
                "candidate": str(candidate),
                "patch": patch,
                "local": local,
                "local_pass": local_pass,
            })

        viable = [row for row in candidates if row["local_pass"]]
        viable.sort(key=lambda row: -int(((row["local"].get("first_error") or {}).get("line") or 0)))
        improved: list[dict[str, object]] = []
        for row in viable:
            variant = str(row["variant"])
            full = compile_candidate(Path(str(row["candidate"])), variant, "full", 10000)
            semantic = (
                int(full["exit"]) == 0 and int(full["error_headers"]) == 0
                and int(full["panic_lines"]) == 0 and bool(full["olean_exists"])
                and bool(full["ilean_exists"])
            )
            strict = semantic or (
                int(full["panic_lines"]) == 0 and int(full["error_headers"]) < BASE_ERRORS
            )
            full.update({
                "baseline_error_headers": BASE_ERRORS,
                "baseline_qym_sha256": BASE_SHA256,
                "baseline_qym_blob": BASE_BLOB,
                "semantic_pass": semantic,
                "strict_improvement": strict,
                "run_id": os.environ.get("GITHUB_RUN_ID"),
                "trigger_sha": os.environ.get("GITHUB_SHA"),
            })
            row["full"] = full
            write_json(OUT / f"{variant}.FULL_RESULT.json", full)
            if strict:
                improved.append(row)
                break

        selection: dict[str, object] = {
            "schema": "qym-gb78-v12-normal-selection-v1",
            "baseline": {
                "artifact_id": int(ARTIFACT_ID),
                "run_id": int(BASE_RUN_ID),
                "error_headers": BASE_ERRORS,
                "qym_sha256": BASE_SHA256,
                "qym_blob": BASE_BLOB,
            },
            "candidates": candidates,
            "strict_improvement_found": bool(improved),
        }
        if improved:
            best = improved[0]
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
    finally:
        if checked_in.exists():
            shutil.copy2(checked_in, QYM)


if __name__ == "__main__":
    raise SystemExit(main())
