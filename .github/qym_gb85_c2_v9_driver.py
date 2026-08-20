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
VARIANTS = ("hfun_cast", "hfun_rw", "hfun_convert")
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
    return hashlib.sha1(
        b"blob " + str(len(data)).encode() + b"\0" + data
    ).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def run_checked(command: list[str], *, stdout=None) -> None:
    subprocess.run(command, check=True, stdout=stdout)


def recover_baseline() -> Path:
    OUT.mkdir(parents=True, exist_ok=True)
    authority = OUT / "authority"
    if authority.exists():
        shutil.rmtree(authority)
    authority.mkdir(parents=True)
    archive = OUT / "gb85-authority.zip"
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
    with zipfile.ZipFile(archive) as zipped:
        zipped.extractall(authority)

    sources = list(authority.rglob(BASE_SOURCE_NAME))
    results = list(authority.rglob("RESULT.json"))
    if len(sources) != 1 or len(results) != 1:
        raise RuntimeError(
            "expected one GB85 source/result; "
            f"got sources={len(sources)} results={len(results)}"
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
    write_json(
        OUT / "BASELINE_CHECK.json",
        {"checks": checks, "result": result},
    )
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
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    return rows, PANIC_RE.findall(text)


def compile_candidate(
    candidate: Path,
    variant: str,
    phase: str,
    max_errors: int,
) -> dict[str, object]:
    shutil.copy2(candidate, QYM)
    log_path = OUT / f"{variant}.{phase}.log"
    time_path = OUT / f"{variant}.{phase}.time"
    exit_path = OUT / f"{variant}.{phase}.exit"
    olean = OUT / f"{variant}.{phase}.olean"
    ilean = OUT / f"{variant}.{phase}.ilean"

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
        process = subprocess.run(
            command,
            stdout=handle,
            stderr=subprocess.STDOUT,
        )
    exit_path.write_text(str(process.returncode) + "\n", encoding="utf-8")

    rows, panics = parse_log(log_path)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    raw_log = log_path.read_bytes()
    return {
        "phase": phase,
        "variant": variant,
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


def materialize_candidates(baseline: Path) -> list[dict[str, object]]:
    candidates: list[dict[str, object]] = []
    for variant in VARIANTS:
        candidate = OUT / f"QYM.candidate-{variant}.lean"
        shutil.copy2(baseline, candidate)
        patch_file = OUT / f"{variant}.PATCH_RESULT.json"
        with patch_file.open("wb") as handle:
            run_checked(
                [
                    sys.executable,
                    "-B",
                    str(PATCHER),
                    variant,
                    str(candidate),
                ],
                stdout=handle,
            )
        patch = json.loads(patch_file.read_text(encoding="utf-8"))
        raw = candidate.read_bytes()
        if patch.get("input_sha256") != BASE_SHA256:
            raise RuntimeError(f"{variant}: patch input SHA mismatch")
        if patch.get("input_blob") != BASE_BLOB:
            raise RuntimeError(f"{variant}: patch input blob mismatch")
        if patch.get("candidate_sha256") != sha256(raw):
            raise RuntimeError(f"{variant}: patch output SHA mismatch")
        if patch.get("candidate_blob") != git_blob(raw):
            raise RuntimeError(f"{variant}: patch output blob mismatch")
        if any(int(value) != 0 for value in (patch.get("forbidden") or {}).values()):
            raise RuntimeError(f"{variant}: forbidden-token audit failed")
        candidates.append(
            {
                "variant": variant,
                "candidate": str(candidate),
                "patch": patch,
            }
        )
    return candidates


def local_rank(row: dict[str, object]) -> tuple[int, int, str]:
    local = row["local"]
    first = local.get("first_error") or {}
    line = int(first.get("line") or 10**9)
    return (
        0 if row.get("local_gate_pass") else 1,
        -line,
        str(row["variant"]),
    )


def full_rank(row: dict[str, object]) -> tuple[int, int, int, int, str]:
    full = row["full"]
    first = full.get("first_error") or {}
    line = int(first.get("line") or 10**9)
    return (
        0 if full.get("semantic_pass") else 1,
        int(full.get("error_headers", 10**9)),
        int(full.get("panic_lines", 10**9)),
        -line,
        str(row["variant"]),
    )


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    canonical = OUT / "QYM.checked-in.lean"
    shutil.copy2(QYM, canonical)
    try:
        baseline = recover_baseline()
        candidates = materialize_candidates(baseline)

        for row in candidates:
            variant = str(row["variant"])
            local = compile_candidate(
                Path(str(row["candidate"])),
                variant,
                "local",
                1,
            )
            gate_line = int(row["patch"]["gate_line"])
            first = local.get("first_error") or {}
            first_line = int(first.get("line") or 10**9)
            gate_pass = (
                int(local.get("panic_lines", 1)) == 0
                and first_line >= gate_line
            )
            local["gate_line"] = gate_line
            local["c2_fixed"] = gate_pass
            row["local"] = local
            row["local_gate_pass"] = gate_pass
            write_json(OUT / f"{variant}.LOCAL_RESULT.json", local)

        strict_rows: list[dict[str, object]] = []
        for row in sorted(candidates, key=local_rank):
            if not row.get("local_gate_pass"):
                continue
            variant = str(row["variant"])
            full = compile_candidate(
                Path(str(row["candidate"])),
                variant,
                "full",
                10000,
            )
            semantic_pass = (
                int(full["exit"]) == 0
                and int(full["error_headers"]) == 0
                and int(full["panic_lines"]) == 0
                and bool(full["olean_exists"])
                and bool(full["ilean_exists"])
            )
            strict = semantic_pass or (
                int(full["panic_lines"]) == 0
                and int(full["error_headers"]) < BASE_ERRORS
            )
            full["semantic_pass"] = semantic_pass
            full["strict_improvement"] = strict
            full["baseline_error_headers"] = BASE_ERRORS
            full["candidate_qym_sha256"] = row["patch"]["candidate_sha256"]
            full["candidate_qym_blob"] = row["patch"]["candidate_blob"]
            full["run_id"] = os.environ.get("GITHUB_RUN_ID")
            full["trigger_sha"] = os.environ.get("GITHUB_SHA")
            row["full"] = full
            write_json(OUT / f"{variant}.FULL_RESULT.json", full)
            if strict:
                strict_rows.append(row)
                break

        selection: dict[str, object] = {
            "schema": "qym-gb85-c2-v9-selection-v1",
            "baseline": {
                "artifact_id": int(ARTIFACT_ID),
                "run_id": int(BASE_RUN_ID),
                "error_headers": BASE_ERRORS,
                "qym_sha256": BASE_SHA256,
                "qym_blob": BASE_BLOB,
            },
            "candidates": candidates,
            "strict_improvement_found": bool(strict_rows),
        }
        if strict_rows:
            best = sorted(strict_rows, key=full_rank)[0]
            selection["best_variant"] = best["variant"]
            selection["best"] = best["full"]
            shutil.copy2(
                Path(str(best["candidate"])),
                OUT / "QYM.best.lean",
            )
            write_json(OUT / "BEST_RESULT.json", best["full"])
            write_json(OUT / "SELECTION.json", selection)
            print(json.dumps(selection, indent=2, sort_keys=True))
            return 0

        write_json(OUT / "SELECTION.json", selection)
        print(json.dumps(selection, indent=2, sort_keys=True))
        return 2
    except Exception as error:
        (OUT / "FATAL.txt").write_text(
            f"{type(error).__name__}: {error}\n",
            encoding="utf-8",
        )
        raise
    finally:
        if canonical.exists():
            shutil.copy2(canonical, QYM)


if __name__ == "__main__":
    raise SystemExit(main())
