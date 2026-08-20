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
SIDECAR = Path(".github/qym-frontier/QYM_GB76_BEST.lean")
PATCHER = Path(".github/qym_patch_gb76_global_batch_round1.py")

BASE_SHA256 = "fada22264b6618467f89d436ddacff27453db1242769717d5e7a386682d4efb3"
BASE_BLOB = "29d446743036dccd5d9ad8757c351b39d526cfa9"
BASE_ERRORS = 76
BASE_WARNINGS = 358

DIAG = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)
DECL = re.compile(
    r"^\s*(?:private\s+|protected\s+)?"
    r"(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def dump(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def declaration_map(source_text: str) -> list[tuple[int, str]]:
    declarations: list[tuple[int, str]] = []
    for line_number, line in enumerate(source_text.splitlines(), start=1):
        match = DECL.match(line)
        if match:
            declarations.append((line_number, match.group("name")))
    return declarations


def enclosing_declaration(
    declarations: list[tuple[int, str]], line: int
) -> str | None:
    current: str | None = None
    for declaration_line, name in declarations:
        if declaration_line > line:
            break
        current = name
    return current


def parse_log(
    log: Path,
    returncode: int,
    elapsed: float,
    candidate_text: str,
) -> dict[str, object]:
    raw = log.read_bytes()
    text = raw.decode("utf-8", errors="replace")
    declarations = declaration_map(candidate_text)
    diagnostics: list[dict[str, object]] = []
    for match in DIAG.finditer(text):
        row: dict[str, object] = match.groupdict()
        row["line"] = int(str(row["line"]))
        row["column"] = int(str(row["column"]))
        row["enclosing_declaration"] = enclosing_declaration(
            declarations, int(row["line"])
        )
        diagnostics.append(row)

    errors = [row for row in diagnostics if row["severity"] == "error"]
    warnings = [row for row in diagnostics if row["severity"] == "warning"]
    line_buckets = collections.Counter(
        (int(row["line"]) // 1000) * 1000 for row in errors
    )
    declaration_counts = collections.Counter(
        str(row.get("enclosing_declaration") or "<unknown>")
        for row in errors
    )
    return {
        "exit": returncode,
        "elapsed_seconds": round(elapsed, 3),
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(PANIC.findall(text)),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "errors": errors,
        "error_codes": dict(
            sorted(
                collections.Counter(
                    str(row.get("code") or "uncoded") for row in errors
                ).items()
            )
        ),
        "error_line_buckets": {
            str(key): value for key, value in sorted(line_buckets.items())
        },
        "error_declarations": dict(
            sorted(
                declaration_counts.items(),
                key=lambda item: (-item[1], item[0]),
            )
        ),
        "log_sha256": sha256(raw),
        "log_bytes": len(raw),
    }


def main() -> int:
    out = Path(
        os.environ.get(
            "OUT_ROOT", "/tmp/qym-gb76-global-batch-round1"
        )
    )
    out.mkdir(parents=True, exist_ok=True)

    run_id_raw = os.environ.get("GITHUB_RUN_ID", "manual")
    run_id: int | str = (
        int(run_id_raw) if run_id_raw.isdigit() else run_id_raw
    )
    branch = os.environ.get("GITHUB_REF_NAME")
    trigger_sha = os.environ.get("GITHUB_SHA")

    qym_raw = QYM.read_bytes()
    sidecar_raw = SIDECAR.read_bytes()
    authority = {
        "qym_sha256": sha256(qym_raw),
        "qym_blob": git_blob(qym_raw),
        "sidecar_sha256": sha256(sidecar_raw),
        "sidecar_blob": git_blob(sidecar_raw),
        "qym_equals_sidecar": qym_raw == sidecar_raw,
        "expected_sha256": BASE_SHA256,
        "expected_blob": BASE_BLOB,
    }
    dump(out / "AUTHORITY_GATE.json", authority)
    if not (
        authority["qym_sha256"] == BASE_SHA256
        and authority["qym_blob"] == BASE_BLOB
        and authority["sidecar_sha256"] == BASE_SHA256
        and authority["sidecar_blob"] == BASE_BLOB
        and authority["qym_equals_sidecar"]
    ):
        raise SystemExit(f"exact GB76 authority gate failed: {authority}")

    original = out / "QYM.GB76.authority.lean"
    candidate = out / "QYM.GLOBAL_REPAIR_CANDIDATE.lean"
    patch_result_path = out / "PATCH_RESULT.json"
    full_log = out / "full.log"
    full_olean = out / "QYM.GLOBAL_REPAIR_CANDIDATE.olean"
    full_ilean = out / "QYM.GLOBAL_REPAIR_CANDIDATE.ilean"
    shutil.copy2(QYM, original)

    result: dict[str, object] = {
        "schema": "qym-gb76-global-batch-round1-result-v1",
        "authority": "actual full-QYM direct Lean",
        "run_id": run_id,
        "branch": branch,
        "trigger_sha": trigger_sha,
        "round": 1,
        "baseline_error_headers": BASE_ERRORS,
        "baseline_warning_headers": BASE_WARNINGS,
        "baseline_qym_sha256": BASE_SHA256,
        "baseline_qym_blob": BASE_BLOB,
        "full_compile_executed": False,
        "strict_improvement": False,
        "semantic_pass": False,
    }

    try:
        with patch_result_path.open("wb") as handle:
            subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(PATCHER),
                    str(original),
                    str(candidate),
                ],
                check=True,
                stdout=handle,
                stderr=subprocess.STDOUT,
            )
        patch = json.loads(
            patch_result_path.read_text(encoding="utf-8")
        )
        forbidden = {
            str(key): int(value)
            for key, value in dict(patch.get("forbidden", {})).items()
        }
        if any(forbidden.values()):
            raise SystemExit(
                f"candidate forbidden proof escape is nonzero: {forbidden}"
            )

        candidate_raw = candidate.read_bytes()
        candidate_text = candidate_raw.decode("utf-8")
        candidate_sha = sha256(candidate_raw)
        candidate_blob = git_blob(candidate_raw)
        if candidate_sha != patch.get("candidate_sha256"):
            raise SystemExit("patch result/candidate SHA256 mismatch")
        if candidate_blob != patch.get("candidate_blob"):
            raise SystemExit("patch result/candidate blob mismatch")

        result.update(
            {
                "patch": patch,
                "forbidden": forbidden,
                "candidate_qym_sha256": candidate_sha,
                "candidate_qym_blob": candidate_blob,
                "candidate_bytes": len(candidate_raw),
                "candidate_lf": candidate_raw.count(b"\n"),
            }
        )

        shutil.copy2(candidate, QYM)
        command = [
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
        ]
        started = time.monotonic()
        with full_log.open("wb") as handle:
            proc = subprocess.run(
                command,
                stdout=handle,
                stderr=subprocess.STDOUT,
            )
        full = parse_log(
            full_log,
            proc.returncode,
            time.monotonic() - started,
            candidate_text,
        )
        full.update(
            {
                "command": command,
                "olean_exists": (
                    full_olean.is_file() and full_olean.stat().st_size > 0
                ),
                "ilean_exists": (
                    full_ilean.is_file() and full_ilean.stat().st_size > 0
                ),
                "olean_bytes": (
                    full_olean.stat().st_size if full_olean.is_file() else 0
                ),
                "ilean_bytes": (
                    full_ilean.stat().st_size if full_ilean.is_file() else 0
                ),
            }
        )
        dump(out / "FULL_RESULT.json", full)

        semantic_pass = (
            int(full["exit"]) == 0
            and int(full["error_headers"]) == 0
            and int(full["panic_lines"]) == 0
            and bool(full["olean_exists"])
            and bool(full["ilean_exists"])
        )
        strict_improvement = (
            int(full["panic_lines"]) == 0
            and int(full["error_headers"]) < BASE_ERRORS
        )
        result.update(
            {
                "full_compile_executed": True,
                "full": full,
                "exit": full["exit"],
                "error_headers": full["error_headers"],
                "warning_headers": full["warning_headers"],
                "panic_lines": full["panic_lines"],
                "first_error": full["first_error"],
                "last_error": full["last_error"],
                "error_codes": full["error_codes"],
                "error_line_buckets": full["error_line_buckets"],
                "error_declarations": full["error_declarations"],
                "log_sha256": full["log_sha256"],
                "semantic_pass": semantic_pass,
                "strict_improvement": strict_improvement,
                "improvement": (
                    f"{BASE_ERRORS}->{int(full['error_headers'])}"
                ),
            }
        )
        dump(out / "RESULT.json", result)
        return 0
    finally:
        shutil.copy2(original, QYM)


if __name__ == "__main__":
    raise SystemExit(main())
