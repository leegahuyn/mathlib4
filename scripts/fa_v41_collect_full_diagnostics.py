#!/usr/bin/env python3
"""Collect complete, declaration-indexed FA v41 diagnostics.

The collector is evidence-only: it does not invoke Lean, Lake, git, GitHub, or
the network.  It accepts both traditional ``error:`` headers and Lean headers
with an optional diagnostic code such as ``error(lean.someCode):``.  Missing
compile outputs are represented explicitly so an ``always()`` workflow step
can still produce uploadable METRIC/FULL_DIAGNOSTICS evidence.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
from bisect import bisect_right
from pathlib import Path
from typing import Any


SCHEMA = "fa-v41-cumulative-highcap2000-metric-v1"
AUTHORITY = {
    "run_id": "31691415963",
    "job_id": "94419363592",
    "head_sha": "52a036e260592b839ad3f7e49e4cf1c60c00cbc2",
    "artifact_id": "9178173556",
    "artifact_digest": (
        "sha256:b75144f04e6579b291b0402c3f38406e4d34308af71e1861da85fcbd582f82f5"
    ),
    "source_sha256": (
        "c88cd9832ea095ab22b0f1dd9307c8f43587d85b10688d47c4a534529cebca5c"
    ),
    "diagnostics_sha256": (
        "fe09d7ad50bfebb6fbc13e03e2bb58cfde0f7116e4ed624f97a7204c2de38efc"
    ),
}
STEMS = ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)"
)
DIAGNOSTIC_RE = re.compile(
    r"^(?P<file>.+?\.lean):(?P<line>\d+):(?P<column>\d+):\s+"
    r"(?P<severity>error|warning)(?:\((?P<code>[^()]+)\))?:"
    r"(?P<message>.*)$"
)
CAP_SENTINEL_RE = re.compile(
    r"(?i)(maximum number of errors|maxErrors|too many errors|error limit)"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_exit(path: Path) -> tuple[int | None, str | None]:
    if not path.exists():
        return None, "missing"
    raw = path.read_text(encoding="utf-8", errors="replace").strip()
    try:
        value = int(raw)
    except ValueError:
        return None, f"invalid:{raw!r}"
    if not 0 <= value <= 255:
        return None, f"out-of-range:{value}"
    return value, None


def normalized_message(message: str) -> str:
    return re.sub(r"\s+", " ", message).strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--max-errors", type=int, default=2000)
    args = parser.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)
    source_exists = args.source.exists()
    source_bytes = args.source.read_bytes() if source_exists else b""
    source_text = source_bytes.decode("utf-8", errors="replace")
    source_name = args.source.name

    declarations = list(DECL_RE.finditer(source_text))
    declaration_starts = [
        source_text.count("\n", 0, match.start()) + 1 for match in declarations
    ]

    fa_log = args.out / "Mock2_FunctionalAnalysis.log"
    log_text = (
        fa_log.read_text(encoding="utf-8", errors="replace")
        if fa_log.exists()
        else ""
    )
    errors: list[dict[str, Any]] = []
    warnings: list[dict[str, Any]] = []
    all_headers: list[dict[str, Any]] = []
    for raw in log_text.splitlines():
        match = DIAGNOSTIC_RE.match(raw)
        if match is None:
            continue
        line = int(match.group("line"))
        diagnostic_file = match.group("file")
        same_source = Path(diagnostic_file).name == source_name
        index = bisect_right(declaration_starts, line) - 1 if same_source else -1
        message = match.group("message").strip()
        item: dict[str, Any] = {
            "file": diagnostic_file,
            "line": line,
            "column": int(match.group("column")),
            "severity": match.group("severity"),
            "diagnostic_code": match.group("code"),
            "message": message,
            "normalized_message_signature": normalized_message(message),
            "source_file_match": same_source,
            "declaration": declarations[index].group("name") if index >= 0 else None,
            "declaration_index": index if index >= 0 else None,
            "raw_header": raw,
        }
        all_headers.append(item)
        if item["severity"] == "error":
            item["ordinal"] = len(errors) + 1
            errors.append(item)
        else:
            item["ordinal"] = len(warnings) + 1
            warnings.append(item)

    exits: dict[str, int | None] = {}
    exit_parse_errors: dict[str, str] = {}
    for stem in STEMS:
        value, error = read_exit(args.out / f"{stem}.exit")
        exits[stem] = value
        if error is not None:
            exit_parse_errors[stem] = error

    candidate_lock_path = args.out / "candidate.sha256"
    locked_candidate_sha = (
        candidate_lock_path.read_text(encoding="utf-8", errors="replace").strip()
        if candidate_lock_path.exists()
        else None
    )
    expected_candidate_sha = os.environ.get("FA_V41_EXPECTED_CANDIDATE_SHA256")
    actual_source_sha = sha256(source_bytes) if source_exists else None
    code_counts = collections.Counter(
        diagnostic["diagnostic_code"] or "<none>" for diagnostic in errors
    )
    declaration_counts = collections.Counter(
        (diagnostic["declaration_index"], diagnostic["declaration"])
        for diagnostic in errors
    )
    cap_sentinel_present = CAP_SENTINEL_RE.search(log_text) is not None
    first = errors[0] if errors else {}

    metric = {
        "schema": SCHEMA,
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "github_head_sha": os.environ.get("GITHUB_SHA"),
        "authority": AUTHORITY,
        "selected_index_expected_sha256": os.environ.get(
            "FA_V41_SELECTED_INDEX_SHA256"
        ),
        "selected_index_actual_sha256": os.environ.get(
            "FA_V41_SELECTED_INDEX_ACTUAL_SHA256"
        ),
        "candidate_expected_sha256": expected_candidate_sha,
        "candidate_locked_sha256": locked_candidate_sha,
        "source_exists": source_exists,
        "source_sha256": actual_source_sha,
        "source_bytes": len(source_bytes) if source_exists else None,
        "source_lines": len(source_text.splitlines()) if source_exists else None,
        "source_identity_locked": bool(
            source_exists
            and expected_candidate_sha
            and locked_candidate_sha
            and actual_source_sha == expected_candidate_sha == locked_candidate_sha
        ),
        "Mock2_exit": exits["Mock2"],
        "Mock2_Advanced_exit": exits["Mock2_Advanced"],
        "FA_exit": exits["Mock2_FunctionalAnalysis"],
        "exit_parse_errors": exit_parse_errors,
        "all_required_lean_executed": all(
            (args.out / f"{stem}.executed").exists() for stem in STEMS
        ),
        "all_required_raw_logs_present": all(
            (args.out / f"{stem}.log").exists() for stem in STEMS
        ),
        "strict_direct_chain_exit_zero": all(exits[stem] == 0 for stem in STEMS),
        "FA_compile_max_errors": args.max_errors,
        "FA_error_headers_captured": len(errors),
        "FA_warning_headers_captured": len(warnings),
        "FA_diagnostic_headers_captured": len(all_headers),
        "FA_error_cap_sentinel_present": cap_sentinel_present,
        "FA_inventory_below_configured_cap": len(errors) < args.max_errors,
        "FA_inventory_complete_by_header_evidence": (
            fa_log.exists()
            and exits["Mock2_FunctionalAnalysis"] is not None
            and not cap_sentinel_present
            and len(errors) < args.max_errors
        ),
        "FA_first_actual_error_line": first.get("line"),
        "FA_first_actual_error_col": first.get("column"),
        "FA_first_error_declaration": first.get("declaration"),
        "FA_error_declaration_index": first.get("declaration_index"),
        "FA_first_error_code": first.get("diagnostic_code"),
        "FA_first_error_message": first.get("message"),
        "unique_declarations_with_errors": len(declaration_counts),
        "unique_normalized_message_signatures": len(
            {diagnostic["normalized_message_signature"] for diagnostic in errors}
        ),
        "error_headers_by_optional_code": dict(sorted(code_counts.items())),
        "direct_lean_verified": exits["Mock2_FunctionalAnalysis"] is not None,
        "full_fa_clean": all(exits[stem] == 0 for stem in STEMS),
    }

    declaration_count_rows = [
        {
            "declaration_index": key[0],
            "declaration": key[1],
            "count": count,
        }
        for key, count in sorted(
            declaration_counts.items(),
            key=lambda item: (
                item[0][0] if item[0][0] is not None else -1,
                item[0][1] or "",
            ),
        )
    ]
    (args.out / "FULL_DIAGNOSTICS.json").write_text(
        json.dumps(errors, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (args.out / "FULL_WARNINGS.json").write_text(
        json.dumps(warnings, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (args.out / "DIAGNOSTIC_DECLARATION_COUNTS.json").write_text(
        json.dumps(
            declaration_count_rows, indent=2, ensure_ascii=False, sort_keys=True
        )
        + "\n",
        encoding="utf-8",
    )
    (args.out / "METRIC.json").write_text(
        json.dumps(metric, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(metric, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

