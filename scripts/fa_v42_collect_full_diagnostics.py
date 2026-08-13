#!/usr/bin/env python3
"""Collect complete FA v42 compile evidence without invoking Lean or network.

The collector is designed for an ``always()`` workflow step. Missing source,
logs, or exit files are represented explicitly while METRIC.json and the full
diagnostic inventories are still emitted. Compiler-created ``declaration uses
`sorry``` warnings are counted separately from the six-token source scan.
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


SCHEMA = "fa-v42-two-variant-highcap2000-metric-v1"
AUTHORITY = {
    "run_id": "31699916923",
    "job_id": "94446323369",
    "head_sha": "6867203e032c9711b47d8c2e1bd74f30d15cbd59",
    "head_branch": "codex/fa-qym-cleanbuild-final-20260811-fast",
    "artifact_id": "9181214334",
    "artifact_digest": "sha256:bb18b117b461a4fd36746685ce4437d835382989d4b7e1cff87bb6ebbcc9c870",
    "source_sha256": "d7e99092e79b26af21cd8c960b8e9c811731e27343757b750b62c53608805937",
    "diagnostics_sha256": "b50357457a8213b1a53ae353c67fd7639334a9db4b5f7a4e61ad9c00b9f07fcf",
    "fa_log_sha256": "dc4370280c35eb1b8565e9776d9e93e42f4bf299b543a4bdaea029f438445530",
}
STEMS = ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")
TRUST_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)
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
SYNTHETIC_SORRY_RE = re.compile(r"(?i)declaration\s+uses\s+[`']?sorry[`']?")


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


def strip_noncode(text: str) -> str:
    chars = list(text)
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(chars):
        if depth:
            if text.startswith("/-", i):
                chars[i] = chars[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                chars[i] = chars[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue
        if in_string:
            original = chars[i]
            if original != "\n":
                chars[i] = " "
            if escaped:
                escaped = False
            elif original == "\\":
                escaped = True
            elif original == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            chars[i] = chars[i + 1] = " "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        if chars[i] == '"':
            chars[i] = " "
            in_string = True
        i += 1
    return "".join(chars)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        token: len(
            re.findall(
                r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])",
                code,
            )
        )
        for token in TRUST_TOKENS
    }


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

    missing_raw_logs_before_collection = [
        stem for stem in STEMS if not (args.out / f"{stem}.log").exists()
    ]
    for stem in missing_raw_logs_before_collection:
        (args.out / f"{stem}.log").write_text(
            "NOT_EXECUTED_OR_LOG_MISSING_BEFORE_ALWAYS_COLLECTOR\n",
            encoding="utf-8",
        )
    fa_log = args.out / "Mock2_FunctionalAnalysis.log"
    log_text = fa_log.read_text(encoding="utf-8", errors="replace")
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
    expected_candidate_sha = os.environ.get("FA_V42_EXPECTED_CANDIDATE_SHA256")
    actual_source_sha = sha256(source_bytes) if source_exists else None
    source_trust = trust_counts(source_text) if source_exists else {token: 0 for token in TRUST_TOKENS}
    code_counts = collections.Counter(
        diagnostic["diagnostic_code"] or "<none>" for diagnostic in errors
    )
    declaration_counts = collections.Counter(
        (diagnostic["declaration_index"], diagnostic["declaration"])
        for diagnostic in errors
    )
    synthetic_sorry = [
        warning for warning in warnings if SYNTHETIC_SORRY_RE.search(warning["message"])
    ]
    cap_sentinel_present = CAP_SENTINEL_RE.search(log_text) is not None
    first = errors[0] if errors else {}
    compiler_exit_clean = all(exits[stem] == 0 for stem in STEMS)
    semantic_clean = (
        compiler_exit_clean
        and not synthetic_sorry
        and source_exists
        and all(value == 0 for value in source_trust.values())
    )

    metric = {
        "schema": SCHEMA,
        "variant": os.environ.get("FA_V42_VARIANT"),
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "github_head_sha": os.environ.get("GITHUB_SHA"),
        "authority": AUTHORITY,
        "variant_index_expected_sha256": os.environ.get("FA_V42_INDEX_SHA256"),
        "variant_index_actual_sha256": os.environ.get("FA_V42_INDEX_ACTUAL_SHA256"),
        "candidate_expected_sha256": expected_candidate_sha,
        "candidate_locked_sha256": locked_candidate_sha,
        "source_exists": source_exists,
        "source_sha256": actual_source_sha,
        "source_bytes": len(source_bytes) if source_exists else None,
        "source_lines": len(source_text.splitlines()) if source_exists else None,
        "source_declaration_count": len(declarations) if source_exists else None,
        "source_executable_trust_counts": source_trust,
        "source_executable_trust_six_zero": source_exists and all(value == 0 for value in source_trust.values()),
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
        "all_required_lean_executed": all((args.out / f"{stem}.executed").exists() for stem in STEMS),
        "all_required_raw_logs_uploaded": all((args.out / f"{stem}.log").exists() for stem in STEMS),
        "all_required_raw_logs_from_execution": not missing_raw_logs_before_collection,
        "raw_log_placeholders": missing_raw_logs_before_collection,
        "compiler_exit_clean": compiler_exit_clean,
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
        "FA_first_error_declaration_index": first.get("declaration_index"),
        "FA_first_error_code": first.get("diagnostic_code"),
        "FA_first_error_message": first.get("message"),
        "unique_declarations_with_errors": len(declaration_counts),
        "unique_normalized_message_signatures": len(
            {diagnostic["normalized_message_signature"] for diagnostic in errors}
        ),
        "error_headers_by_optional_code": dict(sorted(code_counts.items())),
        "synthetic_declaration_uses_sorry_warning_count": len(synthetic_sorry),
        "synthetic_declaration_uses_sorry_warning_declarations": sorted(
            {
                warning["declaration"]
                for warning in synthetic_sorry
                if warning["declaration"] is not None
            }
        ),
        "synthetic_trust_clean": not synthetic_sorry,
        "direct_lean_verified": (
            (args.out / "Mock2_FunctionalAnalysis.executed").exists()
            and exits["Mock2_FunctionalAnalysis"] is not None
        ),
        "semantic_clean": semantic_clean,
    }

    declaration_count_rows = [
        {"declaration_index": key[0], "declaration": key[1], "count": count}
        for key, count in sorted(
            declaration_counts.items(),
            key=lambda item: (
                item[0][0] if item[0][0] is not None else -1,
                item[0][1] or "",
            ),
        )
    ]
    outputs = {
        "FULL_DIAGNOSTICS.json": errors,
        "FULL_WARNINGS.json": warnings,
        "DIAGNOSTIC_DECLARATION_COUNTS.json": declaration_count_rows,
        "SYNTHETIC_SORRY_WARNINGS.json": synthetic_sorry,
        "METRIC.json": metric,
    }
    for name, value in outputs.items():
        (args.out / name).write_text(
            json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(json.dumps(metric, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
