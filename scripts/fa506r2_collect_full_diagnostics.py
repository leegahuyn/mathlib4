#!/usr/bin/env python3
"""Collect the complete direct-Lean diagnostic inventory for the d0a3 source.

This parser never truncates or caps the diagnostics it reads.  The raw Lean log
remains the authority and is hashed into the result; this JSON is a navigable
index over that exact byte stream.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from bisect import bisect_right
from pathlib import Path
from typing import Any

SCHEMA = "fa506r2-full-diagnostics-v1"
EXPECTED_SOURCE_SHA256 = (
    "d0a3decee1c0a7a781d14fdf122e235d71d8f210bb65a894dc4e518821bf03ec"
)
EXPECTED_SOURCE_BYTES = 2_702_252
EXPECTED_SOURCE_LINES = 60_573
EXPECTED_DECLARATION_COUNT = 4_397
EXPECTED_DECLARATION_SEQUENCE_SHA256 = (
    "a33d2a1e132e47c9c6b31924ed1b8a04a50de709ed2149a9f9abfb0b052b25eb"
)
EXPECTED_MAX_ERRORS = 2_000

DECLARATION_PATTERN_TEXT = (
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s(:]+)"
)
DECLARATION_PATTERN = re.compile(DECLARATION_PATTERN_TEXT)
DIAGNOSTIC_PATTERN = re.compile(
    r"^(?P<file>.+?\.lean):(?P<line>[0-9]+):(?P<col>[0-9]+): "
    r"(?P<severity>error|warning|info):(?P<message>.*)$"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--metric", type=Path, required=True)
    parser.add_argument("--command", type=Path, required=True)
    parser.add_argument("--executed", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def declaration_inventory(source: str) -> tuple[list[dict[str, Any]], str]:
    matches = list(DECLARATION_PATTERN.finditer(source))
    declarations: list[dict[str, Any]] = []
    for index, match in enumerate(matches):
        start_line = source.count("\n", 0, match.start()) + 1
        next_start = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        end_line = source.count("\n", 0, next_start) + 1
        declarations.append(
            {
                "index": index,
                "name": match.group("name"),
                "start_line": start_line,
                "end_line": end_line,
            }
        )
    sequence_sha = sha256(
        "\n".join(item["name"] for item in declarations).encode("utf-8")
    )
    return declarations, sequence_sha


def parse_diagnostics(
    log_text: str, declarations: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    starts = [item["start_line"] for item in declarations]
    entries: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    for raw_line in log_text.splitlines():
        match = DIAGNOSTIC_PATTERN.match(raw_line)
        if match:
            if current is not None:
                current["message"] = "\n".join(current.pop("message_lines"))
                entries.append(current)
            line = int(match.group("line"))
            declaration_position = bisect_right(starts, line) - 1
            declaration = (
                declarations[declaration_position]
                if declaration_position >= 0
                else None
            )
            current = {
                "ordinal": len(entries),
                "severity": match.group("severity"),
                "file": match.group("file"),
                "line": line,
                "col": int(match.group("col")),
                "header": raw_line,
                "message_lines": [match.group("message").lstrip()],
                "declaration": declaration["name"] if declaration else None,
                "declaration_index": declaration["index"] if declaration else None,
                "declaration_start_line": (
                    declaration["start_line"] if declaration else None
                ),
            }
        elif current is not None:
            current["message_lines"].append(raw_line)
    if current is not None:
        current["message"] = "\n".join(current.pop("message_lines"))
        entries.append(current)
    return entries


def collect(args: argparse.Namespace) -> dict[str, Any]:
    source_bytes = args.source.read_bytes()
    source_text = source_bytes.decode("utf-8")
    log_bytes = args.log.read_bytes()
    log_text = log_bytes.decode("utf-8", errors="replace")
    command_text = args.command.read_text(encoding="utf-8", errors="replace").strip()
    metric = json.loads(args.metric.read_text(encoding="utf-8"))

    source_identity = {
        "sha256": sha256(source_bytes),
        "bytes": len(source_bytes),
        "lines": len(source_text.splitlines()),
    }
    source_identity_passed = source_identity == {
        "sha256": EXPECTED_SOURCE_SHA256,
        "bytes": EXPECTED_SOURCE_BYTES,
        "lines": EXPECTED_SOURCE_LINES,
    }
    declarations, sequence_sha = declaration_inventory(source_text)
    declaration_identity_passed = (
        len(declarations) == EXPECTED_DECLARATION_COUNT
        and sequence_sha == EXPECTED_DECLARATION_SEQUENCE_SHA256
    )
    diagnostics = parse_diagnostics(log_text, declarations)
    severity_counts = {
        severity: sum(item["severity"] == severity for item in diagnostics)
        for severity in ("error", "warning", "info")
    }
    command_max_errors_verified = (
        f"-DmaxErrors={EXPECTED_MAX_ERRORS}" in command_text
    )
    metric_max_errors_verified = metric.get("maxErrors_cap") == EXPECTED_MAX_ERRORS
    executed_marker_verified = args.executed.is_file()
    all_checks_passed = all(
        (
            source_identity_passed,
            declaration_identity_passed,
            len(log_bytes) > 0,
            command_max_errors_verified,
            metric_max_errors_verified,
            executed_marker_verified,
        )
    )
    return {
        "schema": SCHEMA,
        "all_checks_passed": all_checks_passed,
        "known_frontier": {
            "status": "KNOWN_FIX_PENDING",
            "declaration": (
                "complex_image_heightStrip_eq_coe_image_selectedBaseCuspStrip"
            ),
            "declaration_index": 2_839,
            "source_line": 36_111,
            "source_col": 4,
            "membership_only_job_id": 93_786_800_858,
            "membership_only_result": (
                "Set.mem_prod exposes hp as a conjunction but does not normalize "
                "the constructed UpperHalfPlane projections in the target"
            ),
            "next_repair_candidates": [
                "add UpperHalfPlane.mk_re and UpperHalfPlane.mk_im",
                "explicitly rcases the membership conjunction",
            ],
        },
        "source": {
            "path": str(args.source),
            **source_identity,
            "expected_sha256": EXPECTED_SOURCE_SHA256,
            "expected_bytes": EXPECTED_SOURCE_BYTES,
            "expected_lines": EXPECTED_SOURCE_LINES,
            "identity_passed": source_identity_passed,
        },
        "compile": {
            "expected_max_errors": EXPECTED_MAX_ERRORS,
            "command_path": str(args.command),
            "command": command_text,
            "command_max_errors_verified": command_max_errors_verified,
            "metric_max_errors_verified": metric_max_errors_verified,
            "executed_marker_path": str(args.executed),
            "executed_marker_verified": executed_marker_verified,
        },
        "log": {
            "path": str(args.log),
            "sha256": sha256(log_bytes),
            "bytes": len(log_bytes),
            "lines": len(log_text.splitlines()),
            "panic_mentions": len(re.findall(r"(?i)\bPANIC\b", log_text)),
            "stored_unmodified": True,
        },
        "declaration_parser": {
            "authority": "fa506r2_collect_full_diagnostics.py",
            "pattern": DECLARATION_PATTERN_TEXT,
            "pattern_sha256": sha256(DECLARATION_PATTERN_TEXT.encode("utf-8")),
            "declaration_count": len(declarations),
            "expected_declaration_count": EXPECTED_DECLARATION_COUNT,
            "declaration_sequence_sha256": sequence_sha,
            "expected_declaration_sequence_sha256": (
                EXPECTED_DECLARATION_SEQUENCE_SHA256
            ),
            "identity_passed": declaration_identity_passed,
        },
        "diagnostics": {
            "parse_cap": None,
            "complete_log_scanned": True,
            "count": len(diagnostics),
            "severity_counts": severity_counts,
            "entries": diagnostics,
        },
        "metric_path": str(args.metric),
        "metric": metric,
    }


def main() -> int:
    args = parse_args()
    try:
        payload = collect(args)
        exit_code = 0 if payload["all_checks_passed"] else 86
    except Exception as exc:  # keep an uploadable fail-closed record
        payload = {
            "schema": SCHEMA,
            "all_checks_passed": False,
            "fatal_error": f"{type(exc).__name__}: {exc}",
        }
        exit_code = 86
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
