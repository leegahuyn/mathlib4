#!/usr/bin/env python3
"""Candidate-identity wrapper around the corrected optional-code collector."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import sys
from pathlib import Path


BASE = Path("scripts/fa506r2_collect_full_diagnostics.py")
BASE_SHA256 = "e6e065fedb359ee7a1fa329d5633ce9ea2d05bf8a20ac2e58f9e37ea96ee81a6"
DECLARATION_COUNT = 4_397
DECLARATION_SEQUENCE_SHA256 = (
    "a33d2a1e132e47c9c6b31924ed1b8a04a50de709ed2149a9f9abfb0b052b25eb"
)


def require_sha(name: str) -> str:
    value = os.environ.get(name, "")
    if (
        value.startswith("PENDING")
        or value == "0" * 64
        or re.fullmatch(r"[0-9a-f]{64}", value) is None
    ):
        raise RuntimeError(f"{name} is not a hydrated SHA256")
    return value


def require_int(name: str) -> int:
    value = os.environ.get(name, "")
    if value.startswith("PENDING") or re.fullmatch(r"[1-9][0-9]*", value) is None:
        raise RuntimeError(f"{name} is not a hydrated positive decimal")
    return int(value)


try:
    data = BASE.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != BASE_SHA256:
        raise RuntimeError(f"corrected collector SHA drift: {actual}; expected {BASE_SHA256}")
    spec = importlib.util.spec_from_file_location("fa_corrected_collector_locked", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {BASE}")
    collector = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = collector
    spec.loader.exec_module(collector)

    collector.EXPECTED_SOURCE_SHA256 = require_sha("FA_FULL_EXPECTED_SHA256")
    collector.EXPECTED_SOURCE_BYTES = require_int("FA_FULL_EXPECTED_BYTES")
    collector.EXPECTED_SOURCE_LINES = require_int("FA_FULL_EXPECTED_LINES")
    collector.EXPECTED_DECLARATION_COUNT = DECLARATION_COUNT
    collector.EXPECTED_DECLARATION_SEQUENCE_SHA256 = DECLARATION_SEQUENCE_SHA256
    collector.EXPECTED_MAX_ERRORS = 2_000

    original_collect = collector.collect

    def cumulative_collect(args):
        payload = original_collect(args)
        metric = json.loads(args.metric.read_text(encoding="utf-8"))
        entries = (payload.get("diagnostics") or {}).get("entries", [])
        errors = [entry for entry in entries if entry.get("severity") == "error"]
        if errors:
            first = errors[0]
            payload["known_frontier"] = {
                "status": "OBSERVED_THIS_CUMULATIVE_RUN",
                "declaration": first.get("declaration"),
                "declaration_index": first.get("declaration_index"),
                "source_line": first.get("line"),
                "source_col": first.get("col"),
                "diagnostic_code": first.get("diagnostic_code"),
            }
        else:
            payload["known_frontier"] = {
                "status": "DIRECT_PASS_NO_ERROR_DIAGNOSTIC",
                "declaration": None,
                "declaration_index": None,
                "source_line": None,
                "source_col": None,
                "diagnostic_code": None,
            }

        # The original collector requires a nonempty raw log.  A fully clean
        # direct Lean invocation may legitimately emit zero bytes.  In that
        # one case only, recompute the gate from every remaining exact check.
        log_bytes = args.log.read_bytes()
        if not log_bytes and metric.get("FA_exit") == 0:
            source = payload.get("source") or {}
            compile_info = payload.get("compile") or {}
            parser = payload.get("declaration_parser") or {}
            payload["all_checks_passed"] = all(
                (
                    source.get("identity_passed") is True,
                    parser.get("identity_passed") is True,
                    compile_info.get("command_max_errors_verified") is True,
                    compile_info.get("metric_max_errors_verified") is True,
                    compile_info.get("executed_marker_verified") is True,
                    (payload.get("diagnostics") or {}).get("count") == 0,
                )
            )
            (payload.setdefault("log", {}))["empty_log_allowed_for_direct_pass"] = True
        elif not log_bytes:
            payload["all_checks_passed"] = False
            (payload.setdefault("log", {}))["empty_log_rejected_for_nonzero_FA_exit"] = True

        payload["collector_profile"] = {
            "schema": "fa-full-cumulative-corrected-collector-wrapper-v1",
            "base_collector_sha256": BASE_SHA256,
            "optional_diagnostic_codes_supported": True,
            "parse_cap": None,
            "source_identity_from_hydrated_candidate": True,
            "raw_log_stored_unmodified": True,
        }
        return payload

    collector.collect = cumulative_collect
except Exception as error:
    print(f"FA cumulative collector initialization failure: {error}", file=sys.stderr)
    sys.exit(86)


if __name__ == "__main__":
    sys.exit(collector.main())
