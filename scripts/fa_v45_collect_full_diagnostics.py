#!/usr/bin/env python3
"""v45 authority adapter for the locked v42 diagnostics collector.

The mature v42 maxErrors=2000 parser, cap check, warning/synthetic-sorry
inventory, and trust scan are reused byte-for-byte.  This wrapper verifies the
dependency hash and substitutes only the v45 schema, authority, and env names.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import os
import sys
from pathlib import Path


HEX = set("0123456789abcdef")
AUTHORITY = {
    "run_id": "31719983304",
    "job_id": "94514229853",
    "head_sha": "dda6274627f628eca6cbfcef48f0c6e572881f0c",
    "head_branch": "codex/fa-qym-cleanbuild-final-20260811-fast",
    "artifact_id": "9189354873",
    "artifact_digest": "sha256:78416b511693fe68bd556674246cc0815015f8fddb46afcdc1e34673eefe87e5",
    "source_sha256": "f8d1b152e1c12639e4fc4f126e501a2a309333c5b8a6f3c8645df3e433572109",
    "diagnostics_sha256": "baab8be659f062f26d4b7563073c18480263747bfa45de88c642aeb13e1f4d07",
    "fa_log_sha256": "4edd03f6c327dda4fa5a49cc3fac56e85004199d3a5dfa7aca0c726ab533a73c",
    "metric_sha256": "65ccfd8035d1c3044de2385fe132fe36fdb08cbd4b67a1742313b18f4c20ea8e",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    bootstrap = argparse.ArgumentParser(add_help=False)
    bootstrap.add_argument("--base-collector", type=Path, required=True)
    bootstrap.add_argument("--base-collector-sha256", required=True)
    known, remaining = bootstrap.parse_known_args()

    expected = known.base_collector_sha256
    require(len(expected) == 64 and set(expected) <= HEX,
            "invalid base collector SHA-256")
    payload = known.base_collector.read_bytes()
    require(sha256(payload) == expected, "base collector SHA mismatch")

    spec = importlib.util.spec_from_file_location(
        "fa_v42_locked_collector", known.base_collector
    )
    require(spec is not None and spec.loader is not None,
            "cannot load locked base collector")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    require(hasattr(module, "main") and hasattr(module, "AUTHORITY"),
            "base collector API mismatch")
    require(tuple(module.STEMS) ==
            ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis"),
            "base collector stem drift")

    module.SCHEMA = "fa-v45-six-variant-highcap2000-metric-v1"
    module.AUTHORITY = dict(AUTHORITY)
    env_map = {
        "FA_V42_VARIANT": "FA_V45_VARIANT",
        "FA_V42_EXPECTED_CANDIDATE_SHA256":
            "FA_V45_EXPECTED_CANDIDATE_SHA256",
        "FA_V42_INDEX_SHA256": "FA_V45_INDEX_SHA256",
        "FA_V42_INDEX_ACTUAL_SHA256": "FA_V45_INDEX_ACTUAL_SHA256",
    }
    for old, new in env_map.items():
        if new in os.environ:
            os.environ[old] = os.environ[new]

    sys.argv = [sys.argv[0], *remaining]
    return int(module.main())


if __name__ == "__main__":
    raise SystemExit(main())
