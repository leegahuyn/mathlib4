#!/usr/bin/env python3
"""v43 authority adapter for the locked v42 diagnostics collector.

The mature v42 parser, complete inventory, cap-sentinel check, synthetic-sorry
inventory, and trust scan are reused byte-for-byte.  This wrapper verifies the
dependency SHA, replaces only its evidence schema/authority, and maps v43
environment names to the collector's existing interface.
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
    "run_id": "31709054520",
    "job_id": "94476949087",
    "head_sha": "d6e8e7d12bbf76bf371bb0f21c085f0ebd4ba199",
    "head_branch": "codex/fa-qym-cleanbuild-final-20260811-fast",
    "artifact_id": "9184978707",
    "artifact_digest": "sha256:a587808a5ca47993bba554673c4b24d2f8c6cbea08415be69db7f9f11923e042",
    "source_sha256": "442dc2841f80b6814a16396a9b08ec27e90d3bd3d1913c4edd417137d8d1bbe7",
    "diagnostics_sha256": "d71f00c9181ff3bdce00ca39d0bbb33367c3f939ee1ad2c47d4982f639406a8a",
    "fa_log_sha256": "63b5dacbe7a6d40280ad0dea17001ef730a99a17400da72d8665d97b7d49c899",
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

    module.SCHEMA = "fa-v43-five-variant-highcap2000-metric-v1"
    module.AUTHORITY = dict(AUTHORITY)
    env_map = {
        "FA_V42_VARIANT": "FA_V43_VARIANT",
        "FA_V42_EXPECTED_CANDIDATE_SHA256":
            "FA_V43_EXPECTED_CANDIDATE_SHA256",
        "FA_V42_INDEX_SHA256": "FA_V43_INDEX_SHA256",
        "FA_V42_INDEX_ACTUAL_SHA256": "FA_V43_INDEX_ACTUAL_SHA256",
    }
    for old, new in env_map.items():
        if new in os.environ:
            os.environ[old] = os.environ[new]

    sys.argv = [sys.argv[0], *remaining]
    return int(module.main())


if __name__ == "__main__":
    raise SystemExit(main())
