#!/usr/bin/env python3
"""v46 authority adapter for the locked v42 diagnostics collector.

The mature maxErrors=2000 parser, cap check, complete error/warning inventory,
synthetic-sorry inventory, raw-execution evidence, source identity lock, and
trust-six scan are reused byte-for-byte.  This wrapper changes only the schema,
authority attestation, and environment names after SHA-verifying the collector.
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
    "run_id": "31728453514",
    "job_id": "94542617528",
    "head_sha": "5ec44f3d343955f3124e7efecc048b648dccc5ab",
    "head_branch": "codex/fa-qym-cleanbuild-final-20260811-fast",
    "artifact_id": "9192669673",
    "artifact_digest": "sha256:8f07a678145b62342aaa9cb94ebbce6c9f7cc1a45c400560918d42499e67f2f3",
    "source_sha256": "726f40d1dd03d32f03592adf4f6b02e3f7f52e7e1f71087ee53bdb83c4bb0caf",
    "diagnostics_sha256": "1fb14600849d7281df6ff65ae9213b6671b19a396cf539041f864fea157476a1",
    "fa_log_sha256": "bcc92a247a531419b25677cfdd5e28ce1705e6c3fb87301b93e24510932b4888",
    "metric_sha256": "ff9a1400bc020ac417bab4558dc5313a75a8910b89ee6107d2b913ecc9b6353f",
    "patch_audit_sha256": "045fe75a7b0b7691e58b01dd97e87d1e9d76d4f84648b34745870d902df7ec94",
    "variant_index_sha256": "e96fe0bafb8e145148170b9cf46ac223c97887354de68491018d1baa53b3dfdc",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


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
        "fa_v46_locked_collector", known.base_collector
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
    require(tuple(module.TRUST_TOKENS) ==
            ("sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool"),
            "base collector trust-token drift")

    module.SCHEMA = "fa-v46-five-variant-highcap2000-metric-v1"
    module.AUTHORITY = dict(AUTHORITY)
    env_map = {
        "FA_V42_VARIANT": "FA_V46_VARIANT",
        "FA_V42_EXPECTED_CANDIDATE_SHA256":
            "FA_V46_EXPECTED_CANDIDATE_SHA256",
        "FA_V42_INDEX_SHA256": "FA_V46_INDEX_SHA256",
        "FA_V42_INDEX_ACTUAL_SHA256": "FA_V46_INDEX_ACTUAL_SHA256",
    }
    for old, new in env_map.items():
        if new in os.environ:
            os.environ[old] = os.environ[new]

    sys.argv = [sys.argv[0], *remaining]
    return int(module.main())


if __name__ == "__main__":
    raise SystemExit(main())
