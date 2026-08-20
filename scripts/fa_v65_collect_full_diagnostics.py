#!/usr/bin/env python3
"""Compatibility adapter for the locked v63/v42 full diagnostic collector.

The proven v63 collector already consumes the v42 raw parser and enforces the
same M2/M2A/FA2000 evidence.  This adapter maps only exact v65 identities; no
fallback collector or alternate path is permitted.
"""

from __future__ import annotations

import hashlib
import os
import subprocess
import sys
from pathlib import Path


V63_COLLECTOR = Path("scripts/fa_v63_collect_full_diagnostics.py")
V63_SHA = "257d3751c889ee45656e7b6e3e1133a67c2e0b0ef8efe117c0ba35386964ac6d"
V42_COLLECTOR = Path("scripts/fa_v42_collect_full_diagnostics.py")
V42_SHA = "7de7bc92e4e2735c0d25706d70777ea67340d8afcf67434e43b051d5cb8c90c6"


def locked(path: Path, expected: str) -> None:
    if path.is_symlink() or not path.is_file():
        raise AssertionError(f"missing ordinary collector: {path}")
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise AssertionError(f"collector SHA mismatch: {path}")


def required(name: str) -> str:
    value = os.environ.get(name)
    if not value:
        raise AssertionError(f"missing environment: {name}")
    return value


def main() -> int:
    locked(V63_COLLECTOR, V63_SHA)
    locked(V42_COLLECTOR, V42_SHA)
    out = required("FA_V65_OUT")
    source = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
    mapping = {
        "FA_V63_VARIANT": required("FA_V65_VARIANT"),
        "FA_V63_EXPECTED_CANDIDATE_SHA256": required("FA_V65_EXPECTED_CANDIDATE_SHA256"),
        "FA_V63_SELECTION_SHA256": required("FA_V65_SELECTION_SHA256"),
        "FA_V63_SELECTION_ACTUAL_SHA256": required("FA_V65_SELECTION_ACTUAL_SHA256"),
        "FA_V63_AUTHORITY_LOCK_SHA256": required("FA_V65_AUTHORITY_LOCK_SHA256"),
        "FA_V63_AUTHORITY_LOCK_ACTUAL_SHA256": required("FA_V65_AUTHORITY_LOCK_ACTUAL_SHA256"),
        "FA_V63_OUT": out,
    }
    env = dict(os.environ)
    env.update(mapping)
    result = subprocess.run(
        [
            sys.executable, str(V63_COLLECTOR),
            "--base-collector", str(V42_COLLECTOR),
            "--base-collector-sha256", V42_SHA,
            "--source", source,
            "--out", out,
            "--max-errors", "2000",
        ],
        env=env,
        check=False,
    )
    if result.returncode != 0:
        raise AssertionError(f"locked collector returned nonzero: {result.returncode}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL-CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(86)
