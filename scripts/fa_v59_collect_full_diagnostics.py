#!/usr/bin/env python3
"""v59 provenance adapter for the SHA-locked v42 diagnostics collector.

The mature parser and trust scan are reused byte-for-byte after SHA and byte
verification.  Before execution, this adapter replaces the stale v42 schema
and authority with the exact v58 core_base authority.  After execution it
reopens METRIC.json and fails unless base authority, current GitHub run/head,
selection index, variant, and candidate identity are all current and exact.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
from pathlib import Path


BASE_COLLECTOR_SHA256 = (
    "7de7bc92e4e2735c0d25706d70777ea67340d8afcf67434e43b051d5cb8c90c6"
)
BASE_COLLECTOR_BYTES = 12932
SCHEMA = "fa-v59-independent-matrix-highcap2000-metric-v1"
AUTHORITY = {
    "workflow_run_id": 31803223990,
    "head_sha": "14e3e3f5e85f3c3ca7a1381eb88522552ffe29dc",
    "head_branch": "codex/fa-exclusive-focus-20260814",
    "artifact_id": 9220688452,
    "artifact_name": (
        "codex-fa-v58-core_base-highcap2000-"
        "14e3e3f5e85f3c3ca7a1381eb88522552ffe29dc"
    ),
    "artifact_size_in_bytes": 619491,
    "artifact_digest":
        "sha256:269100960a5e7ecd8b35e39cdde2c774f244b49c269e992aec00203bd2288ab4",
    "variant": "core_base",
    "source_sha256":
        "013f64cf5eaaab544629ad02fc2e33e63f90916e9b1e1581d73f2af2e7ba34ba",
    "source_bytes": 2807163,
    "source_lines": 62815,
    "declaration_count": 4416,
    "diagnostics_sha256":
        "a9ec828f9bbe0226b2bc694f26911cfd84fce016adca411f9bb8df52c6833db1",
    "fa_log_sha256":
        "8395ab207c12ad32483166ec9a118b4fe1d82a1c772d5cd79d9237563efc9127",
    "patch_audit_sha256":
        "372037c8eee8ce1a030e5085b831b5f04c9bfaaa9e8f707767ed48ecbe630b9a",
}
TRUST_TOKENS = (
    "sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool"
)
STEMS = ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def required_env(name: str) -> str:
    value = os.environ.get(name)
    require(bool(value), f"missing environment variable: {name}")
    return str(value)


def validate_runtime_identity(
    *,
    variant: str,
    expected_candidate: str,
    expected_index: str,
    actual_index: str,
    current_run: str,
    current_head: str,
) -> None:
    require(bool(variant), "empty v59 variant")
    require(re.fullmatch(r"[0-9]+", current_run) is not None,
            "invalid current GitHub run ID")
    for label, value in (
        ("candidate", expected_candidate),
        ("expected index", expected_index),
        ("actual index", actual_index),
    ):
        require(re.fullmatch(r"[0-9a-f]{64}", value) is not None,
                f"invalid {label} SHA-256")
    require(re.fullmatch(r"[0-9a-f]{40}", current_head) is not None,
            "invalid current Git commit SHA")
    require(expected_index == actual_index, "selection index identity mismatch")


def main() -> int:
    bootstrap = argparse.ArgumentParser(add_help=False)
    bootstrap.add_argument("--base-collector", type=Path, required=True)
    bootstrap.add_argument("--base-collector-sha256", required=True)
    known, remaining = bootstrap.parse_known_args()

    require(known.base_collector_sha256 == BASE_COLLECTOR_SHA256,
            "configured base collector SHA differs from promoted lock")
    payload = known.base_collector.read_bytes()
    require(sha256(payload) == BASE_COLLECTOR_SHA256,
            "base collector SHA mismatch")
    require(len(payload) == BASE_COLLECTOR_BYTES,
            "base collector byte mismatch")

    spec = importlib.util.spec_from_file_location(
        "fa_v59_locked_v42_collector", known.base_collector
    )
    require(spec is not None and spec.loader is not None,
            "cannot load locked base collector")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    require(hasattr(module, "main") and hasattr(module, "AUTHORITY"),
            "base collector API mismatch")
    require(tuple(module.STEMS) == STEMS, "base collector stem drift")
    require(tuple(module.TRUST_TOKENS) == TRUST_TOKENS,
            "base collector trust-six drift")

    variant = required_env("FA_V59_VARIANT")
    expected_candidate = required_env("FA_V59_EXPECTED_CANDIDATE_SHA256")
    expected_index = required_env("FA_V59_INDEX_SHA256")
    actual_index = required_env("FA_V59_INDEX_ACTUAL_SHA256")
    current_run = required_env("GITHUB_RUN_ID")
    current_head = required_env("GITHUB_SHA")
    validate_runtime_identity(
        variant=variant,
        expected_candidate=expected_candidate,
        expected_index=expected_index,
        actual_index=actual_index,
        current_run=current_run,
        current_head=current_head,
    )

    module.SCHEMA = SCHEMA
    module.AUTHORITY = dict(AUTHORITY)
    env_map = {
        "FA_V42_VARIANT": variant,
        "FA_V42_EXPECTED_CANDIDATE_SHA256": expected_candidate,
        "FA_V42_INDEX_SHA256": expected_index,
        "FA_V42_INDEX_ACTUAL_SHA256": actual_index,
    }
    os.environ.update(env_map)
    sys.argv = [sys.argv[0], *remaining]
    result = int(module.main())
    require(result == 0, "base collector returned nonzero")

    out = None
    for position, value in enumerate(remaining):
        if value == "--out" and position + 1 < len(remaining):
            out = Path(remaining[position + 1])
            break
    require(out is not None, "collector --out argument missing")
    metric_path = out / "METRIC.json"
    require(metric_path.is_file(), "collector did not emit METRIC.json")
    metric = json.loads(metric_path.read_text(encoding="utf-8"))
    require(metric.get("schema") == SCHEMA, "v59 metric schema mismatch")
    require(metric.get("authority") == AUTHORITY,
            "stale or altered metric authority")
    require(metric.get("github_run_id") == current_run,
            "metric current run mismatch")
    require(metric.get("github_head_sha") == current_head,
            "metric current head mismatch")
    require(metric.get("variant") == variant, "metric variant mismatch")
    require(metric.get("variant_index_expected_sha256") == expected_index,
            "metric expected index mismatch")
    require(metric.get("variant_index_actual_sha256") == actual_index,
            "metric actual index mismatch")
    require(metric.get("candidate_expected_sha256") == expected_candidate,
            "metric expected candidate mismatch")
    require(metric.get("source_sha256") == expected_candidate,
            "metric observed candidate mismatch")
    require(metric.get("candidate_locked_sha256") == expected_candidate,
            "metric locked candidate mismatch")
    require(metric.get("source_declaration_count") == 4416,
            "metric declaration count mismatch")
    require(metric.get("source_executable_trust_six_zero") is True,
            "metric trust-six is not zero")
    trust_counts = metric.get("source_executable_trust_counts")
    require(trust_counts == {token: 0 for token in TRUST_TOKENS},
            "metric trust-six key/value drift")
    require(metric.get("source_identity_locked") is True,
            "metric source identity is not locked")
    require(metric.get("all_required_raw_logs_uploaded") is True,
            "metric required raw logs are not all present")
    require(metric.get("all_required_raw_logs_from_execution") is True,
            "metric raw logs include collector placeholders")
    require(metric.get("raw_log_placeholders") == [],
            "metric reports raw-log placeholders")
    warnings_path = out / "FULL_WARNINGS.json"
    diagnostics_path = out / "FULL_DIAGNOSTICS.json"
    synthetic_path = out / "SYNTHETIC_SORRY_WARNINGS.json"
    require(warnings_path.is_file() and diagnostics_path.is_file()
            and synthetic_path.is_file(), "collector JSON inventory missing")
    warnings = json.loads(warnings_path.read_text(encoding="utf-8"))
    diagnostics = json.loads(diagnostics_path.read_text(encoding="utf-8"))
    synthetic = json.loads(synthetic_path.read_text(encoding="utf-8"))
    require(isinstance(warnings, list) and isinstance(diagnostics, list)
            and isinstance(synthetic, list), "collector JSON inventory type mismatch")
    require(len(warnings) == metric.get("FA_warning_headers_captured"),
            "full warning inventory does not reconcile")
    require(len(diagnostics) == metric.get("FA_error_headers_captured"),
            "full diagnostic inventory does not reconcile")
    require(synthetic == [], "synthetic declaration-uses-sorry warning present")
    require(metric.get("synthetic_declaration_uses_sorry_warning_count") == 0,
            "metric synthetic-sorry count is nonzero")
    require(metric.get("synthetic_trust_clean") is True,
            "metric synthetic trust is not clean")

    attestation = {
        "schema": "fa-v59-collector-authority-attestation-v1",
        "status": "EXACT_CURRENT_PROVENANCE",
        "base_collector_sha256": BASE_COLLECTOR_SHA256,
        "base_collector_bytes": BASE_COLLECTOR_BYTES,
        "metric_sha256": sha256(metric_path.read_bytes()),
        "base_authority": AUTHORITY,
        "current_github_run_id": current_run,
        "current_github_head_sha": current_head,
        "selection_index_sha256": expected_index,
        "variant": variant,
        "candidate_sha256": expected_candidate,
        "source_identity_locked": True,
        "source_executable_trust_counts": trust_counts,
        "all_required_raw_logs_uploaded": True,
        "all_required_raw_logs_from_execution": True,
        "full_warning_count": len(warnings),
        "full_diagnostic_count": len(diagnostics),
        "synthetic_declaration_uses_sorry_warning_count": 0,
        "synthetic_trust_clean": True,
        "stale_v42_authority_rejected": True,
    }
    (out / "COLLECTOR_AUTHORITY_ATTESTATION.json").write_text(
        json.dumps(attestation, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
