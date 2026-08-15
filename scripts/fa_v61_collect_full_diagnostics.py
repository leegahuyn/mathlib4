#!/usr/bin/env python3
"""v61 provenance adapter for the SHA-locked v42 diagnostics collector.

The mature parser and trust scan are reused byte-for-byte after SHA and byte
verification.  Before execution, this adapter replaces the stale v42 schema
and authority with the exact v60 winner A_no_idx3933 authority. After execution it
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
SCHEMA = "fa-v61-direct-eight-way-highcap2000-metric-v1"
AUTHORITY = {
    "workflow_run_id": 31857051709,
    "head_sha": "21f3bd08703a2d3e73375d69cd2474a7366a4497",
    "head_branch": "codex/fa-exclusive-focus-20260814",
    "job_id": 94943712491,
    "artifact_id": 9239620079,
    "artifact_name": (
        "codex-fa-v59-A_no_idx3933-highcap2000-"
        "21f3bd08703a2d3e73375d69cd2474a7366a4497"
    ),
    "artifact_size_in_bytes": 1674379,
    "artifact_digest":
        "sha256:6c2e6f9a1515ddd032c8edf860de30b3c98e82f399e150e06a56d351c2a9b5cf",
    "variant": "A_no_idx3933",
    "source_sha256":
        "84e0a7843de9bcf99a25e51db95d48e9d5feceffe4e1b94f315b11d166792e5a",
    "source_bytes": 2812433,
    "source_lines": 62933,
    "declaration_count": 4416,
    "diagnostics_sha256":
        "0365e539e8e52b13bcbc9ca5d9f67e2e198274c83ff7a3a7db4b4620830d790b",
    "fa_log_sha256":
        "5ea7f5733056f2691b460f714db846c3478a47dc709a0d41e6c31ce90f0f93bf",
    "patch_audit_sha256":
        "94f10d6ca9316b7406dd96e8bab887cabb0423005c8931233010f52210c6bc08",
    "toolchain_pin_sha256":
        "3fcdaf1fb2568e48b557e44d215abffcd742c4154309c13bb8b9e735564ceee7",
    "selection_sha256":
        "3bccb507dc1971c6a053b8e7dfe5c079b02f15dd85455aed136b8bab2facf45c",
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
    require(bool(variant), "empty v61 variant")
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
        "fa_v61_locked_v42_collector", known.base_collector
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

    variant = required_env("FA_V61_VARIANT")
    expected_candidate = required_env("FA_V61_EXPECTED_CANDIDATE_SHA256")
    expected_index = required_env("FA_V61_INDEX_SHA256")
    actual_index = required_env("FA_V61_INDEX_ACTUAL_SHA256")
    authority_lock_expected = required_env("FA_V61_AUTHORITY_LOCK_SHA256")
    authority_lock_actual = required_env("FA_V61_AUTHORITY_LOCK_ACTUAL_SHA256")
    require(authority_lock_expected == authority_lock_actual,
            "authority-lock identity mismatch")
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
    require(metric.get("schema") == SCHEMA, "v61 metric schema mismatch")
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
    require(metric.get("all_required_lean_executed") is True,
            "metric direct execution markers are incomplete")
    require(metric.get("FA_inventory_below_configured_cap") is True,
            "full FA inventory reached configured cap")
    exit_keys = {
        "Mock2": "Mock2_exit",
        "Mock2_Advanced": "Mock2_Advanced_exit",
        "Mock2_FunctionalAnalysis": "FA_exit",
    }
    raw_reconciliation: dict[str, dict[str, object]] = {}
    for stem in STEMS:
        executed = out / f"{stem}.executed"
        exit_path = out / f"{stem}.exit"
        log_path = out / f"{stem}.log"
        command_path = out / f"{stem}.command"
        require(executed.is_file() and executed.read_bytes() == b"",
                f"invalid execution marker: {stem}")
        require(exit_path.is_file(), f"missing raw exit: {stem}")
        exit_text = exit_path.read_text(encoding="utf-8")
        require(re.fullmatch(r"[0-9]+\n", exit_text) is not None,
                f"non-canonical raw exit: {stem}")
        raw_exit = int(exit_text)
        require(raw_exit == metric.get(exit_keys[stem]),
                f"raw exit/metric mismatch: {stem}")
        require(log_path.is_file(), f"missing raw execution log: {stem}")
        require(command_path.is_file() and bool(command_path.read_bytes()),
                f"missing raw command: {stem}")
        raw_reconciliation[stem] = {
            "executed_marker_exact_empty_file": True,
            "exit": raw_exit,
            "metric_exit_field": exit_keys[stem],
            "log_present": True,
            "log_bytes": len(log_path.read_bytes()),
            "command_present_nonempty": True,
        }
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
        "schema": "fa-v61-collector-authority-attestation-v1",
        "status": "EXACT_CURRENT_PROVENANCE",
        "base_collector_sha256": BASE_COLLECTOR_SHA256,
        "base_collector_bytes": BASE_COLLECTOR_BYTES,
        "metric_sha256": sha256(metric_path.read_bytes()),
        "base_authority": AUTHORITY,
        "current_github_run_id": current_run,
        "current_github_head_sha": current_head,
        "selection_index_sha256": expected_index,
        "authority_lock_sha256": authority_lock_expected,
        "variant": variant,
        "candidate_sha256": expected_candidate,
        "source_identity_locked": True,
        "source_executable_trust_counts": trust_counts,
        "all_required_raw_logs_uploaded": True,
        "all_required_raw_logs_from_execution": True,
        "raw_execution_exit_log_reconciliation": raw_reconciliation,
        "FA_inventory_below_configured_cap": True,
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
