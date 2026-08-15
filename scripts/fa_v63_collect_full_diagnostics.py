#!/usr/bin/env python3
"""v63 provenance adapter for the exact locked v42 full-inventory collector.

The mature optional-coded-header parser is imported only after its SHA/byte
lock passes.  Its stale authority is replaced with the official v62 winner
projection, and every emitted raw log, command, execution marker, exit,
diagnostic, warning, trust count, cap field, and current-run identity is then
reconciled.  Nonzero FA exits remain valid evidence and are not called clean.
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


BASE_COLLECTOR_SHA256 = "7de7bc92e4e2735c0d25706d70777ea67340d8afcf67434e43b051d5cb8c90c6"
BASE_COLLECTOR_BYTES = 12932
SCHEMA = "fa-v63-direct-bounded-highcap2000-metric-v1"
AUTHORITY = {
    "workflow_run_id": 31863434345,
    "head_sha": "3a503721ec899f6c1c92758eeb5facc49e0d59b4",
    "head_branch": "codex/fa-exclusive-focus-20260814",
    "job_id": 94960572977,
    "artifact_id": 9241529792,
    "artifact_name": "codex-fa-v61-fourier_pair-highcap2000-3a503721ec899f6c1c92758eeb5facc49e0d59b4",
    "artifact_size_in_bytes": 1684227,
    "artifact_digest": "sha256:799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333",
    "variant": "fourier_pair",
    "source_sha256": "1badac1451e11708114eb5438616063379558bcf0579dc82a01c2200b501d365",
    "source_bytes": 2812442,
    "source_lines": 62933,
    "declaration_count": 4416,
    "diagnostics_sha256": "31370de532745411bd9acdc258cf5d90c9d0bb5b08b23870b00b55300000f383",
    "fa_log_sha256": "8e27a4dcc8be79a091b8b1c2f61197fdb7c9e4d995f3e158327442969c1de60a",
    "patch_audit_sha256": "e104455b3242b45df254528e59f7e7400a86120a2c4db4b81305198c9a8316e5",
    "toolchain_pin_sha256": "8f54d5486b82a5fc11bc52199c89265b7e9e8eed5a3ff4131f86251894bcff07",
    "official_v62_ready_sha256": "8a7f65766baf2d20713b7cfa29c7edbb0a5cff0d670256adebfb57646ce2ab51",
}
TRUST_TOKENS = (
    "sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool",
)
STEMS = ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")
HEADER_RE = re.compile(
    r"^.+?\.lean:\d+:\d+:\s+(?:error|warning)(?:\([^()]+\))?:"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def required_env(name: str) -> str:
    value = os.environ.get(name)
    require(bool(value), f"missing environment variable: {name}")
    return str(value)


def main() -> int:
    bootstrap = argparse.ArgumentParser(add_help=False)
    bootstrap.add_argument("--base-collector", type=Path, required=True)
    bootstrap.add_argument("--base-collector-sha256", required=True)
    known, remaining = bootstrap.parse_known_args()
    require(known.base_collector_sha256 == BASE_COLLECTOR_SHA256,
            "configured base collector SHA differs from promoted lock")
    require(known.base_collector.is_file(), "locked base collector missing")
    payload = known.base_collector.read_bytes()
    require(sha256(payload) == BASE_COLLECTOR_SHA256,
            "locked base collector SHA mismatch")
    require(len(payload) == BASE_COLLECTOR_BYTES,
            "locked base collector byte mismatch")
    spec = importlib.util.spec_from_file_location(
        "fa_v63_locked_v42_collector", known.base_collector)
    require(spec is not None and spec.loader is not None,
            "cannot load locked base collector")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    require(hasattr(module, "main") and hasattr(module, "AUTHORITY"),
            "base collector API mismatch")
    require(tuple(module.STEMS) == STEMS, "base collector stem drift")
    require(tuple(module.TRUST_TOKENS) == TRUST_TOKENS,
            "base collector trust-six drift")

    variant = required_env("FA_V63_VARIANT")
    expected_candidate = required_env("FA_V63_EXPECTED_CANDIDATE_SHA256")
    expected_index = required_env("FA_V63_SELECTION_SHA256")
    actual_index = required_env("FA_V63_SELECTION_ACTUAL_SHA256")
    authority_expected = required_env("FA_V63_AUTHORITY_LOCK_SHA256")
    authority_actual = required_env("FA_V63_AUTHORITY_LOCK_ACTUAL_SHA256")
    current_run = required_env("GITHUB_RUN_ID")
    current_head = required_env("GITHUB_SHA")
    require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", variant) is not None,
            "invalid v63 variant")
    for label, value in (
        ("candidate", expected_candidate), ("expected selection", expected_index),
        ("actual selection", actual_index), ("expected authority", authority_expected),
        ("actual authority", authority_actual),
    ):
        require(re.fullmatch(r"[0-9a-f]{64}", value) is not None,
                f"invalid {label} SHA-256")
    require(expected_index == actual_index, "selection identity mismatch")
    require(authority_expected == authority_actual, "authority identity mismatch")
    require(re.fullmatch(r"[0-9]+", current_run) is not None,
            "invalid current GitHub run ID")
    require(re.fullmatch(r"[0-9a-f]{40}", current_head) is not None,
            "invalid current GitHub head SHA")

    module.SCHEMA = SCHEMA
    module.AUTHORITY = dict(AUTHORITY)
    os.environ.update({
        "FA_V42_VARIANT": variant,
        "FA_V42_EXPECTED_CANDIDATE_SHA256": expected_candidate,
        "FA_V42_INDEX_SHA256": expected_index,
        "FA_V42_INDEX_ACTUAL_SHA256": actual_index,
    })
    sys.argv = [sys.argv[0], *remaining]
    result = int(module.main())
    require(result == 0, "base collector returned nonzero")
    out: Path | None = None
    for position, value in enumerate(remaining):
        if value == "--out" and position + 1 < len(remaining):
            out = Path(remaining[position + 1])
            break
    require(out is not None, "collector --out argument missing")
    metric_path = out / "METRIC.json"
    require(metric_path.is_file(), "collector did not emit METRIC.json")
    metric = json.loads(metric_path.read_text(encoding="utf-8"))
    require(metric.get("schema") == SCHEMA, "v63 metric schema mismatch")
    require(metric.get("authority") == AUTHORITY, "metric authority mismatch")
    require(metric.get("github_run_id") == current_run, "metric current run mismatch")
    require(metric.get("github_head_sha") == current_head, "metric current head mismatch")
    require(metric.get("variant") == variant, "metric variant mismatch")
    require(metric.get("variant_index_expected_sha256") == expected_index
            and metric.get("variant_index_actual_sha256") == actual_index,
            "metric selection identity mismatch")
    require(metric.get("candidate_expected_sha256") == expected_candidate
            and metric.get("candidate_locked_sha256") == expected_candidate
            and metric.get("source_sha256") == expected_candidate,
            "metric candidate identity mismatch")
    require(metric.get("source_declaration_count") == 4416,
            "metric declaration count mismatch")
    require(metric.get("source_executable_trust_counts") ==
            {token: 0 for token in TRUST_TOKENS}
            and metric.get("source_executable_trust_six_zero") is True,
            "metric executable trust-six mismatch")
    require(metric.get("source_identity_locked") is True,
            "metric source identity is not locked")
    require(metric.get("all_required_raw_logs_uploaded") is True
            and metric.get("all_required_raw_logs_from_execution") is True
            and metric.get("raw_log_placeholders") == [],
            "metric raw-log provenance mismatch")
    require(metric.get("all_required_lean_executed") is True,
            "metric execution markers incomplete")
    require(metric.get("FA_compile_max_errors") == 2000,
            "metric FA maxErrors drift")
    require(metric.get("FA_error_cap_sentinel_present") is False,
            "metric cap sentinel present")
    require(metric.get("FA_inventory_below_configured_cap") is True
            and metric.get("FA_inventory_complete_by_header_evidence") is True,
            "metric full inventory is not complete below cap")
    require(metric.get("direct_lean_verified") is True,
            "metric does not attest direct Lean execution")

    exit_fields = {
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
                f"noncanonical raw exit: {stem}")
        raw_exit = int(exit_text)
        require(raw_exit == metric.get(exit_fields[stem]),
                f"raw exit/metric mismatch: {stem}")
        require(log_path.is_file(), f"missing raw log: {stem}")
        require(command_path.is_file() and bool(command_path.read_bytes()),
                f"missing raw command: {stem}")
        raw_reconciliation[stem] = {
            "executed_marker_exact_empty_file": True,
            "exit": raw_exit,
            "metric_exit_field": exit_fields[stem],
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
            and isinstance(synthetic, list), "collector inventory type mismatch")
    require(len(warnings) == metric.get("FA_warning_headers_captured"),
            "warning inventory does not reconcile")
    require(len(diagnostics) == metric.get("FA_error_headers_captured"),
            "diagnostic inventory does not reconcile")
    require(all(isinstance(row.get("raw_header"), str)
                and HEADER_RE.match(row["raw_header"]) for row in warnings + diagnostics),
            "plain/coded raw diagnostic header preservation failed")
    coded_errors = sum(row.get("diagnostic_code") is not None for row in diagnostics)
    coded_warnings = sum(row.get("diagnostic_code") is not None for row in warnings)
    require(synthetic == []
            and metric.get("synthetic_declaration_uses_sorry_warning_count") == 0
            and metric.get("synthetic_trust_clean") is True,
            "synthetic declaration-uses-sorry evidence present")
    attestation = {
        "schema": "fa-v63-collector-authority-attestation-v1",
        "status": "EXACT_CURRENT_PROVENANCE",
        "base_collector_sha256": BASE_COLLECTOR_SHA256,
        "base_collector_bytes": BASE_COLLECTOR_BYTES,
        "metric_sha256": sha256(metric_path.read_bytes()),
        "base_authority": AUTHORITY,
        "current_github_run_id": current_run,
        "current_github_head_sha": current_head,
        "selection_sha256": expected_index,
        "authority_lock_sha256": authority_expected,
        "variant": variant,
        "candidate_sha256": expected_candidate,
        "source_identity_locked": True,
        "source_executable_trust_counts": {token: 0 for token in TRUST_TOKENS},
        "all_required_raw_logs_uploaded": True,
        "all_required_raw_logs_from_execution": True,
        "raw_execution_exit_log_reconciliation": raw_reconciliation,
        "FA_maxErrors": 2000,
        "FA_error_cap_sentinel_present": False,
        "FA_inventory_complete_below_cap": True,
        "full_warning_count": len(warnings),
        "full_diagnostic_count": len(diagnostics),
        "coded_warning_header_count": coded_warnings,
        "coded_error_header_count": coded_errors,
        "synthetic_declaration_uses_sorry_warning_count": 0,
        "synthetic_trust_clean": True,
        "runtime_evidence_fallback_used": False,
        "stale_v42_authority_rejected": True,
        "clean_claimed": False,
    }
    (out / "COLLECTOR_AUTHORITY_ATTESTATION.json").write_text(
        json.dumps(attestation, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
