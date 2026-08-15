#!/usr/bin/env python3
"""Exact v65 per-lane final evidence gate.

The gate accepts both FA0 and nonzero FA evidence, but permits a clean claim
only for FA0 with a zero diagnostic inventory.  In every case it requires the
same exact flat 48-member artifact contract.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

import fa_v65_contract as contract


DIAGNOSTIC_HEADER_RE = re.compile(
    r"^.+?\.lean:\d+:\d+:\s+(?:error|warning)(?:\([^()]+\))?:.*$"
)
CAP_SENTINEL_RE = re.compile(
    r"(?i)(maximum number of errors|maxErrors|too many errors|error limit)"
)


def require(value: bool, message: str) -> None:
    if not value:
        raise AssertionError(message)


def ordinary(path: Path) -> None:
    require(path.is_file() and not path.is_symlink(), f"not an ordinary file: {path.name}")


def json_file(path: Path) -> Any:
    ordinary(path)
    return json.loads(path.read_bytes())


def exact_exit(path: Path) -> int:
    ordinary(path)
    payload = path.read_bytes()
    require(payload in {b"0\n", b"1\n"}, f"invalid exit bytes: {path.name}")
    return int(payload.strip())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--expected-selection-sha256", required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--variant", required=True, choices=contract.LANE_ORDER)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--gate-output", type=Path, required=True)
    args = parser.parse_args()

    ordinary(args.selection)
    selection_bytes = args.selection.read_bytes()
    require(contract.sha256(selection_bytes) == args.expected_selection_sha256, "selection SHA mismatch")
    selection = json.loads(selection_bytes)
    contract.validate_selection(selection, require_ready=True)
    contract.validate_runtime_support(args.repo_root, selection, require_ready=True)
    rows = [row for row in selection["variants"] if row["name"] == args.variant]
    require(len(rows) == 1, "variant selection mismatch")
    expected = rows[0]["expected_candidate"]

    require(args.out.is_dir() and not args.out.is_symlink(), "result output directory mismatch")
    out = args.out.resolve(strict=True)
    gate = args.gate_output.resolve(strict=False)
    require(gate.parent == out and gate.name == "FINAL_GATE.json" and not gate.exists(), "final gate output path mismatch")
    entries = list(out.iterdir())
    require(all(row.is_file() and not row.is_symlink() for row in entries), "result inventory contains non-file/link")
    expected_pre = sorted(set(contract.RESULT_ARTIFACT_MEMBERS) - {"FINAL_GATE.json"})
    require(sorted(row.name for row in entries) == expected_pre, "exact pre-gate 47-member inventory mismatch")

    ordinary(args.source)
    source = args.source.read_bytes()
    require(contract.sha256(source) == expected["sha256"] and len(source) == expected["bytes"], "repository candidate identity mismatch")
    require(len(source.decode().splitlines()) == expected["lines"], "repository candidate line mismatch")
    for name in ("Mock2_FunctionalAnalysis-candidate.lean", "Mock2_FunctionalAnalysis-observed.lean"):
        path = out / name
        ordinary(path)
        require(path.read_bytes() == source, f"candidate mirror mismatch: {name}")
    ordinary(out / "VARIANT_INDEX.json")
    require((out / "VARIANT_INDEX.json").read_bytes() == selection_bytes, "variant index byte mismatch")

    materialization = json_file(out / "MATERIALIZATION.json")
    patch = json_file(out / "PATCH_AUDIT.json")
    require(materialization == {
        "schema": "fa-v65-materialization-v1",
        "status": "READY_EXACT",
        "variant": args.variant,
        "selection_sha256": args.expected_selection_sha256,
        "candidate_sha256": expected["sha256"],
        "candidate_bytes": expected["bytes"],
        "candidate_lines": expected["lines"],
        "declaration_count": 4416,
        "composition_mode": "EXACT_FROM_OFFICIAL_V62_AUTHORITY_NONCUMULATIVE",
        "runtime_fallback_used": False,
        "pending_static_replay_used": False,
        "direct_lean_verified": False,
        "clean_claimed": False,
    }, "materialization exact evidence mismatch")
    require(json_file(out / "MATERIALIZATION.stdout.json") == materialization, "materialization stdout mirror mismatch")
    require(patch.get("schema") == "fa-v65-static-materialization-audit-v1" and patch.get("lane") == args.variant and patch.get("candidate") == expected and patch.get("runtime_fallback_used") is False, "patch audit mismatch")
    changed_indices = rows[0]["changed_declaration_indices"]
    require(patch.get("invariants") == {
        "declaration_count": 4416,
        "changed_declaration_indices": changed_indices,
        "headers_statements_order_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "outside_changed_owners_byte_identical": True,
        "trust_six_before": contract.TRUST_ZERO,
        "trust_six_after": contract.TRUST_ZERO,
        "global_maxHeartbeats_before": {"token_count": 8, "set_option_count": 8},
        "global_maxHeartbeats_after": {"token_count": 8, "set_option_count": 8},
        "changed_owner_maxHeartbeats": {
            str(index): {"token_count": 0, "set_option_count": 0}
            for index in changed_indices
        },
        "source_moves": 0,
        "imports_options_helpers_added": False,
        "body_only": True,
    }, "patch audit declaration/header/order/comment/attribute/trust/heartbeat mismatch")

    scaffold = json_file(out / "SCAFFOLD_GATE.json")
    require(scaffold == {
        "schema": "fa-v65-workflow-activation-gate-v1", "status": "READY",
        "variant": args.variant, "selection_sha256": args.expected_selection_sha256,
        "authority_lock_sha256": selection["authority"]["sha256"],
        "runtime_evidence_fallback_used": False,
    }, "scaffold gate mismatch")
    authority = json_file(out / "AUTHORITY_REPROOF.json")
    require(authority.get("schema") == "fa-v65-authority-reproof-v1" and authority.get("status") == "EXACT" and authority.get("selection_sha256") == args.expected_selection_sha256 and authority.get("runtime_evidence_fallback_used") is False, "authority reproof mismatch")
    require(authority.get("v62_source") == {key: contract.INPUT_LOCKS["v62_source"][key] for key in ("sha256", "bytes", "lines")}, "authority source reproof mismatch")
    require(authority.get("v62_authority_zip") == {"sha256": "799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333", "bytes": 1684227, "member_count": 48}, "authority ZIP reproof mismatch")
    full_member_locks = authority.get("v62_full_member_locks")
    require(isinstance(full_member_locks, dict) and len(full_member_locks) == 48 and all(isinstance(row, dict) and set(row) == {"sha256", "bytes"} and re.fullmatch(r"[0-9a-f]{64}", str(row["sha256"])) and isinstance(row["bytes"], int) and row["bytes"] >= 0 for row in full_member_locks.values()), "authority full48 member ledger mismatch")
    require(authority.get("base_authority_copies") == contract.BASE_AUTHORITY_COPIES and authority.get("runtime_manifest_locks") == contract.RUNTIME_MANIFEST_LOCKS and authority.get("independent_cross_audit") == contract.CROSS_AUDIT_LOCK, "authority copy/runtime/cross-audit ledger mismatch")
    require(json_file(out / "AUTHORITY_REPROOF.stdout.json") == authority, "authority reproof stdout mirror mismatch")
    observed_snapshot_locks = {}
    for name in ("V63_RUN.json", "V63_JOBS.json", "V63_ARTIFACT.json"):
        path = out / name
        ordinary(path)
        payload = path.read_bytes()
        observed_snapshot_locks[name] = {"sha256": contract.sha256(payload), "bytes": len(payload)}
    require(authority.get("v63_api_snapshots") == observed_snapshot_locks, "v63 API snapshot byte-lock mismatch")
    for row in contract.BASE_AUTHORITY_COPIES:
        path = out / row["result_member"]
        ordinary(path)
        payload = path.read_bytes()
        require(contract.sha256(payload) == row["sha256"] and len(payload) == row["bytes"], f"BASE copy mismatch: {row['result_member']}")
    recomposed, exact_patch = contract.compose_lane(
        args.variant,
        authority_source=(out / "BASE_Mock2_FunctionalAnalysis-candidate.lean").read_bytes(),
        repo_root=args.repo_root,
    )
    require(recomposed == source and patch == exact_patch, "final independent body-only recomposition/audit mismatch")

    commands = {
        "Mock2.command": "lake env lean -DmaxErrors=1 -DwarningAsError=false -o .lake/build/lib/lean/PrimalitySheafVerification/Mock2.olean -i .lake/build/lib/lean/PrimalitySheafVerification/Mock2.ilean PrimalitySheafVerification/Mock2.lean",
        "Mock2_Advanced.command": "lake env lean -DmaxErrors=1 -DwarningAsError=false -o .lake/build/lib/lean/PrimalitySheafVerification/Mock2_Advanced.olean -i .lake/build/lib/lean/PrimalitySheafVerification/Mock2_Advanced.ilean PrimalitySheafVerification/Mock2_Advanced.lean",
        "Mock2_FunctionalAnalysis.command": "lake env lean -DmaxErrors=2000 -DwarningAsError=false -o .lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.olean -i .lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.ilean PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
    }
    for name, expected_command in commands.items():
        path = out / name
        ordinary(path)
        require(path.read_bytes() == (expected_command + " \n").encode(), f"raw command mismatch: {name}")
    for name in ("Mock2.executed", "Mock2_Advanced.executed", "Mock2_FunctionalAnalysis.executed"):
        path = out / name
        ordinary(path)
        require(path.stat().st_size == 0, f"executed marker mismatch: {name}")
    for name in ("Mock2.log", "Mock2_Advanced.log", "Mock2_FunctionalAnalysis.log"):
        path = out / name
        ordinary(path)
        require(path.stat().st_size > 0, f"raw log empty: {name}")
    m2 = exact_exit(out / "Mock2.exit")
    m2a = exact_exit(out / "Mock2_Advanced.exit")
    fa = exact_exit(out / "Mock2_FunctionalAnalysis.exit")
    require((m2, m2a) == (0, 0), "M2/M2A must be clean before FA")

    metric = json_file(out / "METRIC.json")
    diagnostics = json_file(out / "FULL_DIAGNOSTICS.json")
    warnings = json_file(out / "FULL_WARNINGS.json")
    declaration_counts = json_file(out / "DIAGNOSTIC_DECLARATION_COUNTS.json")
    synthetic = json_file(out / "SYNTHETIC_SORRY_WARNINGS.json")
    require(isinstance(diagnostics, list) and isinstance(warnings, list) and isinstance(declaration_counts, list) and synthetic == [], "diagnostic/warning/declaration/synthetic shapes mismatch")
    require(metric.get("schema") == "fa-v63-direct-bounded-highcap2000-metric-v1" and metric.get("variant") == args.variant, "metric schema/variant mismatch")
    require(metric.get("candidate_expected_sha256") == expected["sha256"] and metric.get("candidate_locked_sha256") == expected["sha256"] and metric.get("source_sha256") == expected["sha256"], "metric identity mismatch")
    require(metric.get("source_bytes") == expected["bytes"] and metric.get("source_lines") == expected["lines"] and metric.get("source_declaration_count") == 4416 and metric.get("source_identity_locked") is True, "metric source structure mismatch")
    require(metric.get("Mock2_exit") == 0 and metric.get("Mock2_Advanced_exit") == 0 and metric.get("FA_exit") == fa, "metric exit reconciliation mismatch")
    require(metric.get("FA_compile_max_errors") == 2000 and metric.get("FA_error_cap_sentinel_present") is False and metric.get("FA_inventory_complete_by_header_evidence") is True and metric.get("FA_inventory_below_configured_cap") is True, "FA cap/inventory mismatch")
    require(metric.get("FA_error_headers_captured") == len(diagnostics) and metric.get("FA_warning_headers_captured") == len(warnings), "metric diagnostic multiset count mismatch")
    require(metric.get("synthetic_declaration_uses_sorry_warning_count") == 0 and metric.get("synthetic_trust_clean") is True and metric.get("source_executable_trust_counts") == contract.TRUST_ZERO and metric.get("source_executable_trust_six_zero") is True, "synthetic/trust metric mismatch")
    require(metric.get("all_required_lean_executed") is True and metric.get("all_required_raw_logs_uploaded") is True and metric.get("all_required_raw_logs_from_execution") is True and metric.get("raw_log_placeholders") == [] and metric.get("direct_lean_verified") is True, "raw direct-execution metric mismatch")
    fa_log_text = (out / "Mock2_FunctionalAnalysis.log").read_text(encoding="utf-8", errors="replace")
    require(CAP_SENTINEL_RE.search(fa_log_text) is None, "raw FA log contains error-cap sentinel")
    raw_fa_headers = [
        line for line in fa_log_text.splitlines()
        if DIAGNOSTIC_HEADER_RE.match(line)
    ]
    recorded_headers = [row.get("raw_header") for row in diagnostics + warnings]
    require(all(isinstance(value, str) and DIAGNOSTIC_HEADER_RE.match(value) for value in recorded_headers), "invalid plain/coded diagnostic header")
    require(collections.Counter(recorded_headers) == collections.Counter(raw_fa_headers), "raw diagnostic/warning header multiset mismatch")
    observed_counts = collections.Counter(
        (row.get("declaration_index"), row.get("declaration")) for row in diagnostics
    )
    expected_count_rows = [
        {"declaration_index": key[0], "declaration": key[1], "count": count}
        for key, count in sorted(
            observed_counts.items(),
            key=lambda item: (
                item[0][0] if item[0][0] is not None else -1,
                item[0][1] or "",
            ),
        )
    ]
    require(declaration_counts == expected_count_rows and metric.get("unique_declarations_with_errors") == len(observed_counts), "diagnostic declaration-owner inventory mismatch")
    collector = json_file(out / "COLLECTOR_AUTHORITY_ATTESTATION.json")
    require(collector.get("schema") == "fa-v63-collector-authority-attestation-v1" and collector.get("status") == "EXACT_CURRENT_PROVENANCE" and collector.get("variant") == args.variant and collector.get("candidate_sha256") == expected["sha256"] and collector.get("selection_sha256") == args.expected_selection_sha256 and collector.get("authority_lock_sha256") == selection["authority"]["sha256"] and collector.get("runtime_evidence_fallback_used") is False, "collector provenance mismatch")
    require(collector.get("metric_sha256") == contract.sha256((out / "METRIC.json").read_bytes()) and collector.get("full_diagnostic_count") == len(diagnostics) and collector.get("full_warning_count") == len(warnings), "collector metric/inventory hash mismatch")
    require(collector.get("all_required_raw_logs_uploaded") is True and collector.get("all_required_raw_logs_from_execution") is True and collector.get("FA_maxErrors") == 2000 and collector.get("FA_error_cap_sentinel_present") is False and collector.get("FA_inventory_complete_below_cap") is True, "collector raw/cap/inventory mismatch")
    require(collector.get("source_identity_locked") is True and collector.get("source_executable_trust_counts") == contract.TRUST_ZERO and collector.get("synthetic_declaration_uses_sorry_warning_count") == 0 and collector.get("synthetic_trust_clean") is True and collector.get("clean_claimed") is False, "collector source/trust/clean mismatch")
    toolchain = json_file(out / "TOOLCHAIN_PIN.json")
    require(toolchain == {
        "schema": "fa-v65-exact-toolchain-pin-v1",
        "status": "EXACT_FILE_PIN_AND_OBSERVED_VERSION",
        "content": contract.TOOLCHAIN,
        "terminal_lf": True,
        "bytes": 29,
        "sha256": contract.TOOLCHAIN_SHA256,
        "lean_version": contract.LEAN_VERSION,
    }, "toolchain pin/content/LF/observed-version mismatch")
    lean_version_path = out / "lean-version.txt"
    ordinary(lean_version_path)
    require(lean_version_path.read_bytes() == (contract.LEAN_VERSION + "\n").encode(), "observed Lean version byte mirror mismatch")
    for name in ("candidate.sha256", "candidate.before.sha256", "candidate.before-fa.sha256", "candidate.after.sha256"):
        path = out / name
        ordinary(path)
        require(path.read_text().strip() == expected["sha256"], f"candidate SHA mirror mismatch: {name}")

    require((fa == 0) == (len(diagnostics) == 0), "FA exit/error inventory semantic mismatch")
    clean = fa == 0
    require(metric.get("semantic_clean") is clean, "metric semantic-clean mismatch")
    outcomes = {
        key: os.environ.get(f"FA_V65_{key.upper()}_OUTCOME")
        for key in ("preflight", "authority", "materialize", "install", "compile", "collect")
    }
    require(outcomes == {key: "success" for key in outcomes}, "workflow step outcome mirror mismatch")
    wrapper_rc = os.environ.get("FA_V65_WRAPPER_RC")
    captured_fa_exit = os.environ.get("FA_V65_CAPTURED_FA_EXIT")
    require(wrapper_rc == "0", "compile wrapper infrastructure exit mismatch")
    require(captured_fa_exit in {"0", "1"} and int(captured_fa_exit) == fa, "captured/raw FA exit mirror mismatch")
    status = "PASS_DIRECT_FA0_EXACT" if clean else "DIRECT_FA_NONZERO_EVIDENCE_COMPLETE"
    result = {
        "schema": "fa-v65-direct-final-gate-v1",
        "status": status,
        "variant": args.variant,
        "selection_sha256": args.expected_selection_sha256,
        "candidate": expected,
        "Mock2_exit": 0,
        "Mock2_Advanced_exit": 0,
        "FA_exit": fa,
        "FA_exit_mirror": fa,
        "FA_error_count": len(diagnostics),
        "FA_warning_count": len(warnings),
        "FA_maxErrors": 2000,
        "error_cap_sentinel_present": False,
        "inventory_complete": True,
        "synthetic_sorry_warning_count": 0,
        "trust_six_zero": True,
        "declaration_count": 4416,
        "headers_statements_order_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "global_maxHeartbeats": {"token_count": 8, "set_option_count": 8},
        "changed_owner_maxHeartbeats": {
            str(index): {"token_count": 0, "set_option_count": 0}
            for index in changed_indices
        },
        "source_moves": 0,
        "toolchain": toolchain,
        "lean_version_file_sha256": contract.sha256(lean_version_path.read_bytes()),
        "metric_sha256": contract.sha256((out / "METRIC.json").read_bytes()),
        "full_diagnostics_sha256": contract.sha256((out / "FULL_DIAGNOSTICS.json").read_bytes()),
        "full_warnings_sha256": contract.sha256((out / "FULL_WARNINGS.json").read_bytes()),
        "diagnostic_declaration_counts_sha256": contract.sha256((out / "DIAGNOSTIC_DECLARATION_COUNTS.json").read_bytes()),
        "patch_audit_sha256": contract.sha256((out / "PATCH_AUDIT.json").read_bytes()),
        "materialization_sha256": contract.sha256((out / "MATERIALIZATION.json").read_bytes()),
        "collector_attestation_sha256": contract.sha256((out / "COLLECTOR_AUTHORITY_ATTESTATION.json").read_bytes()),
        "authority_reproof_sha256": contract.sha256((out / "AUTHORITY_REPROOF.json").read_bytes()),
        "v63_api_snapshots": observed_snapshot_locks,
        "result_artifact_member_count": 48,
        "result_artifact_member_names": contract.RESULT_ARTIFACT_MEMBERS,
        "result_artifact_exact_flat_inventory_enforced": True,
        "all_required_raw_commands_logs_exits_markers_reconciled": True,
        "raw_diagnostic_warning_multiset_reconciled": True,
        "runtime_evidence_fallback_used": False,
        "workflow_step_outcomes": outcomes,
        "compile_wrapper_exit": 0,
        "captured_FA_exit": int(captured_fa_exit),
        "clean_permitted": clean,
        "clean_claimed": clean,
    }
    args.gate_output.write_bytes(contract.canonical_json(result))
    require(sorted(row.name for row in out.iterdir()) == sorted(contract.RESULT_ARTIFACT_MEMBERS), "post-gate exact 48-member inventory mismatch")
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL-CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(86)
