#!/usr/bin/env python3
"""Fail-closed v63 final gate that mirrors the exact direct FA exit.

The gate reopens the READY contract and reconciles materialization, authority
reproof, raw commands/markers/logs/exits, collector inventories, trust evidence,
the cap/full-inventory fields, and the candidate source.  A valid FA nonzero is
preserved as evidence and returned unchanged; it is never reported as clean.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

from fa_v63_contract import (
    BASE_AUTHORITY_COPIES,
    ContractError,
    PendingInput,
    RESULT_ARTIFACT_MEMBERS,
    TRUST_TOKENS,
    canonical_authority_projection,
    load_ready_contract,
    require,
    sha256,
)


STEMS = ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")


def read_json(path: Path, label: str) -> dict[str, Any]:
    require(path.is_file(), f"missing {label}: {path}")
    try:
        value = json.loads(path.read_bytes())
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"invalid {label} JSON: {exc}") from exc
    require(isinstance(value, dict), f"{label} root is not object")
    return value


def read_list(path: Path, label: str) -> list[Any]:
    require(path.is_file(), f"missing {label}: {path}")
    try:
        value = json.loads(path.read_bytes())
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"invalid {label} JSON: {exc}") from exc
    require(isinstance(value, list), f"{label} root is not array")
    return value


def read_exit(path: Path, label: str) -> int:
    require(path.is_file(), f"missing raw exit: {label}")
    value = path.read_text(encoding="utf-8")
    require(re.fullmatch(r"[0-9]+\n", value) is not None,
            f"noncanonical raw exit: {label}")
    result = int(value)
    require(0 <= result <= 255, f"raw exit out of range: {label}")
    return result


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)
            + "\n").encode("utf-8")


def exclusive_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
    except BaseException:
        try:
            path.unlink()
        except OSError:
            pass
        raise


def validate_pre_gate_inventory(out: Path) -> list[str]:
    """Require the exact 47 files present while FINAL_GATE.json is unwritten."""
    require(out.is_dir(), "result artifact directory missing")
    current_entries = list(out.iterdir())
    require(all(path.is_file() and not path.is_symlink()
                for path in current_entries),
            "result artifact contains directory or symbolic link")
    pre_gate_members = sorted(path.name for path in current_entries)
    expected_pre_gate_members = sorted(
        set(RESULT_ARTIFACT_MEMBERS) - {"FINAL_GATE.json"})
    require(pre_gate_members == expected_pre_gate_members,
            "pre-gate result artifact exact member inventory mismatch")
    return pre_gate_members


def build(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    contract = load_ready_contract(
        selection_path=args.selection,
        authority_lock_path=args.authority_lock,
        manifest_schema_path=args.manifest_schema,
        expected_selection_sha256=args.expected_selection_sha256,
        repo_root=args.repo_root,
    )
    rows = [row for row in contract["selection"]["variants"]
            if row["name"] == args.variant]
    require(len(rows) == 1, "final-gate variant not selected exactly once")
    row = rows[0]
    expected = row["expected_candidate"]
    require(args.expected_candidate_sha256 == expected["sha256"],
            "configured candidate SHA differs from selection")
    require(args.source.is_file(), "candidate source missing")
    source_payload = args.source.read_bytes()
    require(sha256(source_payload) == expected["sha256"],
            "final candidate source SHA mismatch")
    require(len(source_payload) == expected["bytes"],
            "final candidate source byte mismatch")
    try:
        source_text = source_payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ContractError("final candidate source is not UTF-8") from exc
    require(len(source_text.splitlines()) == expected["lines"],
            "final candidate source line mismatch")
    out = args.out
    require(out.is_dir(), "result artifact directory missing")
    require(args.gate_output.resolve() == (out / "FINAL_GATE.json").resolve(),
            "final-gate output is not exact result member path")
    require(args.authority_reproof.resolve() ==
            (out / "AUTHORITY_REPROOF.json").resolve(),
            "authority reproof is not exact result member path")
    metric_path = out / "METRIC.json"
    patch_path = out / "PATCH_AUDIT.json"
    materialization_path = out / "MATERIALIZATION.json"
    collector_path = out / "COLLECTOR_AUTHORITY_ATTESTATION.json"
    metric = read_json(metric_path, "metric")
    patch = read_json(patch_path, "patch audit")
    materialization = read_json(materialization_path, "materialization")
    collector = read_json(collector_path, "collector attestation")
    authority_reproof = read_json(args.authority_reproof, "authority reproof")
    diagnostics = read_list(out / "FULL_DIAGNOSTICS.json", "full diagnostics")
    warnings = read_list(out / "FULL_WARNINGS.json", "full warnings")
    synthetic = read_list(out / "SYNTHETIC_SORRY_WARNINGS.json", "synthetic warnings")
    authority_projection = canonical_authority_projection(contract["authority"])
    require(authority_reproof.get("schema") ==
            "fa-v63-v62-winner-authority-reproof-v1"
            and authority_reproof.get("status") == "EXACT"
            and authority_reproof.get("authority") == authority_projection
            and authority_reproof.get("runtime_evidence_fallback_used") is False,
            "authority reproof mismatch")
    authority = contract["authority"]
    artifact_lock = authority["artifact"]
    require(authority_reproof.get("artifact_zip") == {
                "sha256": artifact_lock["zip_sha256"],
                "bytes": artifact_lock["zip_bytes"],
            }
            and authority_reproof.get("flat_member_count") == 48
            and authority_reproof.get("flat_member_names") ==
            authority["expected_flat_members"],
            "authority reproof ZIP/member inventory mismatch")
    declared_locks = authority["member_locks"]
    require(authority_reproof.get("declared_member_lock_count") ==
            len(declared_locks)
            and authority_reproof.get("declared_member_locks") == declared_locks,
            "authority reproof declared member locks mismatch")
    all_member_locks = authority_reproof.get("all_member_locks")
    require(isinstance(all_member_locks, dict)
            and authority_reproof.get("all_member_lock_count") == 48
            and authority_reproof.get(
                "all_member_locks_derived_only_after_exact_zip_reproof") is True
            and sorted(all_member_locks) == authority["expected_flat_members"],
            "authority reproof full 48-member hash ledger mismatch")
    for member_name, member_lock in all_member_locks.items():
        require(isinstance(member_lock, dict)
                and set(member_lock) == {"sha256", "bytes"}
                and isinstance(member_lock["sha256"], str)
                and re.fullmatch(r"[0-9a-f]{64}", member_lock["sha256"])
                is not None
                and isinstance(member_lock["bytes"], int)
                and member_lock["bytes"] >= 0,
                f"invalid authority full-member lock: {member_name}")
    for member_name, declared_lock in declared_locks.items():
        require(all_member_locks[member_name] == declared_lock,
                f"authority full/declaration lock mismatch: {member_name}")
    copy_locks = contract["selection"]["artifact_contract"][
        "v62_authority_zip"]["copies"]
    require(authority_reproof.get("base_authority_copies") == copy_locks,
            "authority reproof BASE copy ledger mismatch")
    require([(row["result_member"], row["authority_member"])
             for row in copy_locks] == list(BASE_AUTHORITY_COPIES),
            "authority BASE copy mapping mismatch")
    base_copy_hashes: dict[str, dict[str, Any]] = {}
    for row_lock in copy_locks:
        require(all_member_locks[row_lock["authority_member"]] == {
                    "sha256": row_lock["sha256"], "bytes": row_lock["bytes"]},
                f"authority full/BASE lock mismatch: {row_lock['result_member']}")
        path = out / row_lock["result_member"]
        require(path.is_file() and not path.is_symlink(),
                f"missing or linked authority BASE copy: {row_lock['result_member']}")
        payload = path.read_bytes()
        require(sha256(payload) == row_lock["sha256"]
                and len(payload) == row_lock["bytes"],
                f"authority BASE copy lock mismatch: {row_lock['result_member']}")
        base_copy_hashes[row_lock["result_member"]] = {
            "authority_member": row_lock["authority_member"],
            "sha256": row_lock["sha256"],
            "bytes": row_lock["bytes"],
        }
    for observed, label in ((patch, "patch"), (materialization, "materialization")):
        require(observed.get("variant") == args.variant, f"{label} variant mismatch")
        require(observed.get("selection_sha256") == contract["selection_sha256"],
                f"{label} selection mismatch")
        require(observed.get("candidate_sha256") == expected["sha256"]
                and observed.get("candidate_bytes") == expected["bytes"]
                and observed.get("candidate_lines") == expected["lines"],
                f"{label} candidate mismatch")
        require(observed.get("selected_repair_ids") == row["selected_repair_ids"],
                f"{label} selected repair mismatch")
        require(observed.get("source_moves") == [], f"{label} source move present")
        require(observed.get("global_maxHeartbeats_before") ==
                {"token_count": 8, "set_option_count": 8}
                and observed.get("global_maxHeartbeats_after") ==
                {"token_count": 8, "set_option_count": 8},
                f"{label} heartbeat mismatch")
        require(observed.get("trust_counts_before") ==
                {token: 0 for token in TRUST_TOKENS}
                and observed.get("trust_counts_after") ==
                {token: 0 for token in TRUST_TOKENS},
                f"{label} trust-six mismatch")
        require(observed.get("runtime_evidence_fallback_used") is False,
                f"{label} runtime fallback used")
        require(observed.get("direct_lean_verified") is False,
                f"{label} improperly claims direct Lean")
    require(materialization.get("patch_audit_sha256") == sha256(patch_path.read_bytes()),
            "materialization/patch audit hash mismatch")

    require(metric.get("schema") == "fa-v63-direct-bounded-highcap2000-metric-v1",
            "metric schema mismatch")
    require(metric.get("variant") == args.variant, "metric variant mismatch")
    require(metric.get("candidate_expected_sha256") == expected["sha256"]
            and metric.get("candidate_locked_sha256") == expected["sha256"]
            and metric.get("source_sha256") == expected["sha256"],
            "metric candidate mismatch")
    require(metric.get("source_declaration_count") == 4416,
            "metric declaration count mismatch")
    require(metric.get("source_executable_trust_counts") ==
            {token: 0 for token in TRUST_TOKENS}
            and metric.get("source_executable_trust_six_zero") is True,
            "metric trust-six mismatch")
    require(metric.get("synthetic_declaration_uses_sorry_warning_count") == 0
            and metric.get("synthetic_trust_clean") is True and synthetic == [],
            "synthetic trust evidence mismatch")
    require(metric.get("FA_compile_max_errors") == 2000,
            "metric maxErrors mismatch")
    require(metric.get("FA_error_cap_sentinel_present") is False,
            "metric cap sentinel present")
    require(metric.get("FA_inventory_below_configured_cap") is True
            and metric.get("FA_inventory_complete_by_header_evidence") is True,
            "metric full inventory incomplete")
    require(metric.get("FA_error_headers_captured") == len(diagnostics)
            and metric.get("FA_warning_headers_captured") == len(warnings),
            "metric full inventory counts do not reconcile")
    require(metric.get("all_required_lean_executed") is True
            and metric.get("all_required_raw_logs_uploaded") is True
            and metric.get("all_required_raw_logs_from_execution") is True
            and metric.get("raw_log_placeholders") == [],
            "metric raw execution provenance mismatch")
    require(collector.get("schema") ==
            "fa-v63-collector-authority-attestation-v1"
            and collector.get("status") == "EXACT_CURRENT_PROVENANCE"
            and collector.get("variant") == args.variant
            and collector.get("candidate_sha256") == expected["sha256"]
            and collector.get("selection_sha256") == contract["selection_sha256"]
            and collector.get("FA_maxErrors") == 2000
            and collector.get("FA_error_cap_sentinel_present") is False
            and collector.get("FA_inventory_complete_below_cap") is True
            and collector.get("runtime_evidence_fallback_used") is False,
            "collector attestation mismatch")
    require(collector.get("metric_sha256") == sha256(metric_path.read_bytes()),
            "collector/metric hash mismatch")
    require(collector.get("full_diagnostic_count") == len(diagnostics)
            and collector.get("full_warning_count") == len(warnings),
            "collector full inventory count mismatch")

    exits: dict[str, int] = {}
    metric_exit_fields = {
        "Mock2": "Mock2_exit", "Mock2_Advanced": "Mock2_Advanced_exit",
        "Mock2_FunctionalAnalysis": "FA_exit",
    }
    for stem in STEMS:
        executed = out / f"{stem}.executed"
        command = out / f"{stem}.command"
        log = out / f"{stem}.log"
        require(executed.is_file() and executed.read_bytes() == b"",
                f"invalid executed marker: {stem}")
        require(command.is_file() and bool(command.read_bytes()),
                f"missing command: {stem}")
        require(log.is_file(), f"missing raw log: {stem}")
        exits[stem] = read_exit(out / f"{stem}.exit", stem)
        require(exits[stem] == metric.get(metric_exit_fields[stem]),
                f"raw exit/metric mismatch: {stem}")
    require(exits["Mock2"] == 0, "Mock2 direct compile is nonzero")
    require(exits["Mock2_Advanced"] == 0,
            "Mock2_Advanced direct compile is nonzero")
    fa_exit = exits["Mock2_FunctionalAnalysis"]
    require((fa_exit == 0 and len(diagnostics) == 0)
            or (fa_exit != 0 and len(diagnostics) > 0),
            "FA exit/error inventory semantic mismatch")
    for name in ("candidate.before.sha256", "candidate.before-fa.sha256",
                 "candidate.after.sha256", "candidate.sha256"):
        path = out / name
        require(path.is_file()
                and path.read_text(encoding="utf-8") == expected["sha256"] + "\n",
                f"candidate identity file mismatch: {name}")
    clean = fa_exit == 0 and len(diagnostics) == 0
    require(metric.get("semantic_clean") is clean,
            "metric semantic-clean value mismatch")
    validate_pre_gate_inventory(out)
    gate = {
        "schema": "fa-v63-direct-final-gate-v1",
        "status": ("PASS_DIRECT_FA0_EXACT" if clean
                   else "DIRECT_FA_NONZERO_EVIDENCE_COMPLETE"),
        "variant": args.variant,
        "selection_sha256": contract["selection_sha256"],
        "authority": authority_projection,
        "candidate": expected,
        "selected_repair_ids": row["selected_repair_ids"],
        "Mock2_exit": exits["Mock2"],
        "Mock2_Advanced_exit": exits["Mock2_Advanced"],
        "Mock2_FunctionalAnalysis_exit": fa_exit,
        "exit_code_to_mirror": fa_exit,
        "FA_maxErrors": 2000,
        "FA_error_count": len(diagnostics),
        "FA_warning_count": len(warnings),
        "FA_error_cap_sentinel_present": False,
        "FA_inventory_complete_below_cap": True,
        "synthetic_declaration_uses_sorry_warning_count": 0,
        "trust_six_zero": True,
        "declaration_count": 4416,
        "source_moves": 0,
        "global_maxHeartbeats": {"token_count": 8, "set_option_count": 8},
        "metric_sha256": sha256(metric_path.read_bytes()),
        "full_diagnostics_sha256": sha256((out / "FULL_DIAGNOSTICS.json").read_bytes()),
        "full_warnings_sha256": sha256((out / "FULL_WARNINGS.json").read_bytes()),
        "patch_audit_sha256": sha256(patch_path.read_bytes()),
        "materialization_sha256": sha256(materialization_path.read_bytes()),
        "collector_attestation_sha256": sha256(collector_path.read_bytes()),
        "authority_reproof_sha256": sha256(args.authority_reproof.read_bytes()),
        "base_authority_copies": base_copy_hashes,
        "result_artifact_member_count": len(RESULT_ARTIFACT_MEMBERS),
        "result_artifact_member_names": list(RESULT_ARTIFACT_MEMBERS),
        "result_artifact_exact_flat_inventory_enforced": True,
        "all_required_raw_commands_logs_exits_markers_reconciled": True,
        "runtime_evidence_fallback_used": False,
        "clean_claim_permitted": clean,
        "clean_claimed": clean,
    }
    return gate, fa_exit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--authority-lock", type=Path, required=True)
    parser.add_argument("--manifest-schema", type=Path, required=True)
    parser.add_argument("--expected-selection-sha256", required=True)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--authority-reproof", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--expected-candidate-sha256", required=True)
    parser.add_argument("--gate-output", type=Path, required=True)
    args = parser.parse_args()
    try:
        require(not args.gate_output.exists(), "final-gate output already exists")
        gate, mirror_exit = build(args)
    except PendingInput as exc:
        print(f"PENDING: {exc}", file=sys.stderr)
        return 2
    except (ContractError, OSError) as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        if not args.gate_output.exists():
            failure = {
                "schema": "fa-v63-direct-final-gate-v1",
                "status": "FAIL_CLOSED_CONTRACT_VIOLATION",
                "variant": args.variant,
                "exit_code_to_mirror": 86,
                "reason": str(exc),
                "runtime_evidence_fallback_used": False,
                "clean_claim_permitted": False,
                "clean_claimed": False,
            }
            try:
                exclusive_write(args.gate_output, json_bytes(failure))
            except OSError:
                pass
        return 86
    exclusive_write(args.gate_output, json_bytes(gate))
    print(json.dumps(gate, ensure_ascii=False, indent=2, sort_keys=True))
    return mirror_exit


if __name__ == "__main__":
    raise SystemExit(main())
