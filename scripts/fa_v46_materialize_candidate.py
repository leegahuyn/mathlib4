#!/usr/bin/env python3
"""Fail-closed materializer for the five SHA-locked FA v46 variants.

The selection index is the only variant policy input.  This wrapper verifies
the READY index, the locked v45 all_probes authority, and the v46 builder, then
invokes that builder in a temporary directory.  Candidate, audit, and evidence
are published only after exact identity and structural invariant checks pass.
A pending selection exits 2 and emits no candidate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


SCRIPT_PATH = Path(__file__).resolve()
ROOT = SCRIPT_PATH.parents[1] if SCRIPT_PATH.parent.name == "scripts" else SCRIPT_PATH.parents[2]
SCHEMA = "fa-v46-cumulative-selection-v1"
AUDIT_SCHEMA = "fa-v46-cumulative-static-audit-v1"
READY_STATUS = "READY"
EVIDENCE_SCHEMA = "fa-v46-five-variant-materialization-evidence-v1"
EXIT_PENDING = 2
VARIANT_ORDER = (
    "core",
    "w06_probe",
    "w27_probe",
    "w29_w34_probe",
    "all_probes",
)
TRUST_KEYS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)
AUTHORITY = {
    "run_id": 31728453514,
    "head_sha": "5ec44f3d343955f3124e7efecc048b648dccc5ab",
    "job_id": 94542617528,
    "artifact_id": 9192669673,
    "artifact_digest": "sha256:8f07a678145b62342aaa9cb94ebbce6c9f7cc1a45c400560918d42499e67f2f3",
    "variant": "all_probes",
    "source_path": "work/v45-results/run-31728453514/all_probes/Mock2_FunctionalAnalysis-candidate.lean",
    "source_sha256": "726f40d1dd03d32f03592adf4f6b02e3f7f52e7e1f71087ee53bdb83c4bb0caf",
    "source_bytes": 2788764,
    "source_lines": 62383,
    "declaration_count": 4416,
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def canonical(value: dict[str, Any]) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def is_sha(value: Any) -> bool:
    text = str(value)
    return len(text) == 64 and all(char in "0123456789abcdef" for char in text)


def authority_projection(value: dict[str, Any]) -> dict[str, Any]:
    return {key: value[key] for key in AUTHORITY}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--builder", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--allow-source-path-fallback", action="store_true")
    args = parser.parse_args()

    index_payload = args.index.read_bytes()
    index = json.loads(index_payload)
    if index.get("status") != READY_STATUS or b"PENDING" in index_payload:
        print("v46 selection is pending; refusing materialization", file=sys.stderr)
        return EXIT_PENDING
    require(index.get("schema") == SCHEMA, "selection schema mismatch")
    require(index.get("runtime_path") == "scripts/fa_v46_selection.json",
            "selection runtime path mismatch")
    require(index.get("target_branch") == "codex/fa-qym-cleanbuild-final-20260811-fast",
            "target branch mismatch")
    require(index.get("all_34_workers_terminal") is True,
            "worker queue is not terminal")
    require(index.get("source_moves") == [], "source moves are forbidden")
    require(index.get("direct_lean_verified") is False,
            "selection claims direct Lean verification")
    require(index.get("clean_build_claimed") is False,
            "selection claims a clean build")
    require(tuple(index.get("variant_order", [])) == VARIANT_ORDER,
            "five-variant order mismatch")
    require(
        index.get("direct_compile_chain") == [
            {"source": "Mock2", "max_errors": 1},
            {"source": "Mock2_Advanced", "max_errors": 1},
            {"source": "Mock2_FunctionalAnalysis", "max_errors": 2000},
        ],
        "direct compile chain mismatch",
    )

    variants = index.get("variants")
    require(isinstance(variants, list), "variant list missing")
    require(tuple(row.get("name") for row in variants) == VARIANT_ORDER,
            "variant list/order mismatch")
    require(args.variant in VARIANT_ORDER, f"unknown variant: {args.variant}")
    variant_rows = [row for row in variants if row.get("name") == args.variant]
    require(len(variant_rows) == 1, "requested variant absent or duplicated")
    variant = variant_rows[0]

    authority = authority_projection(index["authority"])
    require(authority == AUTHORITY, "selection authority mismatch")
    authority_path = ROOT / AUTHORITY["source_path"]
    require(authority_path.is_file(), f"authority source missing: {authority_path}")
    authority_payload = authority_path.read_bytes()
    require(sha256(authority_payload) == AUTHORITY["source_sha256"],
            "authority source SHA mismatch")
    require(len(authority_payload) == AUTHORITY["source_bytes"],
            "authority source byte mismatch")
    require(len(authority_payload.decode("utf-8").splitlines()) == AUTHORITY["source_lines"],
            "authority source line mismatch")

    builder_record = index.get("builder")
    require(isinstance(builder_record, dict), "builder lock missing")
    expected_builder_sha = builder_record.get("sha256")
    require(is_sha(expected_builder_sha), "builder SHA invalid")
    builder_payload = args.builder.read_bytes()
    require(sha256(builder_payload) == expected_builder_sha,
            "builder SHA mismatch")
    require(len(builder_payload) == int(builder_record["bytes"]),
            "builder byte mismatch")

    expected = variant.get("expected_candidate")
    require(isinstance(expected, dict) and is_sha(expected.get("sha256")),
            "expected candidate lock missing")
    index_sha = sha256(index_payload)

    with tempfile.TemporaryDirectory(prefix="fa-v46-materialize-") as temp_text:
        temp = Path(temp_text)
        candidate_path = temp / "candidate.lean"
        audit_path = temp / "audit.json"
        command = [
            sys.executable,
            str(args.builder),
            "--index",
            str(args.index),
            "--variant",
            args.variant,
            "--output",
            str(candidate_path),
            "--audit",
            str(audit_path),
        ]
        if args.allow_source_path_fallback:
            command.append("--allow-source-path-fallback")
        completed = subprocess.run(
            command,
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        require(completed.returncode == 0,
                f"locked v46 builder failed: {completed.stderr}")
        candidate_payload = candidate_path.read_bytes()
        audit_payload = audit_path.read_bytes()
        audit = json.loads(audit_payload)

    require(sha256(candidate_payload) == expected["sha256"],
            "candidate SHA mismatch")
    require(len(candidate_payload) == int(expected["bytes"]),
            "candidate byte mismatch")
    require(len(candidate_payload.decode("utf-8").splitlines()) == int(expected["lines"]),
            "candidate line mismatch")
    require(audit.get("schema") == AUDIT_SCHEMA, "audit schema mismatch")
    require(audit.get("status") == "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
            "audit status mismatch")
    require(audit.get("variant") == args.variant, "audit variant mismatch")
    require(audit.get("selection_index", {}).get("sha256") == index_sha,
            "audit selection SHA mismatch")
    require(authority_projection(audit["authority"]) == AUTHORITY,
            "audit authority mismatch")
    require(audit.get("candidate_sha256") == expected["sha256"],
            "audit candidate SHA mismatch")
    require(audit.get("candidate_bytes") == int(expected["bytes"]),
            "audit candidate byte mismatch")
    require(audit.get("candidate_lines") == int(expected["lines"]),
            "audit candidate line mismatch")
    require(audit.get("declaration_count") == 4416,
            "audit declaration count mismatch")
    for key in (
        "declaration_sequence_identical",
        "all_declaration_headers_byte_identical",
        "comments_identical",
        "attributes_identical",
        "diff_prefix_contamination_rejected",
    ):
        require(audit.get(key) is True, f"audit invariant failed: {key}")
    require(all(audit["trust_counts_before"].get(key) == 0 for key in TRUST_KEYS),
            "authority trust-six nonzero")
    require(all(audit["trust_counts_after"].get(key) == 0 for key in TRUST_KEYS),
            "candidate trust-six nonzero")
    require(audit.get("direct_lean_verified") is False,
            "static audit claims direct Lean")
    require(audit.get("lean_lake_git_github_network_invoked") is False,
            "builder reports prohibited invocation")
    require(audit.get("selected_worker_count") == variant["selected_worker_count"],
            "selected worker count mismatch")
    require(audit.get("selected_repair_count") == variant["selected_repair_count"],
            "selected repair count mismatch")
    require(audit.get("atomic_groups_checked") ==
            [group["id"] for group in variant.get("atomic_groups", [])],
            "atomic group audit mismatch")

    evidence = {
        "schema": EVIDENCE_SCHEMA,
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "variant": args.variant,
        "selection_index_sha256": index_sha,
        "selection_index_bytes": len(index_payload),
        "builder_sha256": sha256(builder_payload),
        "builder_bytes": len(builder_payload),
        "authority": AUTHORITY,
        "authority_source_sha256": sha256(authority_payload),
        "selected_worker_count": audit["selected_worker_count"],
        "selected_repair_count": audit["selected_repair_count"],
        "selected_owner_count": audit["selected_owner_count"],
        "candidate_sha256": sha256(candidate_payload),
        "candidate_bytes": len(candidate_payload),
        "candidate_lines": len(candidate_payload.decode("utf-8").splitlines()),
        "audit_sha256": sha256(audit_payload),
        "audit_bytes": len(audit_payload),
        "declaration_count": 4416,
        "headers_comments_attributes_preserved": True,
        "source_moves": [],
        "trust_counts_after": audit["trust_counts_after"],
        "source_path_fallback_enabled": args.allow_source_path_fallback,
        "direct_lean_verified": False,
        "lean_lake_git_github_network_invoked_by_materializer": False,
    }

    for destination in (args.output, args.audit, args.evidence):
        destination.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(candidate_payload)
    args.audit.write_bytes(audit_payload)
    evidence_payload = canonical(evidence)
    args.evidence.write_bytes(evidence_payload)
    print(evidence_payload.decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
