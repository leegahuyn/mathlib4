#!/usr/bin/env python3
"""Bind live v63 provenance to the exact v62 source and promoted v65 package."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import fa_v65_contract as contract


EXPECTED_V63_JOBS = [
    "fail-closed-pending-selection-gate", "direct-core", "direct-f3930",
    "direct-f3933_preferred", "direct-f3933_fallback",
    "direct-f3930_f3933_preferred", "direct-f3930_f3933_fallback",
    "direct-w4017_p", "direct-w4017_pz", "direct-w4017_pw", "direct-w4017_full",
    "direct-combined_best",
]


def require(value: bool, message: str) -> None:
    if not value:
        raise AssertionError(message)


def ordinary(path: Path) -> bytes:
    require(path.is_file() and not path.is_symlink(), f"not an ordinary input: {path}")
    return path.read_bytes()


def load_json(path: Path) -> Any:
    return json.loads(ordinary(path))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--expected-selection-sha256", required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--v62-source", type=Path, required=True)
    parser.add_argument("--v62-reproof", type=Path, required=True)
    parser.add_argument("--v63-run-api", type=Path, required=True)
    parser.add_argument("--v63-jobs-api", type=Path, required=True)
    parser.add_argument("--v63-artifact-api", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    selection_bytes = ordinary(args.selection)
    require(contract.sha256(selection_bytes) == args.expected_selection_sha256, "selection SHA mismatch")
    selection = json.loads(selection_bytes)
    contract.validate_selection(selection, require_ready=True)
    support = contract.validate_runtime_support(args.repo_root, selection, require_ready=True)
    source = ordinary(args.v62_source)
    contract._validate_authority_source(source)

    v62 = load_json(args.v62_reproof)
    require(v62.get("schema") == "fa-v63-v62-winner-authority-reproof-v1" and v62.get("status") == "EXACT", "v62 authority reproof schema/status mismatch")
    require(v62.get("artifact_zip") == {"sha256": "799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333", "bytes": 1684227}, "v62 authority ZIP mismatch")
    require(v62.get("flat_member_count") == 48 and v62.get("all_member_lock_count") == 48 and v62.get("all_member_locks_derived_only_after_exact_zip_reproof") is True, "v62 authority full ledger mismatch")
    require(v62.get("source_sha256") == contract.INPUT_LOCKS["v62_source"]["sha256"] and v62.get("source_bytes") == 2812442 and v62.get("source_lines") == 62933, "v62 authority source mismatch")
    require(v62.get("repository_source_fallback_used") is False and v62.get("runtime_evidence_fallback_used") is False and v62.get("embedded_artifact_authority_trusted_without_reproof") is False, "v62 authority fallback mismatch")

    run = load_json(args.v63_run_api)
    require(run.get("id") == 31871876992 and run.get("head_sha") == "336899ee618c4db5e88cf5c41b3a2195c3d61ba3" and run.get("head_branch") == "codex/fa-exclusive-focus-20260814", "v63 run identity mismatch")
    require(run.get("event") == "push" and run.get("run_attempt") == 1 and run.get("status") == "completed" and run.get("conclusion") == "failure", "v63 run terminal mismatch")
    jobs = load_json(args.v63_jobs_api)
    rows = jobs.get("jobs")
    require(isinstance(rows, list) and len(rows) == 12 and sorted(row.get("name") for row in rows) == sorted(EXPECTED_V63_JOBS), "v63 job cardinality/names mismatch")
    require(all(row.get("status") == "completed" for row in rows), "v63 job nonterminal")
    gate_rows = [row for row in rows if row.get("name") == "fail-closed-pending-selection-gate"]
    direct_rows = [row for row in rows if str(row.get("name", "")).startswith("direct-")]
    require(len(gate_rows) == 1 and gate_rows[0].get("conclusion") == "success" and len(direct_rows) == 11 and all(row.get("conclusion") == "failure" for row in direct_rows), "v63 job conclusion mirror mismatch")
    artifact = load_json(args.v63_artifact_api)
    require(artifact.get("id") == 9244032070 and artifact.get("name") == "codex-fa-v63-w4017_full-highcap2000-336899ee618c4db5e88cf5c41b3a2195c3d61ba3", "v63 winner artifact identity mismatch")
    require(artifact.get("digest") == "sha256:51a74664e6bfa180b97ba97ddd8e3f1226c57125429ac90a09e3e9d3d1fdb7b5" and artifact.get("size_in_bytes") == 1687279 and artifact.get("expired") is False, "v63 winner artifact lock mismatch")
    workflow_run = artifact.get("workflow_run", {})
    require(workflow_run.get("id") == 31871876992 and workflow_run.get("head_sha") == "336899ee618c4db5e88cf5c41b3a2195c3d61ba3" and workflow_run.get("head_branch") == "codex/fa-exclusive-focus-20260814", "v63 artifact workflow identity mismatch")

    require(args.out.is_dir() and not args.out.is_symlink(), "authority output directory mismatch")
    out = args.out.resolve(strict=True)
    for row in contract.BASE_AUTHORITY_COPIES:
        path = out / row["result_member"]
        payload = ordinary(path)
        require(contract.sha256(payload) == row["sha256"] and len(payload) == row["bytes"], f"base authority copy mismatch: {path.name}")
    for expected_name, input_path in (
        ("V63_RUN.json", args.v63_run_api), ("V63_JOBS.json", args.v63_jobs_api),
        ("V63_ARTIFACT.json", args.v63_artifact_api),
    ):
        require(input_path.resolve(strict=True) == (out / expected_name).resolve(strict=True), f"v63 snapshot path mismatch: {expected_name}")

    snapshot_locks = {
        expected_name: {
            "sha256": contract.sha256(ordinary(input_path)),
            "bytes": len(ordinary(input_path)),
        }
        for expected_name, input_path in (
            ("V63_RUN.json", args.v63_run_api),
            ("V63_JOBS.json", args.v63_jobs_api),
            ("V63_ARTIFACT.json", args.v63_artifact_api),
        )
    }

    result = {
        "schema": "fa-v65-authority-reproof-v1",
        "status": "EXACT",
        "selection_sha256": args.expected_selection_sha256,
        "authority_lock_sha256": selection["authority"]["sha256"],
        "dependency_graph_sha256": selection["dependency_graph"]["sha256"],
        "v62_source": {key: contract.INPUT_LOCKS["v62_source"][key] for key in ("sha256", "bytes", "lines")},
        "v62_authority_zip": {"sha256": "799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333", "bytes": 1684227, "member_count": 48},
        "v62_full_member_locks": v62["all_member_locks"],
        "v62_reproof_sha256": contract.sha256(ordinary(args.v62_reproof)),
        "base_authority_copies": contract.BASE_AUTHORITY_COPIES,
        "v63_run": {"id": 31871876992, "head_sha": "336899ee618c4db5e88cf5c41b3a2195c3d61ba3", "branch": "codex/fa-exclusive-focus-20260814", "job_count": 12, "direct_job_count": 11},
        "v63_winner_artifact": {"id": 9244032070, "digest": artifact["digest"], "size_in_bytes": 1687279, "expired": False},
        "v63_api_snapshots": snapshot_locks,
        "runtime_support": support,
        "runtime_manifest_locks": contract.RUNTIME_MANIFEST_LOCKS,
        "independent_cross_audit": contract.CROSS_AUDIT_LOCK,
        "runtime_evidence_fallback_used": False,
        "direct_lean_invoked_by_reproof": False,
        "clean_claimed": False,
    }
    target = out / "AUTHORITY_REPROOF.json"
    require(not target.exists() and not target.is_symlink(), "authority reproof output must be absent")
    target.write_bytes(contract.canonical_json(result))
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL-CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(86)
