#!/usr/bin/env python3
"""Validate a v65 selection and emit the exact ten-job matrix."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import fa_v65_contract as contract


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", required=True)
    parser.add_argument("--expected-selection-sha256", required=True)
    parser.add_argument("--repo-root", required=True)
    parser.add_argument("--allow-pending", action="store_true")
    parser.add_argument("--emit", choices=("matrix", "registry", "summary"), required=True)
    args = parser.parse_args()
    path = Path(args.selection)
    if path.is_symlink() or not path.is_file():
        raise AssertionError("selection is not an ordinary file")
    payload = path.read_bytes()
    if contract.sha256(payload) != args.expected_selection_sha256:
        raise AssertionError("selection SHA mismatch")
    selection = json.loads(payload)
    ready = selection.get("status") == "READY"
    if not ready and not args.allow_pending:
        print("v65 selection remains PENDING; matrix emission forbidden", file=sys.stderr)
        return contract.PENDING_EXIT
    contract.validate_selection(selection, require_ready=ready)
    support = contract.validate_runtime_support(Path(args.repo_root), selection, require_ready=ready)
    registry = contract.lane_registry()
    if args.emit == "matrix":
        value = {"include": [{"variant": lane} for lane in contract.LANE_ORDER]}
    elif args.emit == "registry":
        value = registry
    else:
        value = {
            "schema": "fa-v65-selection-validation-v1",
            "status": "PASS_STATIC_PENDING" if not ready else "PASS_READY",
            "lane_count": 10,
            "variant_order": contract.LANE_ORDER,
            "distinct_candidate_outputs": True,
            "each_lane_requires_independent_full_compile": True,
            "direct_chain": ["Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis_FA2000"],
            "direct_lean_verified": False,
            "clean_claimed": False,
            "runtime_support": support,
        }
    print(json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL-CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(contract.CONTRACT_EXIT)
