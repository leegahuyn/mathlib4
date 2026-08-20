#!/usr/bin/env python3
"""Read-only validator for the v61 PENDING/READY direct Lean contract."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from fa_v61_contract import ContractError, PendingInput, load_ready_contract


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--authority-lock", type=Path, required=True)
    parser.add_argument("--manifest-schema", type=Path, required=True)
    parser.add_argument("--cross-audit", type=Path, required=True)
    parser.add_argument("--expected-selection-sha256")
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--emit", choices=("summary", "matrix"), default="summary")
    args = parser.parse_args()
    try:
        contract = load_ready_contract(
            selection_path=args.selection,
            authority_lock_path=args.authority_lock,
            manifest_schema_path=args.manifest_schema,
            cross_audit_path=args.cross_audit,
            expected_selection_sha256=args.expected_selection_sha256,
            repo_root=args.repo_root,
        )
    except PendingInput as exc:
        print(f"PENDING: {exc}", file=sys.stderr)
        return 2
    except ContractError as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        return 86
    selection = contract["selection"]
    if args.emit == "matrix":
        print(json.dumps({"variant": selection["variant_order"]}, separators=(",", ":")))
    else:
        print(json.dumps({
            "schema": "fa-v61-selection-validation-v1",
            "status": "READY",
            "selection_sha256": contract["selection_sha256"],
            "variant_order": selection["variant_order"],
            "manifest_count": len(contract["manifest_records"]),
            "repair_count": len(contract["all_repairs"]),
            "write_performed": False,
        }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
