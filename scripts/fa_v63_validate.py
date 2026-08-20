#!/usr/bin/env python3
"""Read-only READY/PENDING validator for the v63 direct-matrix contract."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from fa_v63_contract import (
    ContractError,
    PendingInput,
    load_ready_contract,
    validate_pending_scaffold,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--authority-lock", type=Path, required=True)
    parser.add_argument("--manifest-schema", type=Path, required=True)
    parser.add_argument("--expected-selection-sha256")
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--mode", choices=("ready", "pending-static"), default="ready")
    parser.add_argument("--emit", choices=("summary", "matrix"), default="summary")
    args = parser.parse_args()
    try:
        if args.mode == "pending-static":
            contract = validate_pending_scaffold(
                selection_path=args.selection,
                authority_lock_path=args.authority_lock,
                manifest_schema_path=args.manifest_schema,
                expected_selection_sha256=args.expected_selection_sha256,
                repo_root=args.repo_root,
            )
            status = "PENDING_STATIC_VALIDATED_NOT_ACTIVATED"
        else:
            contract = load_ready_contract(
                selection_path=args.selection,
                authority_lock_path=args.authority_lock,
                manifest_schema_path=args.manifest_schema,
                expected_selection_sha256=args.expected_selection_sha256,
                repo_root=args.repo_root,
            )
            status = "READY"
    except PendingInput as exc:
        print(f"PENDING: {exc}", file=sys.stderr)
        return 2
    except (ContractError, OSError) as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        return 86
    selection = contract["selection"]
    if args.emit == "matrix":
        if status != "READY":
            print("PENDING: matrix emission is forbidden for PENDING selection",
                  file=sys.stderr)
            return 2
        print(json.dumps({"variant": selection["variant_order"]}, separators=(",", ":")))
    else:
        print(json.dumps({
            "schema": "fa-v63-selection-validation-v1",
            "status": status,
            "selection_sha256": contract["selection_sha256"],
            "variant_order": selection["variant_order"],
            "variant_count": len(selection["variant_order"]),
            "manifest_count": len(contract["manifests"]),
            "repair_count": len(contract["all_repairs"]),
            "activation_allowed": status == "READY",
            "write_performed": False,
            "direct_lean_verified": False,
        }, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
