#!/usr/bin/env python3
"""Fail-closed v65 runtime materializer.

The CLI validates every locked input and composes in memory before creating any
output.  PENDING selections produce exit 2 and no files unless the explicitly
local ``--allow-pending-static-replay`` test flag is supplied.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import fa_v65_contract as contract


def _ordinary(path: Path) -> None:
    if path.is_symlink() or not path.is_file():
        raise AssertionError(f"not an ordinary file: {path}")


def _write_new(path: Path, payload: bytes) -> None:
    if path.exists() or path.is_symlink():
        raise AssertionError(f"refusing to overwrite materialization output: {path}")
    path.write_bytes(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", required=True)
    parser.add_argument("--expected-selection-sha256", required=True)
    parser.add_argument("--variant", required=True, choices=contract.LANE_ORDER)
    parser.add_argument("--authority-source", required=True)
    parser.add_argument("--repo-root", required=True)
    parser.add_argument("--write-root", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--audit", required=True)
    parser.add_argument("--evidence", required=True)
    parser.add_argument("--allow-pending-static-replay", action="store_true")
    parser.add_argument("--static-test-sentinel")
    args = parser.parse_args()

    selection_path = Path(args.selection)
    _ordinary(selection_path)
    selection_bytes = selection_path.read_bytes()
    if contract.sha256(selection_bytes) != args.expected_selection_sha256:
        raise AssertionError("selection SHA mismatch")
    selection = json.loads(selection_bytes)
    ready = selection.get("status") == "READY"
    if not ready and not args.allow_pending_static_replay:
        print("v65 selection remains PENDING; materialization forbidden", file=sys.stderr)
        return contract.PENDING_EXIT
    contract.validate_selection(selection, require_ready=ready)

    repo_root = Path(args.repo_root)
    contract.validate_runtime_support(repo_root, selection, require_ready=ready)
    authority_path = Path(args.authority_source)
    if authority_path.is_symlink() or not authority_path.is_file():
        raise AssertionError("authority source is not an ordinary file")
    authority_payload = authority_path.read_bytes()

    write_root_arg = Path(args.write_root)
    if not write_root_arg.is_absolute() or write_root_arg.is_symlink() or not write_root_arg.is_dir():
        raise AssertionError("write root must be an existing absolute ordinary directory")
    write_root = write_root_arg.resolve(strict=True)
    output_paths = [Path(args.output), Path(args.audit), Path(args.evidence)]
    resolved_outputs: list[Path] = []
    for path in output_paths:
        if not path.is_absolute() or path.exists() or path.is_symlink():
            raise AssertionError("materialization outputs must be absent absolute paths")
        if path.name in {"", ".", ".."} or path.parent.resolve(strict=True) != write_root:
            raise AssertionError("materialization output escapes exact write root")
        resolved_outputs.append(path.resolve(strict=False))
    if len(set(resolved_outputs)) != 3:
        raise AssertionError("output, audit, and evidence paths must be distinct")

    if not ready:
        if not contract.STATIC_LAYOUT:
            raise AssertionError("PENDING static replay is forbidden in promoted runtime")
        if not args.static_test_sentinel:
            raise AssertionError("PENDING static replay sentinel is required")
        sentinel = Path(args.static_test_sentinel)
        if sentinel.is_symlink() or not sentinel.is_file() or sentinel.parent.resolve(strict=True) != write_root:
            raise AssertionError("invalid PENDING static replay sentinel path")
        if sentinel.name != ".fa-v65-local-static-replay" or sentinel.read_bytes() != b"FA_V65_LOCAL_STATIC_REPLAY_ONLY\n":
            raise AssertionError("invalid PENDING static replay sentinel bytes")
    elif args.allow_pending_static_replay or args.static_test_sentinel:
        raise AssertionError("static replay switches are forbidden for READY")

    payload, audit = contract.compose_lane(
        args.variant, authority_source=authority_payload, repo_root=repo_root)
    rows = [row for row in selection["variants"] if row["name"] == args.variant]
    if len(rows) != 1 or rows[0]["expected_candidate"] != audit["candidate"]:
        raise AssertionError("selected lane candidate lock mismatch")
    evidence = {
        "schema": "fa-v65-materialization-v1",
        "status": "READY_EXACT" if ready else "STATIC_PENDING_REPLAY_ONLY",
        "variant": args.variant,
        "selection_sha256": args.expected_selection_sha256,
        "candidate_sha256": audit["candidate"]["sha256"],
        "candidate_bytes": audit["candidate"]["bytes"],
        "candidate_lines": audit["candidate"]["lines"],
        "declaration_count": audit["candidate"]["declaration_count"],
        "composition_mode": audit["composition_mode"],
        "runtime_fallback_used": False,
        "pending_static_replay_used": not ready,
        "direct_lean_verified": False,
        "clean_claimed": False,
    }

    # All validation above is complete before the first output path is touched.
    _write_new(Path(args.output), payload)
    _write_new(Path(args.audit), contract.canonical_json(audit))
    _write_new(Path(args.evidence), contract.canonical_json(evidence))
    print(json.dumps(evidence, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL-CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(contract.CONTRACT_EXIT)
