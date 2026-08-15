#!/usr/bin/env python3
"""Materialize the authoritative v65 winner and raise the local heartbeat budget
only across the final P5 hard-stage/compactness cluster.

The input source is locked to the v65 all_field_w_primary candidate.  This
script intentionally makes no theorem-body or statement change.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

EXPECTED_INPUT_SHA256 = "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b"
START_MARKER = (
    "/-- Hard multiplication on the global carrier agrees with the literal-stage\n"
)
END_MARKER = "\nend P5DiscriminantHardTruncation\n"
START_INSERT = "set_option maxHeartbeats 2000000\n\n"
END_INSERT = "\nset_option maxHeartbeats 200000\n"


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()

    before = args.source.read_bytes()
    before_sha = sha256(before)
    if before_sha != EXPECTED_INPUT_SHA256:
        raise SystemExit(
            f"locked input mismatch: expected {EXPECTED_INPUT_SHA256}, got {before_sha}"
        )

    text = before.decode("utf-8")
    if text.count(START_MARKER) != 1:
        raise SystemExit("start marker is not unique")

    start = text.index(START_MARKER)
    compact_decl = text.index(
        "theorem graphPotentialOperator_isCompact_unconditional (n : ℤ)", start
    )
    end = text.index(END_MARKER, compact_decl)

    patched = text[:start] + START_INSERT + text[start:end] + END_INSERT + text[end:]
    after = patched.encode("utf-8")
    args.source.write_bytes(after)

    audit = {
        "schema": "fa-v66-final-three-heartbeat-scope-v1",
        "input_sha256": before_sha,
        "output_sha256": sha256(after),
        "input_bytes": len(before),
        "output_bytes": len(after),
        "input_lines": len(text.splitlines()),
        "output_lines": len(patched.splitlines()),
        "local_max_heartbeats": 2_000_000,
        "restored_max_heartbeats": 200_000,
        "first_scoped_declaration": "discriminantHardStageOperator_eq_weightedHard",
        "last_scoped_declaration": "graphPotentialOperator_isCompact_unconditional",
        "theorem_statements_changed": False,
        "theorem_bodies_changed": False,
    }
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(audit, sort_keys=True))


if __name__ == "__main__":
    main()
