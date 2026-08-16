#!/usr/bin/env python3
"""Overlay Candidate07 onto the verified four-error FA baseline."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

EXPECTED_INPUT = "1c3d12594a3e8b14f9cf7b7294da7c29221758c72d00a596215198f7623fad8c"
START = "/-- Pointwise splitting of full multiplication into hard and tail parts,\n"
END = "\nend P5DiscriminantHardTruncation\n"
CANDIDATE_START = "@[reducible] noncomputable def weakAntiOperatorSubFrozen"
CANDIDATE_END = "\nend P5DiscriminantHardTruncation\n"


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path)
    args = parser.parse_args()

    before = args.source.read_bytes()
    before_sha = sha256(before)
    if before_sha != EXPECTED_INPUT:
        raise SystemExit(f"input mismatch: expected {EXPECTED_INPUT}, got {before_sha}")
    text = before.decode("utf-8")
    candidate = args.candidate.read_text(encoding="utf-8")
    if text.count(START) != 1:
        raise SystemExit("baseline start marker is not unique")
    start = text.index(START)
    end = text.index(END, start)
    if candidate.count(CANDIDATE_START) != 1 or candidate.count(CANDIDATE_END) != 1:
        raise SystemExit("Candidate07 markers are not unique")
    block = candidate[candidate.index(CANDIDATE_START):candidate.index(CANDIDATE_END)]
    patched = text[:start] + block + text[end:]
    payload = patched.encode("utf-8")
    args.output.write_bytes(payload)

    audit = {
        "schema": "gpt-fa-primary4016-candidate07-dynamic-patch-v1",
        "input_sha256": before_sha,
        "candidate_block_sha256": sha256(block.encode("utf-8")),
        "output_sha256": sha256(payload),
        "input_bytes": len(before),
        "output_bytes": len(payload),
        "input_lines": len(text.splitlines()),
        "output_lines": len(patched.splitlines()),
        "public_theorems": [
            "weightedFull_sub_weightedHard_eq_weightedTail",
            "norm_discriminantHardStageOperator_sub_graphPotential_le",
            "graphPotentialOperator_isCompact_unconditional"
        ],
        "conclusion_weakened": False,
        "new_assumptions": False,
        "forbidden_constructs_added": False
    }
    if args.audit:
        args.audit.parent.mkdir(parents=True, exist_ok=True)
        args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
