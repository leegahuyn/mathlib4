#!/usr/bin/env python3
"""Generate a global-budget candidate from the exact sealed v65 FA winner."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

AUTHORITY_SHA256 = "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b"
TARGETS = (
    "discriminantHardStageOperator_eq_weightedHard",
    "norm_discriminantHardStageOperator_sub_graphPotential_le",
    "graphPotentialOperator_isCompact_unconditional",
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--source", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--heartbeat", required=True, type=int)
    p.add_argument("--rec-depth", required=True, type=int)
    p.add_argument("--evidence", required=True, type=Path)
    a = p.parse_args()

    raw = a.source.read_bytes()
    if digest(raw) != AUTHORITY_SHA256:
        raise SystemExit("exact authority SHA mismatch")
    if a.heartbeat < 0 or a.rec_depth <= 0:
        raise SystemExit("invalid budget")
    text = raw.decode("utf-8")
    for target in TARGETS:
        count = len(re.findall(rf"\b(?:theorem|lemma)\s+{re.escape(target)}\b", text))
        if count != 1:
            raise SystemExit(f"expected exactly one {target}, found {count}")

    lines = text.splitlines(keepends=True)
    last_import = -1
    for i, line in enumerate(lines):
        if re.match(r"^\s*import\s+", line):
            last_import = i
        elif last_import >= 0 and line.strip() and not line.lstrip().startswith("--"):
            break
    if last_import < 0:
        raise SystemExit("no import block found")

    insertion = (
        f"\nset_option maxHeartbeats {a.heartbeat}\n"
        f"set_option maxRecDepth {a.rec_depth}\n\n"
    )
    generated_text = "".join(lines[: last_import + 1]) + insertion + "".join(lines[last_import + 1 :])
    generated = generated_text.encode("utf-8")
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_bytes(generated)

    evidence = {
        "schema": "fa-v68-global-elaboration-budget-v1",
        "authority_sha256": AUTHORITY_SHA256,
        "candidate_sha256": digest(generated),
        "candidate_bytes": len(generated),
        "candidate_lines": len(generated_text.splitlines()),
        "maxHeartbeats": a.heartbeat,
        "maxRecDepth": a.rec_depth,
        "targets_observed": list(TARGETS),
        "statement_or_proof_text_changed": False,
        "trust_bypass_added": False,
    }
    a.evidence.parent.mkdir(parents=True, exist_ok=True)
    a.evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
