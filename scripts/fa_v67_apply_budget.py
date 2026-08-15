#!/usr/bin/env python3
"""Apply local, kernel-safe elaboration budgets to the exact v65 FA winner.

This script does not alter theorem statements or proof terms.  It inserts Lean
command-scoped resource options immediately before the three declarations that
remain after the v65 tournament.  The generated source is then compiled by a
fresh direct Lean process.
"""

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


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--heartbeat", required=True, type=int)
    parser.add_argument("--rec-depth", required=True, type=int)
    parser.add_argument("--evidence", required=True, type=Path)
    args = parser.parse_args()

    raw = args.source.read_bytes()
    actual_authority = sha256_bytes(raw)
    if actual_authority != AUTHORITY_SHA256:
        raise SystemExit(
            f"authority source mismatch: expected {AUTHORITY_SHA256}, got {actual_authority}"
        )
    if args.heartbeat < 0 or args.rec_depth <= 0:
        raise SystemExit("heartbeat must be nonnegative and rec-depth must be positive")

    text = raw.decode("utf-8")
    original_lines = text.splitlines(keepends=True)
    output_lines: list[str] = []
    insertions: list[dict[str, object]] = []
    seen: set[str] = set()

    patterns = {
        target: re.compile(
            rf"^(?P<indent>\s*)(?:(?:private|protected|noncomputable)\s+)*"
            rf"(?:theorem|lemma)\s+{re.escape(target)}\b"
        )
        for target in TARGETS
    }

    for line_no, line in enumerate(original_lines, start=1):
        matched_target: str | None = None
        matched_indent = ""
        for target, pattern in patterns.items():
            match = pattern.match(line)
            if match is not None:
                matched_target = target
                matched_indent = match.group("indent")
                break
        if matched_target is not None:
            if matched_target in seen:
                raise SystemExit(f"duplicate declaration target: {matched_target}")
            seen.add(matched_target)
            output_lines.append(
                f"{matched_indent}set_option maxHeartbeats {args.heartbeat} in\n"
            )
            output_lines.append(
                f"{matched_indent}set_option maxRecDepth {args.rec_depth} in\n"
            )
            insertions.append(
                {
                    "declaration": matched_target,
                    "original_line": line_no,
                    "maxHeartbeats": args.heartbeat,
                    "maxRecDepth": args.rec_depth,
                }
            )
        output_lines.append(line)

    missing = [target for target in TARGETS if target not in seen]
    if missing:
        raise SystemExit(f"missing declaration targets: {missing}")

    generated = "".join(output_lines).encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(generated)

    evidence = {
        "schema": "fa-v67-local-elaboration-budget-v1",
        "authority_sha256": actual_authority,
        "candidate_sha256": sha256_bytes(generated),
        "candidate_bytes": len(generated),
        "candidate_lines": len(generated.decode("utf-8").splitlines()),
        "maxHeartbeats": args.heartbeat,
        "maxRecDepth": args.rec_depth,
        "targets": list(TARGETS),
        "insertions": insertions,
        "statement_or_proof_text_changed": False,
        "trust_bypass_added": False,
    }
    args.evidence.parent.mkdir(parents=True, exist_ok=True)
    args.evidence.write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
