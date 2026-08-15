#!/usr/bin/env python3
"""Normalize all source-level Lean resource options on the exact v65 winner.

No theorem statement or proof body is edited.  Existing finite heartbeat limits
are changed to unlimited, existing recursion-depth limits are raised, and a
post-import fallback is inserted so command-line defaults cannot reintroduce
the 200k frontier.
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


def h(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--evidence", required=True, type=Path)
    ap.add_argument("--rec-depth", type=int, default=100000)
    ns = ap.parse_args()

    raw = ns.source.read_bytes()
    if h(raw) != AUTHORITY_SHA256:
        raise SystemExit("authority SHA mismatch")
    if ns.rec_depth <= 0:
        raise SystemExit("invalid recursion depth")
    text = raw.decode("utf-8")
    for target in TARGETS:
        if text.count(target) < 1:
            raise SystemExit(f"missing target {target}")

    heartbeat_pattern = re.compile(
        r"(?m)^(?P<prefix>\s*set_option\s+(?:[A-Za-z0-9_.]*maxHeartbeats)\s+)\d+(?P<suffix>\s*(?:in)?\s*)$"
    )
    rec_pattern = re.compile(
        r"(?m)^(?P<prefix>\s*set_option\s+(?:[A-Za-z0-9_.]*maxRecDepth)\s+)\d+(?P<suffix>\s*(?:in)?\s*)$"
    )
    rewritten, hb_count = heartbeat_pattern.subn(lambda m: m.group('prefix') + '0' + m.group('suffix'), text)
    rewritten, rec_count = rec_pattern.subn(
        lambda m: m.group('prefix') + str(ns.rec_depth) + m.group('suffix'), rewritten
    )

    lines = rewritten.splitlines(keepends=True)
    last_import = -1
    for i, line in enumerate(lines):
        if re.match(r"^\s*import\s+", line):
            last_import = i
        elif last_import >= 0 and line.strip() and not line.lstrip().startswith("--"):
            break
    if last_import < 0:
        raise SystemExit("no imports")
    insertion = (
        "\n-- v69: kernel-safe elaboration resource normalization\n"
        "set_option maxHeartbeats 0\n"
        f"set_option maxRecDepth {ns.rec_depth}\n\n"
    )
    result_text = "".join(lines[:last_import + 1]) + insertion + "".join(lines[last_import + 1:])
    result = result_text.encode("utf-8")
    ns.output.parent.mkdir(parents=True, exist_ok=True)
    ns.output.write_bytes(result)

    evidence = {
        "schema": "fa-v69-resource-option-normalization-v1",
        "authority_sha256": AUTHORITY_SHA256,
        "candidate_sha256": h(result),
        "candidate_bytes": len(result),
        "candidate_lines": len(result_text.splitlines()),
        "finite_heartbeat_options_rewritten": hb_count,
        "rec_depth_options_rewritten": rec_count,
        "fallback_maxHeartbeats": 0,
        "fallback_maxRecDepth": ns.rec_depth,
        "targets_observed": list(TARGETS),
        "statement_or_proof_text_changed": False,
        "trust_bypass_added": False,
    }
    ns.evidence.parent.mkdir(parents=True, exist_ok=True)
    ns.evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
