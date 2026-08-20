#!/usr/bin/env python3
"""Apply the locally versioned Candidate05 proof cluster to the verified FA baseline."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

EXPECTED_INPUT = "1c3d12594a3e8b14f9cf7b7294da7c29221758c72d00a596215198f7623fad8c"
EXPECTED_OUTPUT = "c8a1d7552d719bb5d71120020e9b1aa9d3bce12066cdbf2f663a969a8cafc86d"
START = "/-- Pointwise splitting of full multiplication into hard and tail parts,\n"
MIDDLE = "theorem norm_discriminantHardStageOperator_sub_graphPotential_le"
END = "/-- Final P5 endpoint:"
CANDIDATE_START = "@[reducible] noncomputable def weakAntiOperatorSubFrozen"
CANDIDATE_END = "\nend P5DiscriminantHardTruncation\n"
PUBLIC_OLD = "weightedFull_sub_weightedHard_eq_weightedTail_frozen"
PUBLIC_NEW = "weightedFull_sub_weightedHard_eq_weightedTail"
OLD_FINAL = """    (fun N ↦ by
      simpa only [discriminantHardStageOperator] using
        norm_discriminantHardStageOperator_sub_graphPotential_le N n)"""
NEW_FINAL = """    (fun N ↦ by
      exact norm_discriminantHardStageOperator_sub_graphPotential_le N n)"""

NORM_BLOCK = r'''/-- Reversing a difference does not change the operator norm.  Keeping this
lemma generic prevents WHNF expansion of the concrete completion abbreviation. -/
theorem norm_sub_rev_eq_norm_weakAntiOperatorSubFrozen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) :
    ‖B - A‖ = ‖weakAntiOperatorSubFrozen A B‖ := by
  simpa only [weakAntiOperatorSubFrozen] using (norm_sub_rev B A)

theorem norm_discriminantHardStageOperator_sub_graphPotential_le
    (N : ℕ) (n : ℤ) :
    ‖discriminantHardStageOperator N n - graphPotentialOperator n‖ ≤
      discriminantCuspEpsilon N := by
  rw [graphPotentialOperator_eq_weightedFull]
  calc
    ‖discriminantHardStageOperator N n -
        weightedGraphOperator n discriminantFullCarrierWeightLp‖ =
      ‖weakAntiOperatorSubFrozen
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n)‖ :=
      norm_sub_rev_eq_norm_weakAntiOperatorSubFrozen
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n)
    _ = ‖weightedGraphOperator n
        (discriminantTailCarrierWeightLp N)‖ :=
      congrArg norm (weightedFull_sub_weightedHard_eq_weightedTail N n)
    _ ≤ discriminantCuspEpsilon N :=
      (norm_weightedGraphOperator_le n
        (discriminantTailCarrierWeightLp N)).trans
          (norm_discriminantTailCarrierWeightLp_le N)

'''


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
    if candidate.count(CANDIDATE_START) != 1 or candidate.count(CANDIDATE_END) != 1:
        raise SystemExit("candidate proof-cluster markers are not unique")
    block = candidate[candidate.index(CANDIDATE_START):candidate.index(CANDIDATE_END)]
    if block.count(PUBLIC_OLD) != 1:
        raise SystemExit("candidate public theorem marker is not unique")
    block = block.replace(PUBLIC_OLD, PUBLIC_NEW, 1)

    if text.count(START) != 1 or text.count(MIDDLE) != 1 or text.count(END) != 1:
        raise SystemExit("baseline source markers are not unique")
    start = text.index(START)
    middle = text.index(MIDDLE, start)
    end = text.index(END, middle)
    patched = text[:start] + block + "\n\n" + NORM_BLOCK + text[end:]
    if patched.count(OLD_FINAL) != 1:
        raise SystemExit("final compactness conversion marker is not unique")
    patched = patched.replace(OLD_FINAL, NEW_FINAL, 1)
    payload = patched.encode("utf-8")
    output_sha = sha256(payload)
    if output_sha != EXPECTED_OUTPUT:
        raise SystemExit(f"output mismatch: expected {EXPECTED_OUTPUT}, got {output_sha}")
    args.output.write_bytes(payload)

    audit = {
        "schema": "gpt-fa-primary4016-candidate05-dynamic-patch-v1",
        "input_sha256": before_sha,
        "candidate_block_sha256": sha256(block.encode("utf-8")),
        "output_sha256": output_sha,
        "input_bytes": len(before),
        "output_bytes": len(payload),
        "input_lines": len(text.splitlines()),
        "output_lines": len(patched.splitlines()),
        "public_theorem_name": PUBLIC_NEW,
        "conclusion_weakened": False,
        "new_assumptions": False,
        "forbidden_constructs_added": False,
    }
    if args.audit:
        args.audit.parent.mkdir(parents=True, exist_ok=True)
        args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
