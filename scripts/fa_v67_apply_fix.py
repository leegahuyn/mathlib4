#!/usr/bin/env python3
"""Apply v67: bounded elaboration on the two integral identities, a direct
norm-sub proof, and a direct compact-operator limit proof.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

SOURCE = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
EXPECTED_INPUT_SHA256 = "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b"

OLD_NORM = '''theorem norm_discriminantHardStageOperator_sub_graphPotential_le
    (N : ℕ) (n : ℤ) :
    ‖discriminantHardStageOperator N n - graphPotentialOperator n‖ ≤
      discriminantCuspEpsilon N := by
  rw [graphPotentialOperator_eq_weightedFull]
  have hsplit := weightedFull_sub_weightedHard_eq_weightedTail N n
  calc
    ‖discriminantHardStageOperator N n -
        weightedGraphOperator n discriminantFullCarrierWeightLp‖ =
      ‖-(weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n)‖ := by
        congr 1
        abel
    _ = ‖weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n‖ := norm_neg _
    _ = ‖weightedGraphOperator n
        (discriminantTailCarrierWeightLp N)‖ := congrArg norm hsplit
    _ ≤ discriminantCuspEpsilon N :=
      (norm_weightedGraphOperator_le n
        (discriminantTailCarrierWeightLp N)).trans
          (norm_discriminantTailCarrierWeightLp_le N)
'''

NEW_NORM = '''theorem norm_discriminantHardStageOperator_sub_graphPotential_le
    (N : ℕ) (n : ℤ) :
    ‖discriminantHardStageOperator N n - graphPotentialOperator n‖ ≤
      discriminantCuspEpsilon N := by
  rw [graphPotentialOperator_eq_weightedFull]
  calc
    ‖discriminantHardStageOperator N n -
        weightedGraphOperator n discriminantFullCarrierWeightLp‖ =
      ‖weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n‖ := norm_sub_rev _ _
    _ = ‖weightedGraphOperator n
        (discriminantTailCarrierWeightLp N)‖ :=
      congrArg norm (weightedFull_sub_weightedHard_eq_weightedTail N n)
    _ ≤ discriminantCuspEpsilon N :=
      (norm_weightedGraphOperator_le n
        (discriminantTailCarrierWeightLp N)).trans
          (norm_discriminantTailCarrierWeightLp_le N)
'''

OLD_COMPACT = '''theorem graphPotentialOperator_isCompact_unconditional (n : ℤ) :
    IsCompactOperator
      (ExplicitDiscriminantPotential.FixedPhaseGraphPotential.graphPotentialOperator n) := by
  exact graphPotentialOperator_isCompact_of_literalStageFactorization n
    (fun N ↦ graphLiteralStageRestriction
      (discriminantHardLiteralStage N) n)
    (fun N ↦ discriminantHardStagePotentialPairing N n)
    (fun N ↦ graphLiteralStageRestriction_isCompact_unconditional
      (discriminantHardLiteralStage N) n)
    (fun N ↦ by
      simpa only [discriminantHardStageOperator] using
        norm_discriminantHardStageOperator_sub_graphPotential_le N n)
'''

NEW_COMPACT = '''theorem graphPotentialOperator_isCompact_unconditional (n : ℤ) :
    IsCompactOperator
      (ExplicitDiscriminantPotential.FixedPhaseGraphPotential.graphPotentialOperator n) := by
  exact isCompactOperator_of_tendsto (l := (Filter.atTop : Filter ℕ))
    (by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero
        (fun N ↦ norm_nonneg
          (discriminantHardStageOperator N n - graphPotentialOperator n))
        (fun N ↦
          norm_discriminantHardStageOperator_sub_graphPotential_le N n)
        discriminantCuspEpsilon_tendsto_zero)
    (Filter.Eventually.of_forall fun N ↦
      discriminantHardStageOperator_isCompact N n)
'''


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one exact block, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    before = SOURCE.read_bytes()
    if digest(before) != EXPECTED_INPUT_SHA256:
        raise SystemExit(f"unexpected authoritative source SHA256: {digest(before)}")
    text = before.decode("utf-8")

    for target in (
        "theorem discriminantHardStageOperator_eq_weightedHard\n",
        "theorem weightedFull_sub_weightedHard_eq_weightedTail\n",
    ):
        text = replace_once(
            text,
            "\n" + target,
            "\nset_option maxHeartbeats 5_000_000 in\n" + target,
            target.strip(),
        )

    text = replace_once(text, OLD_NORM, NEW_NORM, "norm theorem")
    text = replace_once(text, OLD_COMPACT, NEW_COMPACT, "compactness theorem")

    after = text.encode("utf-8")
    SOURCE.write_bytes(after)
    out = Path("build-logs/fa-v67-direct-limit")
    out.mkdir(parents=True, exist_ok=True)
    evidence = {
        "schema": "fa-v67-direct-limit-fix-v1",
        "status": "MATERIALIZED_UNVERIFIED",
        "input_sha256": digest(before),
        "output_sha256": digest(after),
        "input_bytes": len(before),
        "output_bytes": len(after),
        "input_lines": len(before.decode("utf-8").splitlines()),
        "output_lines": len(text.splitlines()),
        "local_heartbeat_theorems": [
            "discriminantHardStageOperator_eq_weightedHard",
            "weightedFull_sub_weightedHard_eq_weightedTail",
        ],
        "rewritten_theorems": [
            "norm_discriminantHardStageOperator_sub_graphPotential_le",
            "graphPotentialOperator_isCompact_unconditional",
        ],
        "trust_tokens_added": {
            "sorry": 0,
            "admit": 0,
            "axiom": 0,
            "unsafe": 0,
            "native_decide": 0,
            "Lean.ofReduceBool": 0,
        },
    }
    (out / "MATERIALIZATION.json").write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
