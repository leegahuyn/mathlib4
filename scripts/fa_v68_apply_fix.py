#!/usr/bin/env python3
"""Apply v68 to the exact v65 winner: correctly scope local heartbeat wrappers,
shorten the norm proof, and prove compactness directly as a norm limit.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

SOURCE = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
EXPECTED_INPUT_SHA256 = "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b"
HEARTBEATS = "10_000_000"

OLD_4017 = '''/-- Hard multiplication on the global carrier agrees with the literal-stage
factorization because every carrier point where the hard weight is nonzero
lies in the chosen literal stage. -/
theorem discriminantHardStageOperator_eq_weightedHard
'''
NEW_4017 = f'''set_option maxHeartbeats {HEARTBEATS} in
/-- Hard multiplication on the global carrier agrees with the literal-stage
factorization because every carrier point where the hard weight is nonzero
lies in the chosen literal stage. -/
theorem discriminantHardStageOperator_eq_weightedHard
'''

OLD_4018 = '''/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
'''
NEW_4018 = f'''set_option maxHeartbeats {HEARTBEATS} in
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
'''

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
  apply isCompactOperator_of_tendsto (l := (Filter.atTop : Filter ℕ))
  · change Filter.Tendsto
      (fun N : ℕ ↦ discriminantHardStageOperator N n)
      Filter.atTop
      (@nhds
        (GraphSobolevCompletion n →L[ℂ] StrongAntiDual (GraphSobolevCompletion n))
        (@UniformSpace.toTopologicalSpace
          (GraphSobolevCompletion n →L[ℂ] StrongAntiDual (GraphSobolevCompletion n))
          (@PseudoMetricSpace.toUniformSpace
            (GraphSobolevCompletion n →L[ℂ] StrongAntiDual (GraphSobolevCompletion n))
            SeminormedAddCommGroup.toPseudoMetricSpace))
        (graphPotentialOperator n))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero
      (fun N ↦ norm_nonneg
        (discriminantHardStageOperator N n - graphPotentialOperator n))
      (fun N ↦ norm_discriminantHardStageOperator_sub_graphPotential_le N n)
      discriminantCuspEpsilon_tendsto_zero
  · exact Filter.Eventually.of_forall fun N ↦
      discriminantHardStageOperator_isCompact N n
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
    text = replace_once(text, OLD_4017, NEW_4017, "decl4017")
    text = replace_once(text, OLD_4018, NEW_4018, "decl4018")
    text = replace_once(text, OLD_NORM, NEW_NORM, "decl4019")
    text = replace_once(text, OLD_COMPACT, NEW_COMPACT, "decl4020")

    after = text.encode("utf-8")
    SOURCE.write_bytes(after)
    out = Path("build-logs/fa-v68-correct-wrapper")
    out.mkdir(parents=True, exist_ok=True)
    evidence = {
        "schema": "fa-v68-correct-wrapper-fix-v1",
        "status": "MATERIALIZED_UNVERIFIED",
        "input_sha256": digest(before),
        "output_sha256": digest(after),
        "input_bytes": len(before),
        "output_bytes": len(after),
        "input_lines": len(before.decode("utf-8").splitlines()),
        "output_lines": len(text.splitlines()),
        "heartbeat_budget": HEARTBEATS,
        "expected_output_sha256": "c663ec1068e2f28aa7c8ebcb5d9ca50430bd24fb79d5be8bea8e5235fc67be37",
        "trust_tokens_added": {
            "sorry": 0,
            "admit": 0,
            "axiom": 0,
            "unsafe": 0,
            "native_decide": 0,
            "Lean.ofReduceBool": 0,
        },
    }
    if evidence["output_sha256"] != evidence["expected_output_sha256"]:
        raise SystemExit("v68 output lock mismatch")
    (out / "MATERIALIZATION.json").write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
