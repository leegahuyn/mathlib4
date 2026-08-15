#!/usr/bin/env python3
"""Split the final hard-stage equality into small kernel-checked lemmas and
make the downstream norm identity fully typed.

The input is locked to the authoritative v65 all_field_w_primary source.
No theorem statement is weakened and no axiom, sorry, admit, unsafe
construction, native_decide, or unchecked oracle is introduced.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

EXPECTED_INPUT_SHA256 = "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b"
EXPECTED_OUTPUT_SHA256 = "1c3d12594a3e8b14f9cf7b7294da7c29221758c72d00a596215198f7623fad8c"
START_MARKER = "/-- Hard multiplication on the global carrier agrees with the literal-stage\n"
END_MARKER = "/-- Pointwise splitting of full multiplication into hard and tail parts,\n"
OLD_NORM_STEP = """    _ = ‖weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n‖ := norm_neg _"""
NEW_NORM_STEP = """    _ = ‖weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n‖ := by
      simpa only using
        (norm_neg
          (weightedGraphOperator n discriminantFullCarrierWeightLp -
            discriminantHardStageOperator N n :
              WeakAntiOperator (GraphSobolevCompletion n)))"""
NEW_BLOCK = "/-- The scalar integrand shared by the literal-stage and global-carrier\npresentations of the hard discriminant multiplier. -/\nnoncomputable def discriminantHardStageIntegrand\n    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) (z : ℍ) : ℂ :=\n  inner ℂ (graphEuclideanBase n v z)\n    (discriminantHardStageWeight N z * graphEuclideanBase n u z)\n\n/-- The literal-stage inner product is the corresponding set integral on the\nglobal Euclidean carrier. -/\ntheorem discriminantHardStage_literalInner_eq_setIntegral\n    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) :\n    (∫ z,\n        inner ℂ\n          (graphLiteralStageRestriction\n            (discriminantHardLiteralStage N) n v z)\n          ((discriminantHardStageWeightLp N •\n            graphLiteralStageRestriction\n              (discriminantHardLiteralStage N) n u :\n              P5PhysicalHardStageRestriction.LiteralStageL2\n                (discriminantHardLiteralStage N)) z)\n        ∂P5PhysicalHardStageRestriction.literalStageMeasure\n          (discriminantHardLiteralStage N)) =\n      ∫ z in gammaTwoThreeCuspTruncation\n          (discriminantHardLiteralStage N),\n        discriminantHardStageIntegrand N n u v z\n        ∂chosenEuclideanCarrierMeasure := by\n  apply integral_congr_ae\n  filter_upwards [\n    coeFn_graphLiteralStageRestriction\n      (discriminantHardLiteralStage N) n v,\n    coeFn_graphLiteralStageRestriction\n      (discriminantHardLiteralStage N) n u,\n    coeFn_discriminantHardStageWeightLp N,\n    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)\n      (discriminantHardStageWeightLp N)\n      (graphLiteralStageRestriction\n        (discriminantHardLiteralStage N) n u)] with z hv hu hw hmul\n  unfold discriminantHardStageIntegrand\n  rw [hv, hmul, Pi.smul_apply', smul_eq_mul, hw, hu]\n  simp only [graphEuclideanBase, ContinuousLinearMap.comp_apply]\n\n/-- The hard-stage integrand vanishes off its literal stage, so restriction\ndoes not change its global-carrier integral. -/\ntheorem discriminantHardStage_setIntegral_eq_integral\n    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) :\n    (∫ z in gammaTwoThreeCuspTruncation\n          (discriminantHardLiteralStage N),\n        discriminantHardStageIntegrand N n u v z\n        ∂chosenEuclideanCarrierMeasure) =\n      ∫ z, discriminantHardStageIntegrand N n u v z\n        ∂chosenEuclideanCarrierMeasure := by\n  apply setIntegral_eq_integral_of_ae_compl_eq_zero\n  filter_upwards [ae_restrict_mem\n    chosenGammaTwoFundamentalDomain.carrier_measurable] with z hzCarrier hz\n  have hzClosed : z ∈ gammaTwoClosedTileCarrier := by\n    rwa [gammaTwoClosedTileCarrier_eq_chosenCarrier]\n  unfold discriminantHardStageIntegrand\n  rw [discriminantHardStageWeight_eq_zero_outside_literalStage\n    N hzClosed hz]\n  simp\n\n/-- The global hard-stage scalar integrand is the `L∞ · L²` carrier\nmultiplication integrand. -/\ntheorem discriminantHardStage_integral_eq_weightedIntegral\n    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) :\n    (∫ z, discriminantHardStageIntegrand N n u v z\n        ∂chosenEuclideanCarrierMeasure) =\n      ∫ z,\n        inner ℂ (graphEuclideanBase n v z)\n          ((discriminantHardCarrierWeightLp N •\n            graphEuclideanBase n u : OrbitEuclideanL2 n) z)\n        ∂chosenEuclideanCarrierMeasure := by\n  apply integral_congr_ae\n  filter_upwards [\n    coeFn_discriminantHardCarrierWeightLp N,\n    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)\n      (discriminantHardCarrierWeightLp N)\n      (graphEuclideanBase n u)] with z hw hmul\n  unfold discriminantHardStageIntegrand\n  rw [hmul, Pi.smul_apply', smul_eq_mul, hw]\n\n/-- Hard multiplication on the global carrier agrees with the literal-stage\nfactorization because every carrier point where the hard weight is nonzero\nlies in the chosen literal stage. -/\ntheorem discriminantHardStageOperator_eq_weightedHard\n    (N : ℕ) (n : ℤ) :\n    discriminantHardStageOperator N n =\n      weightedGraphOperator n (discriminantHardCarrierWeightLp N) := by\n  apply ContinuousLinearMap.ext\n  intro u\n  apply ContinuousLinearMap.ext\n  intro v\n  simp only [discriminantHardStageOperator,\n    ContinuousLinearMap.comp_apply,\n    discriminantHardStagePotentialPairing,\n    LinearMap.mkContinuous₂_apply,\n    weightedGraphOperator]\n  change inner ℂ\n      (graphLiteralStageRestriction (discriminantHardLiteralStage N) n v)\n      (lpInfinityMultiplier\n        (P5PhysicalHardStageRestriction.literalStageMeasure\n          (discriminantHardLiteralStage N))\n        (discriminantHardStageWeightLp N)\n        (graphLiteralStageRestriction\n          (discriminantHardLiteralStage N) n u)) =\n    inner ℂ (graphEuclideanBase n v)\n      (lpInfinityMultiplier chosenEuclideanCarrierMeasure\n        (discriminantHardCarrierWeightLp N)\n        (graphEuclideanBase n u))\n  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]\n  calc\n    (∫ z,\n        inner ℂ\n          (graphLiteralStageRestriction\n            (discriminantHardLiteralStage N) n v z)\n          ((discriminantHardStageWeightLp N •\n            graphLiteralStageRestriction\n              (discriminantHardLiteralStage N) n u :\n              P5PhysicalHardStageRestriction.LiteralStageL2\n                (discriminantHardLiteralStage N)) z)\n        ∂P5PhysicalHardStageRestriction.literalStageMeasure\n          (discriminantHardLiteralStage N)) =\n      ∫ z in gammaTwoThreeCuspTruncation\n          (discriminantHardLiteralStage N),\n        discriminantHardStageIntegrand N n u v z\n        ∂chosenEuclideanCarrierMeasure :=\n      discriminantHardStage_literalInner_eq_setIntegral N n u v\n    _ = ∫ z, discriminantHardStageIntegrand N n u v z\n          ∂chosenEuclideanCarrierMeasure :=\n      discriminantHardStage_setIntegral_eq_integral N n u v\n    _ = ∫ z,\n        inner ℂ (graphEuclideanBase n v z)\n          ((discriminantHardCarrierWeightLp N •\n            graphEuclideanBase n u : OrbitEuclideanL2 n) z)\n        ∂chosenEuclideanCarrierMeasure :=\n      discriminantHardStage_integral_eq_weightedIntegral N n u v"


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
    if text.count(START_MARKER) != 1 or text.count(END_MARKER) != 1:
        raise SystemExit("proof-cluster markers are not unique")
    if text.count(OLD_NORM_STEP) != 1:
        raise SystemExit("norm step marker is not unique")

    start = text.index(START_MARKER)
    end = text.index(END_MARKER, start)
    patched = text[:start] + NEW_BLOCK + "\n\n" + text[end:]
    patched = patched.replace(OLD_NORM_STEP, NEW_NORM_STEP, 1)
    after = patched.encode("utf-8")
    after_sha = sha256(after)
    if after_sha != EXPECTED_OUTPUT_SHA256:
        raise SystemExit(
            f"deterministic output mismatch: expected {EXPECTED_OUTPUT_SHA256}, got {after_sha}"
        )
    args.source.write_bytes(after)

    audit = {
        "schema": "fa-v66-final-three-proof-split-v2",
        "input_sha256": before_sha,
        "output_sha256": after_sha,
        "input_bytes": len(before),
        "output_bytes": len(after),
        "input_lines": len(text.splitlines()),
        "output_lines": len(patched.splitlines()),
        "added_helper_declarations": [
            "discriminantHardStageIntegrand",
            "discriminantHardStage_literalInner_eq_setIntegral",
            "discriminantHardStage_setIntegral_eq_integral",
            "discriminantHardStage_integral_eq_weightedIntegral",
        ],
        "refactored_declaration": "discriminantHardStageOperator_eq_weightedHard",
        "typed_norm_step": "norm_discriminantHardStageOperator_sub_graphPotential_le",
        "theorem_statements_changed": False,
        "theorem_bodies_changed": True,
        "heartbeat_override_added": False,
    }
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(audit, sort_keys=True))


if __name__ == "__main__":
    main()
