#!/usr/bin/env python3
"""Apply the additive-first structural repair to the verified 4-error FA source.

The patch keeps the existing public theorem names and mathematical conclusions.
It avoids elaborating concrete bundled-map subtraction and avoids rewriting
`inner_sub_right` on the large graph-completion L² type.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

SOURCE = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
EXPECTED_INPUT_SHA256 = "1c3d12594a3e8b14f9cf7b7294da7c29221758c72d00a596215198f7623fad8c"
EXPECTED_OUTPUT_SHA256 = "8922c3465fca807d2b34e8432c3e9704e9ab98303d4b414eabc12fa1d553ee72"
START = "/-- Pointwise splitting of full multiplication into hard and tail parts,\n"
MIDDLE = "theorem norm_discriminantHardStageOperator_sub_graphPotential_le"
END = "/-- Final P5 endpoint:"

NEW_SPLIT = r'''/-- A generic subtraction wrapper whose additive instance is synthesized before
substituting the large index-dependent graph-completion type.  It is reducible,
so existing consumers see the original operator subtraction definitionally. -/
@[reducible] noncomputable def weakAntiOperatorSubFrozen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) : WeakAntiOperator E :=
  A - B

@[simp]
theorem weakAntiOperatorSubFrozen_apply_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) (u v : E) :
    weakAntiOperatorSubFrozen A B u v = A u v - B u v :=
  rfl

/-- Reversing a difference does not change the operator norm.  Keeping this
lemma generic prevents WHNF expansion of the concrete completion abbreviation. -/
theorem norm_sub_rev_eq_norm_weakAntiOperatorSubFrozen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) :
    ‖B - A‖ = ‖weakAntiOperatorSubFrozen A B‖ := by
  simpa only [weakAntiOperatorSubFrozen] using (norm_sub_rev B A)

/-- Generic additivity of the inner product in its second argument. -/
theorem inner_add_right_frozen
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y z : E) :
    inner ℂ x (y + z) = inner ℂ x y + inner ℂ x z :=
  inner_add_right x y z

/-- Full carrier multiplication is the sum of hard and tail multiplication. -/
theorem discriminantFullCarrierMul_eq_hard_add_tail_frozen
    (N : ℕ) (n : ℤ) (u : GraphSobolevCompletion n) :
    (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
        OrbitEuclideanL2 n) =
      (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n) +
      (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n) := by
  apply Lp.ext
  filter_upwards [
    coeFn_discriminantFullCarrierWeightLp,
    coeFn_discriminantHardCarrierWeightLp N,
    coeFn_discriminantTailCarrierWeightLp N,
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      discriminantFullCarrierWeightLp (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantHardCarrierWeightLp N) (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantTailCarrierWeightLp N) (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_add
      (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n)
      (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n)] with
      z hfull hhard htail hfullmul hhardmul htailmul hadd
  rw [hfullmul, hadd, Pi.add_apply, hhardmul, htailmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfull, hhard, htail, discriminantFull_eq_hard_add_tail]
  ring

/-- The full carrier multiplier minus the hard multiplier agrees pointwise
with the tail multiplier.  The L² addition is established before scalar
subtraction, avoiding concrete `inner_sub_right` normalization. -/
theorem weightedFull_sub_weightedHard_apply_apply_eq_weightedTail
    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) :
    weakAntiOperatorSubFrozen
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n) u v =
      weightedGraphOperator n (discriminantTailCarrierWeightLp N) u v := by
  rw [weakAntiOperatorSubFrozen_apply_apply]
  rw [congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (discriminantHardStageOperator_eq_weightedHard N n)]
  simp only [weightedGraphOperator, LinearMap.mkContinuous₂_apply,
    weightedGraphLinear, lpInfinityMultiplier_apply]
  have hmul := discriminantFullCarrierMul_eq_hard_add_tail_frozen N n u
  have hinner :
      inner ℂ (graphEuclideanBase n v)
          (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
            OrbitEuclideanL2 n) =
        inner ℂ (graphEuclideanBase n v)
            (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n) +
          inner ℂ (graphEuclideanBase n v)
            (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n) := by
    calc
      inner ℂ (graphEuclideanBase n v)
          (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
            OrbitEuclideanL2 n) =
        inner ℂ (graphEuclideanBase n v)
          ((discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n) +
            (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n)) :=
        congrArg
          (fun w : OrbitEuclideanL2 n ↦
            inner ℂ (graphEuclideanBase n v) w) hmul
      _ = _ := inner_add_right_frozen _ _ _
  rw [hinner]
  ring

/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator.  The public name is preserved and the
wrapper is reducible to the original subtraction. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail (N : ℕ) (n : ℤ) :=
  show weakAntiOperatorSubFrozen
      (weightedGraphOperator n discriminantFullCarrierWeightLp)
      (discriminantHardStageOperator N n) =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) from by
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact weightedFull_sub_weightedHard_apply_apply_eq_weightedTail N n u v

'''

NEW_NORM = r'''theorem norm_discriminantHardStageOperator_sub_graphPotential_le
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

OLD_FINAL = '''    (fun N ↦ by
      simpa only [discriminantHardStageOperator] using
        norm_discriminantHardStageOperator_sub_graphPotential_le N n)'''
NEW_FINAL = '''    (fun N ↦ by
      exact norm_discriminantHardStageOperator_sub_graphPotential_le N n)'''


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--audit", type=Path)
    args = parser.parse_args()

    before = args.source.read_bytes()
    before_sha = digest(before)
    if before_sha != EXPECTED_INPUT_SHA256:
        raise SystemExit(
            f"input source mismatch: expected {EXPECTED_INPUT_SHA256}, got {before_sha}"
        )
    text = before.decode("utf-8")
    if text.count(START) != 1 or text.count(MIDDLE) != 1 or text.count(END) != 1:
        raise SystemExit("source markers are not unique")

    start = text.index(START)
    middle = text.index(MIDDLE, start)
    end = text.index(END, middle)
    patched = text[:start] + NEW_SPLIT + NEW_NORM + text[end:]
    if patched.count(OLD_FINAL) != 1:
        raise SystemExit("final compactness conversion marker is not unique")
    patched = patched.replace(OLD_FINAL, NEW_FINAL, 1)
    payload = patched.encode("utf-8")
    output_sha = digest(payload)
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise SystemExit(
            f"deterministic output mismatch: expected {EXPECTED_OUTPUT_SHA256}, got {output_sha}"
        )

    output = args.output or args.source
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(payload)

    audit = {
        "schema": "gpt-fa-primary4016-additive-full-patch-v1",
        "input_sha256": before_sha,
        "output_sha256": output_sha,
        "input_bytes": len(before),
        "output_bytes": len(payload),
        "input_lines": len(text.splitlines()),
        "output_lines": len(patched.splitlines()),
        "source_path": str(args.source),
        "output_path": str(output),
        "public_theorem_names_preserved": [
            "weightedFull_sub_weightedHard_eq_weightedTail",
            "norm_discriminantHardStageOperator_sub_graphPotential_le",
            "graphPotentialOperator_isCompact_unconditional",
        ],
        "new_helpers": [
            "weakAntiOperatorSubFrozen",
            "weakAntiOperatorSubFrozen_apply_apply",
            "norm_sub_rev_eq_norm_weakAntiOperatorSubFrozen",
            "inner_add_right_frozen",
            "discriminantFullCarrierMul_eq_hard_add_tail_frozen",
            "weightedFull_sub_weightedHard_apply_apply_eq_weightedTail",
        ],
        "theorem_conclusions_weakened": False,
        "new_assumptions": False,
        "forbidden_constructs_added": False,
    }
    if args.audit:
        args.audit.parent.mkdir(parents=True, exist_ok=True)
        args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
