from __future__ import annotations

from pathlib import Path

import apply_one_hundred_forty_second_pass_repairs as pass142
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """        dlogFrame U := by
  simp [nablaTensorId]
""",
            """        dlogFrame U := by
  simp only [nablaTensorId, LinearMap.comp_apply, TensorProduct.map_tmul,
    nablaQFactor_apply, leftTensorReassociate_tmul]
""",
            1,
            "Mock2 evaluate nabla tensor identity on pure tensors explicitly",
        ),
        (
            """        dlogFrame U := by
  simp [idTensorDq]
""",
            """        dlogFrame U := by
  simp only [idTensorDq, LinearMap.comp_apply, TensorProduct.map_tmul,
    dQFactor_apply, rightTensorReassociate_tmul]
""",
            1,
            "Mock2 evaluate logarithmic tensor derivative on pure tensors explicitly",
        ),
        (
            """    apply TensorProduct.ext'
    intro l m
    simp only [LinearMap.comp_apply, potentialCoefficient_tmul,
      tensorRestriction_tmul]
    rw [pointwiseOperator_restrict]
""",
            """    apply TensorProduct.ext'
    intro l m
    change
      tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
          (pointwiseOperator P.qPotential V l ⊗ₜ[ℂ] m) =
        pointwiseOperator P.qPotential U
            ((locallyConstantLinearPresheaf E).res hUV l) ⊗ₜ[ℂ]
          ((locallyConstantLinearPresheaf F).res hUV m)
    rw [tensorRestriction_tmul, pointwiseOperator_restrict]
""",
            1,
            "Mock2 expose potential-coefficient restrictions on pure tensors",
        ),
        (
            """    apply TensorProduct.ext'
    intro l m
    simp only [LinearMap.comp_apply, logRadialCoefficient_tmul,
      tensorRestriction_tmul]
    rw [pointwiseOperator_restrict]
""",
            """    apply TensorProduct.ext'
    intro l m
    change
      tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
          (l ⊗ₜ[ℂ] pointwiseOperator P.logDerivative V m) =
        ((locallyConstantLinearPresheaf E).res hUV l) ⊗ₜ[ℂ]
          pointwiseOperator P.logDerivative U
            ((locallyConstantLinearPresheaf F).res hUV m)
    rw [tensorRestriction_tmul, pointwiseOperator_restrict]
""",
            1,
            "Mock2 expose logarithmic-coefficient restrictions on pure tensors",
        ),
        (
            """  calc
    tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV (localCoefficient P V z) =
        tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
            (logRadialCoefficient P V z + potentialCoefficient P V z) := by
      rw [localCoefficient_apply]
    _ = tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
            (logRadialCoefficient P V z) +
        tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
            (potentialCoefficient P V z) :=
      (tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV).map_add _ _
    _ = logRadialCoefficient P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) +
        potentialCoefficient P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) := by
      rw [logRadialCoefficient_restrict, potentialCoefficient_restrict]
    _ = localCoefficient P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) :=
      (localCoefficient_apply P U _).symm
""",
            """  rw [localCoefficient_apply, LinearMap.map_add,
    logRadialCoefficient_restrict, potentialCoefficient_restrict,
    localCoefficient_apply]
""",
            1,
            "Mock2 prove local-coefficient restriction by linearity",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  rw [hterm] at h
  exact h
""",
            """  rw [hterm, normalization_factor, one_mul] at h
  exact h
""",
            1,
            "Mock2Advanced remove the concrete unit normalization from the selected mode",
        ),
        (
            """(hmean : ∀ k,""",
            """(hmean : ∀ k : ℕ,""",
            4,
            "Mock2Advanced type every mean-square block index as natural",
        ),
        (
            """(hupper : ∀ k,""",
            """(hupper : ∀ k : ℕ,""",
            2,
            "Mock2Advanced type every linear upper-bound index as natural",
        ),
        (
            """(hlower : ∀ k,""",
            """(hlower : ∀ k : ℕ,""",
            2,
            "Mock2Advanced type every lower-profile index as natural",
        ),
        (
            """(hindex : ∀ k m,""",
            """(hindex : ∀ (k m : ℕ),""",
            3,
            "Mock2Advanced type every block-localization index as natural",
        ),
        (
            """    _ ≤ testValue * (coefficientFloor * growth m) + ε :=
      add_le_add_right (mul_le_mul_of_nonneg_right htest hcg) ε
""",
            """    _ ≤ testValue * (coefficientFloor * growth m) + ε := by
      nlinarith [mul_le_mul_of_nonneg_right htest hcg]
""",
            1,
            "Mock2Advanced normalize right-added test-floor inequality",
        ),
        (
            """    _ ≤ testValue * coefficient m ^ 2 + error m :=
      add_le_add_left (hmass m) _
""",
            """    _ ≤ testValue * coefficient m ^ 2 + error m := by
      nlinarith [hmass m]
""",
            1,
            "Mock2Advanced normalize the mass-error addition order",
        ),
        (
            """  rw [map_sub, LinearMap.congr_fun P.idempotent φ]
  exact sub_self _
""",
            """  rw [map_sub, LinearMap.congr_fun P.idempotent φ]
  abel_nf
""",
            1,
            "Mock2Advanced close the polar-kernel identity additively",
        ),
        (
            """∑ n in Finset.range (N + 1), a n""",
            """∑ n ∈ Finset.range (N + 1), a n""",
            1,
            "Mock2Advanced update partial energy finite-sum syntax",
        ),
        (
            """∑ n in Finset.range N, term n""",
            """∑ n ∈ Finset.range N, term n""",
            2,
            "Mock2Advanced update finite vector-sum syntax",
        ),
        (
            """∑ n in Finset.range N, ‖term n‖""",
            """∑ n ∈ Finset.range N, ‖term n‖""",
            1,
            "Mock2Advanced update finite norm-sum syntax",
        ),
        (
            """∑ n in Finset.range N, majorant n""",
            """∑ n ∈ Finset.range N, majorant n""",
            1,
            "Mock2Advanced update finite majorant-sum syntax",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  ext z
  simp only [Function.mem_support, inverseEtaRatio, div_ne_zero_iff,
    inverseEtaSection_apply_ne_zero, and_true]
""",
            """  ext z
  simp only [Function.mem_support, inverseEtaRatio, div_ne_zero_iff]
  constructor
  · exact And.left
  · intro hz
    exact ⟨hz, inverseEtaSection_apply_ne_zero z⟩
""",
            1,
            "FunctionalAnalysis prove inverse-eta support equivalence directly",
        ),
        (
            """  rw [hγ z, SmoothCompactCore.covariance u γ z,
    WeightSection.covariance inverseEtaSection γ z]
  exact mul_div_mul_left _ _
    (inverseEtaPaperCertificate.multiplier.factor_ne_zero γ z)
""",
            """  rw [hγ z, SmoothCompactCore.covariance u γ z]
  have heta := WeightSection.covariance inverseEtaSection γ z
  change
    inverseEtaPaperCertificate.multiplier.factor γ z *
          SmoothCompactCore.toSection u z /
        inverseEtaSection (γ • z) =
      SmoothCompactCore.toSection u z / inverseEtaSection z
  rw [heta]
  exact mul_div_mul_left _ _
    (inverseEtaPaperCertificate.multiplier.factor_ne_zero γ z)
""",
            1,
            "FunctionalAnalysis rewrite inverse-eta covariance after exposing coercions",
        ),
        (
            """  · intro hz
    refine ⟨_, ?_, rfl⟩
    simpa only [Function.mem_support, inverseEtaRatioQuotient_mk] using hz
  · rintro ⟨w, hw, hEq⟩
    have hw' : inverseEtaRatioQuotient u
        (gammaTwoQuotientMk w) ≠ 0 := by
      simpa only [Function.mem_support, inverseEtaRatioQuotient_mk] using hw
    rwa [hEq] at hw'
""",
            """  · intro hz
    refine ⟨_, ?_, rfl⟩
    change inverseEtaRatio u _ ≠ 0 at hz
    exact hz
  · rintro ⟨w, hw, hEq⟩
    change inverseEtaRatio u w ≠ 0 at hw
    have hw' : inverseEtaRatioQuotient u
        (gammaTwoQuotientMk w) ≠ 0 := by
      change inverseEtaRatio u w ≠ 0
      exact hw
    rwa [hEq] at hw'
""",
            1,
            "FunctionalAnalysis compare quotient support definitionally",
        ),
        (
            """  map_add' u v := by
    apply CompactlySupportedContinuousMap.ext
    intro q
    induction q using Quotient.inductionOn'
    simp only [inverseEtaQuotientScalar_mk,
      SmoothCompactCore.add_apply,
      CompactlySupportedContinuousMap.add_apply, add_div]
""",
            """  map_add' u v := by
    apply CompactlySupportedContinuousMap.ext
    intro q
    induction q using Quotient.inductionOn'
    change
      SmoothCompactCore.toSection (u + v) _ / inverseEtaSection _ =
        SmoothCompactCore.toSection u _ / inverseEtaSection _ +
          SmoothCompactCore.toSection v _ / inverseEtaSection _
    rw [SmoothCompactCore.add_apply, add_div]
""",
            1,
            "FunctionalAnalysis prove quotient scalar additivity on representatives",
        ),
        (
            """  map_smul' c u := by
    apply CompactlySupportedContinuousMap.ext
    intro q
    induction q using Quotient.inductionOn'
    simp only [inverseEtaQuotientScalar_mk,
      SmoothCompactCore.smul_apply,
      CompactlySupportedContinuousMap.smul_apply,
      smul_eq_mul, mul_div_assoc]
""",
            """  map_smul' c u := by
    apply CompactlySupportedContinuousMap.ext
    intro q
    induction q using Quotient.inductionOn'
    change
      SmoothCompactCore.toSection (c • u) _ / inverseEtaSection _ =
        c * (SmoothCompactCore.toSection u _ / inverseEtaSection _)
    rw [SmoothCompactCore.smul_apply]
    ring
""",
            1,
            "FunctionalAnalysis prove quotient scalar homogeneity on representatives",
        ),
    ])


def main() -> int:
    pass142.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
