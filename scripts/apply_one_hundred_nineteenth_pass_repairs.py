from __future__ import annotations

from pathlib import Path

import apply_one_hundred_eighteenth_pass_repairs as pass118
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


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass,
      List.mem_cons]
""",
            """  cases r <;> decide
""",
            1,
            "Mock1Advanced compute the exhaustive finite evidence partition",
        ),
        (
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  intro h
  have hm : List.Mem objectClaimRegistry finiteExactRequirements := by
    simp [finiteExactRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute finite-exact bucket nonemptiness",
        ),
        (
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  intro h
  have hm : List.Mem completionShadowHolomorphicConsequence
      analyticBoundaryRequirements := by
    simp [analyticBoundaryRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute analytic-boundary bucket nonemptiness",
        ),
        (
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  intro h
  have hm : List.Mem regressionCardySkeleton
      diagnosticMetadataRequirements := by
    simp [diagnosticMetadataRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute diagnostic bucket nonemptiness",
        ),
        (
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  intro h
  have hm : List.Mem namedConcretePaperInstance aggregateRequirements := by
    simp [aggregateRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute aggregate bucket nonemptiness",
        ),
        (
            """                (AdvancedClaimsIISectionFormulaStatementBridgeCertificate.padic_obstruction_failure_formula_at S)))))))
  entropy_atoms := by
""",
            """                (AdvancedClaimsIISectionFormulaStatementBridgeCertificate.padic_obstruction_failure_formula_at S))))))
  entropy_atoms := by
""",
            1,
            "Mock1Advanced remove the extra closing parenthesis before entropy atoms",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """  obj : TopologicalSpace.Opens X → ModuleCat ℂ
""",
            """  obj : TopologicalSpace.Opens X → ModuleCat.{0} ℂ
""",
            1,
            "Mock2 fix the carrier universe of the module-valued presheaf",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  have hfun :
      (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) =
        smoothTentAutocorrelationScale T hT •
          (fun x : ℝ => (smoothTentAutocorrelationRaw T hT x : ℂ)) := by
    funext x
    simp [fourierPositiveSmoothTentFunction]
  rw [hfun, FourierTransform.fourier_smul,
    fourier_smoothTentAutocorrelationRaw_eq_normSq T hT ξ]
  simp [smul_eq_mul, Complex.ofReal_mul]
""",
            """  rw [← normalizedFourier_eq_mathlib
    (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ]
  calc
    normalizedFourier
          (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ =
        (smoothTentAutocorrelationScale T hT : ℂ) *
          normalizedFourier
            (fun x : ℝ => (smoothTentAutocorrelationRaw T hT x : ℂ)) ξ := by
      simp only [normalizedFourier, fourierPositiveSmoothTentFunction,
        Complex.ofReal_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ((smoothTentAutocorrelationScale T hT *
          Complex.normSq
            (𝓕 (fun x : ℝ => (narrowSmoothTentFunction T hT x : ℂ)) ξ) : ℝ) : ℂ) := by
      rw [normalizedFourier_eq_mathlib,
        fourier_smoothTentAutocorrelationRaw_eq_normSq T hT ξ,
        Complex.ofReal_mul]
""",
            1,
            "Mock2Advanced prove Fourier scaling directly from the integral convention",
        ),
        (
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    simpa [profileBesselConvention, Convention.normalizedKernel] using
      ((Complex.continuous_ofReal.comp
        (TentKernel.continuous_profile 1)).mul continuous_const).aestronglyMeasurable
""",
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    change AEStronglyMeasurable
      (fun t : ℝ =>
        (TentKernel.profile 1 t : ℂ) * (besselEnvelope x : ℂ)) volume
    simpa only [Function.comp_apply, Pi.mul_apply] using
      ((Complex.continuous_ofReal.comp
        (TentKernel.continuous_profile 1)).mul continuous_const).aestronglyMeasurable
""",
            1,
            "Mock2Advanced normalize the measurable kernel function expression",
        ),
        (
            """    exact mul_le_mul_of_nonneg_right hprofile1 hbessel
""",
            """    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hprofile1 hbessel)
""",
            1,
            "Mock2Advanced normalize the unit envelope bound",
        ),
        (
            """  rw [hentry, Int.natAbs_eq_iff_sq_eq]
  simp only [pow_two]
""",
            """  rw [hentry]
  apply (Int.natAbs_eq_iff_mul_self_eq).2
""",
            1,
            "Mock2Advanced use the natAbs product-square equivalence available in the pinned Mathlib",
        ),
        (
            """  finite_measure : ∀ n, μ (set n) ≠ (⊤ : ℝ≥0∞)
""",
            """  finite_measure : ∀ n, μ (set n) ≠ (⊤ : ENNReal)
""",
            1,
            "Mock2Advanced avoid unsupported compact ENNReal notation in a structure field",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """      have hinside :
          1 - ((2 * (z : ℂ).re) / 2) ^ 2 = (z : ℂ).im ^ 2 := by
        nlinarith [himSq]
      rw [hinside, Real.sqrt_sq_eq_abs, abs_of_pos z.im_pos]
""",
            """      have himSq' : z.im ^ 2 = 1 - z.re ^ 2 := by
        exact himSq
      have hinside :
          1 - ((2 * z.re) / 2) ^ 2 = z.im ^ 2 := by
        nlinarith [himSq']
      rw [hinside, Real.sqrt_sq_eq_abs, abs_of_pos z.im_pos]
""",
            1,
            "FunctionalAnalysis state the circular square identity in the exact edge goal language",
        ),
        (
            """    have hbaseSq :
        (Real.sqrt (3 : ℝ) / 2) ^ 2 ≤ z.im ^ 2 := by
      rw [hre] at hnormLower
      nlinarith
""",
            """    have hbaseSq :
        (Real.sqrt (3 : ℝ) / 2) ^ 2 ≤ z.im ^ 2 := by
      change (Real.sqrt (3 : ℝ) / 2) ^ 2 ≤ (z : ℂ).im ^ 2
      rw [hre] at hnormLower
      nlinarith [hsqrtSq]
""",
            2,
            "FunctionalAnalysis keep both vertical square bounds in the coerced complex carrier",
        ),
        (
            """      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.ext_iff]
""",
            """      simp only [GammaTwoModularTileEdge.pairingMatrix,
        GammaTwoModularTileEdge.paired,
        GammaTwoModularTileEdge.pairedParameter, modularTileEdgeParam]
      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.ext_iff]
""",
            1,
            "FunctionalAnalysis unfold the circular pairing enum before applying the S formula",
        ),
        (
            """      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.ext_iff]
      simp [modularLeftVerticalParam, modularRightVerticalParam,
        UpperHalfPlane.coe_vadd]
""",
            """      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.ext_iff]
      apply Complex.ext <;>
        norm_num [modularLeftVerticalParam, modularRightVerticalParam,
          UpperHalfPlane.coe_vadd]
""",
            1,
            "FunctionalAnalysis prove the left vertical pairing componentwise",
        ),
        (
            """      rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.ext_iff]
      simp [modularLeftVerticalParam, modularRightVerticalParam,
        UpperHalfPlane.coe_vadd]
""",
            """      rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.ext_iff]
      apply Complex.ext <;>
        norm_num [modularLeftVerticalParam, modularRightVerticalParam,
          UpperHalfPlane.coe_vadd]
""",
            1,
            "FunctionalAnalysis prove the right vertical pairing componentwise",
        ),
    ])


def main() -> int:
    pass118.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
