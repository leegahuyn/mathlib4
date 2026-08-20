from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fourth_pass_repairs as pass104
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """theorem advanced_claims_ii_paper_i2_extrapolated_not_in_precision_tube
    (i : Fin 5) :
    Not
      (AdvancedClaimsIIPaperI2PrecisionTube
        (AdvancedClaimsIIPaperI2ExtrapolatedValue i)) := by
  fin_cases i <;> native_decide
""",
            """theorem advanced_claims_ii_paper_i2_extrapolated_not_in_precision_tube
    (i : Fin 5) :
    Not
      (AdvancedClaimsIIPaperI2PrecisionTube
        (AdvancedClaimsIIPaperI2ExtrapolatedValue i)) := by
  fin_cases i <;>
    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
      AdvancedClaimsIIPaperI2ExtrapolatedValue,
      AdvancedClaimsIIPaperI2ExtrapolatedIndex,
      AdvancedClaimsIIPaperI2MahlerEval,
      AdvancedClaimsIIPaperI2MahlerRawEval,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      mahlerBinomialBasis, FiniteCongruenceMod, IntCongruent,
      PrimePower, AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision]
""",
            "Mock1Advanced prove the five precision-tube failures by integer arithmetic",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_coefficient_is_forward_difference_residue
    (j : Fin 6) :
    AdvancedClaimsIIPaperI2MahlerCoefficient j =
      AdvancedClaimsIIPaperI2ForwardDifferenceResidue j := by
  fin_cases j <;> native_decide
""",
            """theorem advanced_claims_ii_paper_i2_coefficient_is_forward_difference_residue
    (j : Fin 6) :
    AdvancedClaimsIIPaperI2MahlerCoefficient j =
      AdvancedClaimsIIPaperI2ForwardDifferenceResidue j := by
  fin_cases j <;>
    norm_num [AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifferenceResidue,
      AdvancedClaimsIIPaperI2ForwardDifference,
      AdvancedClaimsIIPaperI2NormalizedValue,
      PrimePower, AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision]
""",
            "Mock1Advanced prove the six forward-difference residue equalities",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_coefficient_congruent_forward_difference
    (j : Fin 6) :
    FiniteCongruenceMod AdvancedClaimsIIPaperI2Prime
      AdvancedClaimsIIPaperI2Precision
      (AdvancedClaimsIIPaperI2MahlerCoefficient j)
      (AdvancedClaimsIIPaperI2ForwardDifference (j : Nat)) := by
  fin_cases j <;> native_decide
""",
            """theorem advanced_claims_ii_paper_i2_coefficient_congruent_forward_difference
    (j : Fin 6) :
    FiniteCongruenceMod AdvancedClaimsIIPaperI2Prime
      AdvancedClaimsIIPaperI2Precision
      (AdvancedClaimsIIPaperI2MahlerCoefficient j)
      (AdvancedClaimsIIPaperI2ForwardDifference (j : Nat)) := by
  fin_cases j <;>
    norm_num [FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime, AdvancedClaimsIIPaperI2Precision,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifference,
      AdvancedClaimsIIPaperI2NormalizedValue]
""",
            "Mock1Advanced prove the six Mahler congruences by integer arithmetic",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """theorem gammaLower_mem_Gamma2 : gammaLower ∈ Gamma2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [gammaLower]
""",
            """theorem gammaLower_mem_Gamma2 : gammaLower ∈ Gamma2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gammaLower]
""",
            "Mock2 verify the lower-unipotent matrix entrywise modulo two",
        ),
        (
            """theorem gammaLower_smul_I_im :
    (gammaLower • UpperHalfPlane.I).im = (1 / 5 : ℝ) := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  norm_num [ModularGroup.denom_apply, gammaLower, Complex.normSq]
""",
            """theorem gammaLower_smul_I_im :
    (gammaLower • UpperHalfPlane.I).im = (1 / 5 : ℝ) := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  change (1 : ℝ) / Complex.normSq (2 * Complex.I + 1) = 1 / 5
  norm_num [Complex.normSq]
""",
            "Mock2 compute the lower-unipotent denominator at i explicitly",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """theorem invGamma_tendsto_zero :
    Tendsto
        (fun ε : ℝ => (Complex.Gamma (ε : ℂ))⁻¹)
        (𝓝 0) (𝓝 0) := by
  have hcontinuous : Continuous (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  convert
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
    using 1 <;> rfl
""",
            """theorem invGamma_tendsto_zero :
    Tendsto
        (fun ε : ℝ => (Complex.Gamma (ε : ℂ))⁻¹)
        (𝓝 0) (𝓝 0) := by
  have hcontinuous : Continuous (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  have hzero : (Complex.Gamma (0 : ℂ))⁻¹ = 0 := by
    simpa using
      (Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (0 : ℂ))
  simpa [Function.comp_apply, hzero] using
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
""",
            "Mock2Advanced identify the reciprocal-Gamma value at zero",
        ),
        (
            """  have hpowR :
      Tendsto (fun ε : ℝ => (4 * Real.pi : ℝ) ^ (-ε))
        (𝓝 0) (𝓝 1) := by
    convert
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
      using 1 <;> rfl
""",
            """  have hpowR :
      Tendsto (fun ε : ℝ => (4 * Real.pi : ℝ) ^ (-ε))
        (𝓝 0) (𝓝 1) := by
    simpa [Function.comp_apply] using
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
""",
            "Mock2Advanced simplify the negative-exponent base value at zero",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  (show Function.Injective
      (fun γ : SL(2, ℤ) =>
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) from by
      intro a b h
      apply Subtype.ext
      exact h).countable
""",
            """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  (show Function.Injective
      (fun γ : SL(2, ℤ) =>
        ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) from by
      intro a b h
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all).countable
""",
            1,
            "FunctionalAnalysis encode SL2Z in a countable four-entry product",
        ),
        (
            """      (Quotient.mk' : ℍ → GammaTwoQuotient) ⁻¹'
          ((Quotient.mk' : ℍ → GammaTwoQuotient) '' A) =
""",
            """      (Quotient.mk'' : ℍ → GammaTwoQuotient) ⁻¹'
          ((Quotient.mk'' : ℍ → GammaTwoQuotient) '' A) =
""",
            2,
            "FunctionalAnalysis use the orbit-relation quotient constructor",
        ),
        (
            """    have hAne : A.Nonempty :=
      gammaTwoQuotientMk_isOpenQuotientMap.surjective
        .nonempty_preimage.mpr hUne
""",
            """    have hAne : A.Nonempty :=
      (gammaTwoQuotientMk_isOpenQuotientMap.surjective.nonempty_preimage).mpr hUne
""",
            1,
            "FunctionalAnalysis parenthesize the nonempty-preimage equivalence",
        ),
        (
            """def descendInvariant {E : Type*} (ρ : ℍ → E)
""",
            """noncomputable def descendInvariant {E : Type*} (ρ : ℍ → E)
""",
            1,
            "FunctionalAnalysis mark quotient descent noncomputable",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass104.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
