from __future__ import annotations

from pathlib import Path

import apply_ninety_seventh_pass_repairs as pass97
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """theorem advanced_claims_ii_paper_i2_precision_raised_multiplier_value :
    AdvancedClaimsIIPaperI2PrecisionRaisedMultiplier = 5 := by
  native_decide
""",
        """theorem advanced_claims_ii_paper_i2_precision_raised_multiplier_value :
    AdvancedClaimsIIPaperI2PrecisionRaisedMultiplier = 5 := by
  norm_num [AdvancedClaimsIIPaperI2PrecisionRaisedMultiplier,
    AdvancedClaimsIIPaperI2Prime, AdvancedClaimsIIPaperI2Precision]
""",
        1,
        "Mock1Advanced prove the raised multiplier value in the kernel",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """theorem advanced_claims_ii_paper_i2_precision_raised_unit_counterexample :
    Not
      (FiniteCongruenceMod AdvancedClaimsIIPaperI2Prime
        AdvancedClaimsIIPaperI2Precision
        (AdvancedClaimsIIPaperI2PrecisionRaisedMultiplier * 1) 1) := by
  native_decide
""",
        """theorem advanced_claims_ii_paper_i2_precision_raised_unit_counterexample :
    Not
      (FiniteCongruenceMod AdvancedClaimsIIPaperI2Prime
        AdvancedClaimsIIPaperI2Precision
        (AdvancedClaimsIIPaperI2PrecisionRaisedMultiplier * 1) 1) := by
  norm_num [FiniteCongruenceMod, IntCongruent, PrimePower,
    AdvancedClaimsIIPaperI2Prime, AdvancedClaimsIIPaperI2Precision,
    AdvancedClaimsIIPaperI2PrecisionRaisedMultiplier]
""",
        1,
        "Mock1Advanced prove the raised-unit counterexample without native_decide",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """          (matrixWedge (-matrixWedge g.pureGauge g.inverse) A) g.forward := by
      rw [g.differential_inverse]
""",
        """          (matrixWedge (-matrixWedge g.pureGauge g.inverse) A) g.forward := by
      rw [g.differential_inverse]
      unfold pureGauge
""",
        1,
        "Mock2 unfold pureGauge after rewriting the inverse derivative",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """      matrixWedge (-matrixWedge g.pureGauge g.inverse)
        (matrixDifferential g.forward) := by
      rw [g.differential_inverse]
""",
        """      matrixWedge (-matrixWedge g.pureGauge g.inverse)
        (matrixDifferential g.forward) := by
      rw [g.differential_inverse]
      unfold pureGauge
""",
        1,
        "Mock2 unfold pureGauge in the differential summand",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    _ = -matrixWedge g.pureGauge g.pureGauge +
          matrixWedge g.inverse 0 := by
      rw [g.inverseDerivative_differential_term,
        matrixDifferential_squared] <;> rfl
""",
        """    _ = -matrixWedge g.pureGauge g.pureGauge +
          matrixWedge g.inverse (0 : Omega X 2 U) := by
      rw [g.inverseDerivative_differential_term,
        matrixDifferential_squared]
""",
        1,
        "Mock2 pin the degree of the zero two-form in Maurer-Cartan",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  simpa using
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
""",
        """  simpa only [Function.comp_apply] using
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
""",
        1,
        "Mock2Advanced normalize reciprocal-Gamma composition",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    simpa using
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
""",
        """    simpa only [Function.comp_apply] using
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
""",
        1,
        "Mock2Advanced normalize the real power composition",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    simpa using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
""",
        """    simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
""",
        1,
        "Mock2Advanced normalize the complex cast composition",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  simpa [citedMockOneNormalization] using
    (hpowC.mul invGamma_tendsto_zero).mul_const
      (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
""",
        """  change Tendsto
    (fun ε : ℝ =>
      ((((4 * Real.pi) ^ (-ε) : ℝ) : ℂ) *
        (Complex.Gamma (ε : ℂ))⁻¹) *
          (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    (𝓝 0) (𝓝 0)
  exact (hpowC.mul invGamma_tendsto_zero).mul_const
    (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
""",
        1,
        "Mock2Advanced expose the Mock-I normalization limit function",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """      (Complex.measurable_re measurableSet_singleton).nullMeasurableSet
""",
        """      (Complex.measurable_re
        (measurableSet_singleton a)).nullMeasurableSet
""",
        1,
        "FunctionalAnalysis instantiate the measurable singleton",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  exact ModularGroup.isOpen_fdo.preimage (continuous_sl2z_smul g⁻¹)
""",
        """  exact ModularGroup.isOpen_fdo.preimage
    (HalfIntegralMultiplier.continuous_sl2z_smul g⁻¹)
""",
        1,
        "FunctionalAnalysis qualify continuity of the integral modular action",
    )
    changed |= did

    old_countable = """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
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
"""
    new_countable = """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  Countable.of_injective
    (fun γ : SL(2, ℤ) =>
      ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
       (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
       (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
       (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1))
    (by
      intro a b h
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all)
"""
    text, did = replace_exact(
        text, old_countable, new_countable, 1,
        "FunctionalAnalysis construct SL2Z countability by an explicit injection")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass97.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
