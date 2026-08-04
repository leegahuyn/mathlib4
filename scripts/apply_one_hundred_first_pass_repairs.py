from __future__ import annotations

from pathlib import Path

import apply_one_hundredth_pass_repairs as pass100
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")

    old = """theorem advanced_claims_ii_paper_i2_extrapolated_not_in_precision_tube
    (i : Fin 5) :
    Not
      (AdvancedClaimsIIPaperI2PrecisionTube
        (AdvancedClaimsIIPaperI2ExtrapolatedValue i)) := by
  fin_cases i <;>
    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
      FiniteCongruenceMod, IntCongruent,
      AdvancedClaimsIIPaperI2ExtrapolatedValue,
      AdvancedClaimsIIPaperI2ExtrapolatedIndex,
      AdvancedClaimsIIPaperI2MahlerEval,
      AdvancedClaimsIIPaperI2MahlerRawEval,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      mahlerBinomialBasis, PrimePower,
      AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision]
"""
    new = """theorem advanced_claims_ii_paper_i2_extrapolated_not_in_precision_tube
    (i : Fin 5) :
    Not
      (AdvancedClaimsIIPaperI2PrecisionTube
        (AdvancedClaimsIIPaperI2ExtrapolatedValue i)) := by
  fin_cases i
  · intro h
    have hv : AdvancedClaimsIIPaperI2ExtrapolatedValue (0 : Fin 5) = 9 := by decide
    rw [hv] at h
    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
      FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision] at h
  · intro h
    have hv : AdvancedClaimsIIPaperI2ExtrapolatedValue (1 : Fin 5) = 1 := by decide
    rw [hv] at h
    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
      FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision] at h
  · intro h
    have hv : AdvancedClaimsIIPaperI2ExtrapolatedValue (2 : Fin 5) = 7 := by decide
    rw [hv] at h
    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
      FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision] at h
  · intro h
    have hv : AdvancedClaimsIIPaperI2ExtrapolatedValue (3 : Fin 5) = 14 := by decide
    rw [hv] at h
    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
      FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision] at h
  · intro h
    have hv : AdvancedClaimsIIPaperI2ExtrapolatedValue (4 : Fin 5) = 24 := by decide
    rw [hv] at h
    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
      FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision] at h
"""
    text, changed = replace_exact(
        text, old, new, 1,
        "Mock1Advanced prove each extrapolated residue is nonzero modulo 25",
    )
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    matrixWedge (matrixWedge (matrixDifferential g.inverse) A) g.forward =
        matrixWedge
          (matrixWedge (-matrixWedge g.pureGauge g.inverse) A) g.forward := by
      rw [g.differential_inverse]
      unfold pureGauge
""",
            """    matrixWedge (matrixWedge (matrixDifferential g.inverse) A) g.forward =
        matrixWedge
          (matrixWedge (-matrixWedge g.pureGauge g.inverse) A) g.forward := by
      rw [g.differential_inverse]
      unfold pureGauge
      rfl
""",
            "Mock2 close the inverse-derivative conjugate rewrite reflexively",
        ),
        (
            """    matrixWedge (matrixDifferential g.inverse)
        (matrixDifferential g.forward) =
      matrixWedge (-matrixWedge g.pureGauge g.inverse)
        (matrixDifferential g.forward) := by
      rw [g.differential_inverse]
      unfold pureGauge
""",
            """    matrixWedge (matrixDifferential g.inverse)
        (matrixDifferential g.forward) =
      matrixWedge (-matrixWedge g.pureGauge g.inverse)
        (matrixDifferential g.forward) := by
      rw [g.differential_inverse]
      unfold pureGauge
      rfl
""",
            "Mock2 close the inverse-derivative differential rewrite reflexively",
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
            """  simpa only [Function.comp_apply] using
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
""",
            """  simpa [Function.comp_apply] using
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
""",
            "Mock2Advanced normalize reciprocal Gamma at zero",
        ),
        (
            """    simpa only [Function.comp_apply] using
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
""",
            """    simpa [Function.comp_apply] using
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
""",
            "Mock2Advanced normalize the real power endpoint",
        ),
        (
            """    simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
""",
            """    simpa [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
""",
            "Mock2Advanced normalize the complex cast endpoint",
        ),
        (
            """  exact (hpowC.mul invGamma_tendsto_zero).mul_const
    (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
""",
            """  simpa using
    (hpowC.mul invGamma_tendsto_zero).mul_const
      (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
""",
            "Mock2Advanced normalize the final zero product endpoint",
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

    old = """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  (show Function.Injective
      (fun γ : SL(2, ℤ) =>
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) from by
      intro a b h
      apply Subtype.ext
      exact h).countable
"""
    new = """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  Countable.of_injective
    (fun γ : SL(2, ℤ) =>
      let M : Matrix (Fin 2) (Fin 2) ℤ :=
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      ((M 0 0, M 0 1), (M 1 0, M 1 1)))
    (by
      intro a b h
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all)
"""
    text, changed = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis derive SL2Z countability from four integer entries",
    )
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass100.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
