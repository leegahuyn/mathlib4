from __future__ import annotations

from pathlib import Path

import apply_one_hundredth_pass_repairs as pass100
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
""",
            """theorem advanced_claims_ii_paper_i2_extrapolated_not_in_precision_tube
    (i : Fin 5) :
    Not
      (AdvancedClaimsIIPaperI2PrecisionTube
        (AdvancedClaimsIIPaperI2ExtrapolatedValue i)) := by
  fin_cases i <;> decide
""",
            "Mock1Advanced decide the five finite extrapolation obstructions in the kernel",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_coefficient_congruent_forward_difference
    (j : Fin 6) :
    FiniteCongruenceMod AdvancedClaimsIIPaperI2Prime
      AdvancedClaimsIIPaperI2Precision
      (AdvancedClaimsIIPaperI2MahlerCoefficient j)
      (AdvancedClaimsIIPaperI2ForwardDifference (j : Nat)) := by
  fin_cases j <;>
    norm_num [FiniteCongruenceMod, IntCongruent,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifference,
      AdvancedClaimsIIPaperI2NormalizedValue,
      AdvancedClaimsIIPaperI2InputTable,
      PrimePower, AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision]
""",
            """theorem advanced_claims_ii_paper_i2_coefficient_congruent_forward_difference
    (j : Fin 6) :
    FiniteCongruenceMod AdvancedClaimsIIPaperI2Prime
      AdvancedClaimsIIPaperI2Precision
      (AdvancedClaimsIIPaperI2MahlerCoefficient j)
      (AdvancedClaimsIIPaperI2ForwardDifference (j : Nat)) := by
  fin_cases j <;> decide
""",
            "Mock1Advanced decide the six finite forward-difference congruences in the kernel",
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
            "Mock2Advanced normalize the real-power endpoint",
        ),
        (
            """    simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
""",
            """    simpa [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
""",
            "Mock2Advanced normalize the complex-cast endpoint",
        ),
        (
            """  exact (hpowC.mul invGamma_tendsto_zero).mul_const
    (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
""",
            """  simpa using
    (hpowC.mul invGamma_tendsto_zero).mul_const
      (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
""",
            "Mock2Advanced normalize the final zero-product endpoint",
        ),
        (
            """theorem overlapVolume_eq_profile (T x : ℝ) :
    volume.real
        (Icc (-T / 2) (T / 2) ∩
          Icc (x - T / 2) (x + T / 2)) =
      profile T x := by
  rw [Icc_inter_Icc, Real.volume_real_Icc]
  unfold profile
  by_cases hx : x ≤ 0
  · rw [sup_eq_left.mpr (by linarith),
      inf_eq_right.mpr (by linarith), abs_of_nonpos hx, max_comm]
    congr 1
    ring
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    rw [sup_eq_right.mpr (by linarith),
      inf_eq_left.mpr (by linarith), abs_of_nonneg hx0, max_comm]
    congr 1
    ring
""",
            """theorem overlapVolume_eq_profile (T x : ℝ) :
    volume.real
        (Icc (-T / 2) (T / 2) ∩
          Icc (x - T / 2) (x + T / 2)) =
      profile T x := by
  rw [Icc_inter_Icc, Real.volume_real_Icc]
  unfold profile
  by_cases hx : x ≤ 0
  · apply congrArg (fun y : ℝ => max 0 y)
    calc
      min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2) =
          (x + T / 2) - (-T / 2) := by
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      _ = T - |x| := by
        rw [abs_of_nonpos hx]
        ring
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    apply congrArg (fun y : ℝ => max 0 y)
    calc
      min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2) =
          T / 2 - (x - T / 2) := by
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      _ = T - |x| := by
        rw [abs_of_nonneg hx0]
        ring
""",
            "Mock2Advanced compute overlap volume without rewriting the outer max",
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
            """  apply EventuallyLE.antisymm
""",
            """  apply Filter.EventuallyLE.antisymm
""",
            "FunctionalAnalysis qualify eventual-order antisymmetry",
        ),
        (
            """      (QuasiMeasurePreserving.smul_ae_eq_of_ae_eq a
""",
            """      (MeasureTheory.Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq a
""",
            "FunctionalAnalysis qualify transport of a.e.-equal sets under smul",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    old_hpre = """  have hpre :
      gammaTwoQuotientMk ⁻¹' (gammaTwoQuotientMk '' A) =
        ⋃ g : GammaTwoEffective, (g • ·) '' A := by
    simpa only [gammaTwoQuotientMk, Quotient.mk''_eq_mk] using
      (MulAction.quotient_preimage_image_eq_union_mul
        A (G := GammaTwoEffective))
"""
    new_hpre = """  have hpre :
      gammaTwoQuotientMk ⁻¹' (gammaTwoQuotientMk '' A) =
        ⋃ g : GammaTwoEffective, (g • ·) '' A := by
    change
      (Quotient.mk' : ℍ → GammaTwoQuotient) ⁻¹'
          ((Quotient.mk' : ℍ → GammaTwoQuotient) '' A) =
        ⋃ g : GammaTwoEffective, (g • ·) '' A
    exact MulAction.quotient_preimage_image_eq_union_mul
      A (G := GammaTwoEffective)
"""
    count = text.count(old_hpre)
    if count == 2:
        text = text.replace(old_hpre, new_hpre)
        changed = True
        print("FunctionalAnalysis expose both quotient preimages through Quotient.mk': applied 2")
    elif count == 0 and text.count(new_hpre) == 2:
        print("FunctionalAnalysis expose both quotient preimages through Quotient.mk': already applied")
    else:
        raise RuntimeError(
            f"FunctionalAnalysis expected two quotient-preimage blocks, found {count}"
        )

    text, did = replace_exact(
        text,
        """  rw [quotientMeasure,
    Measure.map_apply_of_aemeasurable
      (show AEMeasurable gammaTwoQuotientMk
          (hyperbolicMeasure.restrict D.carrier) from
        measurable_quotient_mk''.aemeasurable)
      himage,
    Measure.restrict_apply hpreMeas,
    hpre, iUnion_inter]
  rw [D.isFundamental.measure_eq_tsum A]
  exact measure_iUnion_le _
""",
        """  rw [quotientMeasure,
    Measure.map_apply_of_aemeasurable
      (show AEMeasurable gammaTwoQuotientMk
          (hyperbolicMeasure.restrict D.carrier) from
        measurable_quotient_mk''.aemeasurable)
      himage,
    Measure.restrict_apply hpreMeas,
    hpre]
  have hunionInter :
      (⋃ g : GammaTwoEffective, (g • ·) '' A) ∩ D.carrier =
        ⋃ g : GammaTwoEffective, ((g • ·) '' A ∩ D.carrier) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨g, hg⟩, hzD⟩
      exact ⟨g, hg, hzD⟩
    · rintro ⟨g, hg, hzD⟩
      exact ⟨⟨g, hg⟩, hzD⟩
  rw [hunionInter, D.isFundamental.measure_eq_tsum A]
  exact measure_iUnion_le _
""",
        1,
        "FunctionalAnalysis distribute the countable orbit union across the carrier",
    )
    changed |= did

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
