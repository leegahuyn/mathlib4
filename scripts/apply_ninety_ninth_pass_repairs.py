from __future__ import annotations

from pathlib import Path

import apply_ninety_eighth_pass_repairs as pass98
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
            "Mock1Advanced prove all five extrapolated values outside the precision tube",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_input_manifest_incomplete :
    Not
      (AdvancedClaimsIIPaperI2InputManifest.Complete
        referenceAdvancedClaimsIIPaperI2InputManifest) := by
  native_decide
""",
            """theorem advanced_claims_ii_paper_i2_input_manifest_incomplete :
    Not
      (AdvancedClaimsIIPaperI2InputManifest.Complete
        referenceAdvancedClaimsIIPaperI2InputManifest) := by
  simp [AdvancedClaimsIIPaperI2InputManifest.Complete,
    referenceAdvancedClaimsIIPaperI2InputManifest]
""",
            "Mock1Advanced expose the missing paper-I.2 manifest fields",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_lower_triangular :
    AdvancedClaimsIIPaperI2MahlerMatrixLowerTriangular := by
  native_decide
""",
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_lower_triangular :
    AdvancedClaimsIIPaperI2MahlerMatrixLowerTriangular := by
  intro n j h
  unfold AdvancedClaimsIIPaperI2MahlerMatrixEntry
  exact Nat.choose_eq_zero_of_lt h
""",
            "Mock1Advanced prove lower triangularity from choose vanishing",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_unit_diagonal :
    forall n : Fin 6,
      AdvancedClaimsIIPaperI2MahlerMatrixEntry n n = 1 := by
  native_decide
""",
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_unit_diagonal :
    forall n : Fin 6,
      AdvancedClaimsIIPaperI2MahlerMatrixEntry n n = 1 := by
  intro n
  simp [AdvancedClaimsIIPaperI2MahlerMatrixEntry]
""",
            "Mock1Advanced prove the Mahler diagonal by choose-self",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_below_diagonal_witness :
    AdvancedClaimsIIPaperI2MahlerMatrixEntry
      (1 : Fin 6) (0 : Fin 6) = 1 := by
  native_decide
""",
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_below_diagonal_witness :
    AdvancedClaimsIIPaperI2MahlerMatrixEntry
      (1 : Fin 6) (0 : Fin 6) = 1 := by
  norm_num [AdvancedClaimsIIPaperI2MahlerMatrixEntry]
""",
            "Mock1Advanced compute the below-diagonal Mahler witness",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_not_upper_triangular :
    Not AdvancedClaimsIIPaperI2MahlerMatrixUpperTriangular := by
  native_decide
""",
            """theorem advanced_claims_ii_paper_i2_mahler_matrix_not_upper_triangular :
    Not AdvancedClaimsIIPaperI2MahlerMatrixUpperTriangular := by
  intro h
  have hz := h (1 : Fin 6) (0 : Fin 6) (by norm_num)
  norm_num [AdvancedClaimsIIPaperI2MahlerMatrixEntry] at hz
""",
            "Mock1Advanced refute upper triangularity using the (1,0) entry",
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
    norm_num [FiniteCongruenceMod, IntCongruent,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifference,
      AdvancedClaimsIIPaperI2NormalizedValue,
      AdvancedClaimsIIPaperI2InputTable,
      PrimePower, AdvancedClaimsIIPaperI2Prime,
      AdvancedClaimsIIPaperI2Precision]
""",
            "Mock1Advanced prove all six forward-difference congruences",
        ),
        (
            """theorem advanced_claims_ii_paper_i2_table5b_difference_zero
    (n : Fin 6) :
    AdvancedClaimsIIPaperI2Table5BDifference n = 0 := by
  rfl
""",
            """theorem advanced_claims_ii_paper_i2_table5b_difference_zero
    (n : Fin 6) :
    AdvancedClaimsIIPaperI2Table5BDifference n = 0 := by
  simp [AdvancedClaimsIIPaperI2Table5BDifference,
    referenceAdvancedClaimsIIPaperI2Overlap]
""",
            "Mock1Advanced unfold the identical Table-5B overlap functions",
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

    text, did = replace_exact(
        text,
        """theorem box_mul_box_eq_overlapIndicator (T x : ℝ) :
    (fun t => box T t * box T (x - t)) =
      (Icc (-T / 2) (T / 2) ∩
        Icc (x - T / 2) (x + T / 2)).indicator (fun _ => 1) := by
  funext t
  by_cases ht : t ∈ Icc (-T / 2) (T / 2) <;>
    by_cases hs : t ∈ Icc (x - T / 2) (x + T / 2) <;>
    simp [box, ht, hs, sub_mem_centered_iff]
""",
        """theorem box_mul_box_eq_overlapIndicator (T x : ℝ) :
    (fun t => box T t * box T (x - t)) =
      (Icc (-T / 2) (T / 2) ∩
        Icc (x - T / 2) (x + T / 2)).indicator (fun _ => 1) := by
  funext t
  by_cases ht : t ∈ Icc (-T / 2) (T / 2)
  · by_cases hs : t ∈ Icc (x - T / 2) (x + T / 2)
    · have hsub : x - t ∈ Icc (-T / 2) (T / 2) :=
        (sub_mem_centered_iff T x t).2 hs
      simp [box, ht, hs, hsub]
    · have hsub : x - t ∉ Icc (-T / 2) (T / 2) := by
        intro h
        exact hs ((sub_mem_centered_iff T x t).1 h)
      simp [box, ht, hs, hsub]
  · simp [box, ht]
""",
        1,
        "Mock2Advanced prove the tent overlap indicator by explicit cases",
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
        """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
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
""",
        """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  (show Function.Injective
      (fun γ : SL(2, ℤ) =>
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) from by
      intro a b h
      apply Subtype.ext
      exact h).countable
""",
        1,
        "FunctionalAnalysis derive SL2Z countability from matrix coercion",
    )
    changed |= did

    old_hcancel = """  have hcancel :
      ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z =
        gammaTwoCosetRep q • (g • z) := by
    calc
      ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z =
          ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) •
            (g⁻¹ • (g • z)) := by simp
      _ = ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) •
            (((γ : GammaTwo) : SL(2, ℤ)) *
              gammaTwoCosetRep q) • (g • z) := by
        rw [hdecomp']
      _ = gammaTwoCosetRep q • (g • z) := by
        simp only [mul_smul]
        rw [inv_smul_smul]
"""
    new_hcancel = """  have hcancel :
      ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z =
        gammaTwoCosetRep q • (g • z) := by
    have hg :
        g = (gammaTwoCosetRep q)⁻¹ *
          ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) := by
      have h := congrArg Inv.inv hdecomp'
      simpa [mul_inv_rev] using h
    have hγ :
        ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) =
          gammaTwoCosetRep q * g := by
      rw [hg]
      simp [mul_assoc]
    rw [hγ, mul_smul]
"""
    count = text.count(old_hcancel)
    if count == 2:
        text = text.replace(old_hcancel, new_hcancel)
        changed = True
        print("FunctionalAnalysis derive both coset cancellations by group inversion: applied 2")
    elif count == 0 and text.count(new_hcancel) == 2:
        print("FunctionalAnalysis derive both coset cancellations by group inversion: already applied")
    else:
        raise RuntimeError(
            f"FunctionalAnalysis expected two coset cancellation blocks, found {count}"
        )

    old_finish = """  simpa only [gammaTwoEffectiveElement_smul, hcancel] using htile
"""
    new_finish = """  change ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z ∈
    gammaTwoOpenCarrier
  rw [hcancel]
  exact htile
"""
    count = text.count(old_finish)
    if count == 2:
        text = text.replace(old_finish, new_finish)
        changed = True
        print("FunctionalAnalysis finish both carrier-cover proofs explicitly: applied 2")
    elif count == 0 and text.count(new_finish) == 2:
        print("FunctionalAnalysis finish both carrier-cover proofs explicitly: already applied")
    else:
        raise RuntimeError(
            f"FunctionalAnalysis expected two carrier-cover finishes, found {count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass98.main()
    repair_mock1_advanced()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
