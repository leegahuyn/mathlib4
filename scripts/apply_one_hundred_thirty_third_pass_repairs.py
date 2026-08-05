from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_second_pass_repairs as pass132
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
            """structure AdvancedClaimsIIObjectiveChecklistDischargeCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Prop where
""",
            """structure AdvancedClaimsIIObjectiveChecklistDischargeCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Type where
""",
            1,
            "Mock1Advanced place the data-bearing objective checklist certificate in Type",
        ),
        (
            """theorem reference_advanced_claims_ii_objective_checklist_discharge
""",
            """noncomputable def reference_advanced_claims_ii_objective_checklist_discharge
""",
            1,
            "Mock1Advanced define the data-bearing objective checklist discharge",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """      restriction_pure_tensor := tensorPresheaf_res_tmul L M
      restriction_identity := (tensorPresheaf L M).res_id
      restriction_composition := (tensorPresheaf L M).res_comp }
""",
            """      restriction_pure_tensor := tensorPresheaf_res_tmul L M
      restriction_identity := by
        intro U
        ext s
        exact (tensorPresheaf L M).res_id U s
      restriction_composition := by
        intro U V W hUV hVW
        ext s
        exact (tensorPresheaf L M).res_comp hUV hVW s }
""",
            1,
            "Mock2 upgrade pointwise tensor restriction laws to morphism equalities",
        ),
        (
            """  locallyConstantLinearPresheaf_isSheaf
    (ModuleCat.of ℂ (TensorProduct ℂ E F))
""",
            """  Definition12Tensor.locallyConstantLinearPresheaf_isSheaf
    (X := X) (ModuleCat.of ℂ (TensorProduct ℂ E F))
""",
            1,
            "Mock2 determine the base space of the locally constant tensor sheaf",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """    ((f.onCovariantForms A : qGaugeForms D') : F) = f.map (A : E) :=
""",
            """    ((GaugeDescentMorphism.onCovariantForms f A : qGaugeForms D') : F) =
      f.map (A : E) :=
""",
            1,
            "Mock2Advanced call the nested covariant-form map explicitly",
        ),
        (
            """  (D.restriction hVU).onCovariantForms
""",
            """  GaugeDescentMorphism.onCovariantForms (D.restriction hVU)
""",
            1,
            "Mock2Advanced construct restriction through the explicit covariant-form map",
        ),
        (
            """    ((D.qGaugeRestrict hVU A : qGaugeForms (D.action V)) :
      D.forms.section V) =
""",
            """    ((GaugeDescentSheaf.qGaugeRestrict D hVU A :
        qGaugeForms (D.action V)) : D.forms.section V) =
""",
            1,
            "Mock2Advanced call the nested gauge restriction explicitly in its coercion theorem",
        ),
        (
            """    D.qGaugeRestrict (le_refl U) A = A := by
  apply Subtype.ext
  rw [D.coe_qGaugeRestrict]
""",
            """    GaugeDescentSheaf.qGaugeRestrict D (le_refl U) A = A := by
  apply Subtype.ext
  rw [GaugeDescentSheaf.coe_qGaugeRestrict D]
""",
            1,
            "Mock2Advanced prove gauge restriction identity without field notation",
        ),
        (
            """    D.qGaugeRestrict hWV (D.qGaugeRestrict hVU A) =
      D.qGaugeRestrict (hWV.trans hVU) A := by
  apply Subtype.ext
  simp only [D.coe_qGaugeRestrict]
""",
            """    GaugeDescentSheaf.qGaugeRestrict D hWV
        (GaugeDescentSheaf.qGaugeRestrict D hVU A) =
      GaugeDescentSheaf.qGaugeRestrict D (hWV.trans hVU) A := by
  apply Subtype.ext
  simp only [GaugeDescentSheaf.coe_qGaugeRestrict D]
""",
            1,
            "Mock2Advanced prove gauge restriction composition without field notation",
        ),
        (
            """      rw [hvnorm, div_one]
""",
            """      simpa only [hvnorm, div_one]
""",
            1,
            "Mock2Advanced simplify the dual ratio after beta reduction",
        ),
        (
            """  obtain ⟨Y, hKY⟩ := hK.exists_truncationHeight hKF
""",
            """  obtain ⟨Y, hKY⟩ :=
    Mock2Adv.IsCompact.exists_truncationHeight hK hKF
""",
            1,
            "Mock2Advanced invoke the topological compact-truncation theorem explicitly",
        ),
        (
            """  · intro m
    linarith [Nat.cast_nonneg m]
""",
            """  · intro m
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
""",
            1,
            "Mock2Advanced type the natural-number cast in the polynomial upper bound",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """theorem gammaTwoVerticalIncidencePolynomial_ne_zero
    (L c d x₀ y₀ : ℝ) (hL : 0 < L) :
    gammaTwoVerticalIncidencePolynomial L c d x₀ y₀ ≠ 0 := by
  intro hp
  by_cases hc : c = 0
  · have hcoeff := congrArg
      (fun p : Polynomial ℝ ↦ p.coeff 1) hp
    norm_num [gammaTwoVerticalIncidencePolynomial, hc] at hcoeff
  · have hlead : -(L * c ^ 2) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_ne_zero (ne_of_gt hL) (pow_ne_zero 2 hc))
    have hcoeff := congrArg
      (fun p : Polynomial ℝ ↦ p.coeff 2) hp
    apply hlead
    norm_num [gammaTwoVerticalIncidencePolynomial] at hcoeff ⊢
    exact hcoeff
""",
            """theorem gammaTwoVerticalIncidencePolynomial_ne_zero
    (L c d x₀ y₀ : ℝ) (hL : 0 < L) :
    gammaTwoVerticalIncidencePolynomial L c d x₀ y₀ ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval (0 : ℝ)) hp
  have h1 := congrArg (Polynomial.eval (1 : ℝ)) hp
  have h2 := congrArg (Polynomial.eval (2 : ℝ)) hp
  simp [gammaTwoVerticalIncidencePolynomial_eval] at h0 h1 h2
  by_cases hc : c = 0
  · subst c
    norm_num at h0 h1
    linarith
  · have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    nlinarith
""",
            1,
            "FunctionalAnalysis prove vertical polynomial nonvanishing from three evaluations",
        ),
        (
            """theorem gammaTwoCircularIncidencePolynomial_ne_zero
    (L A B : ℝ) :
    gammaTwoCircularIncidencePolynomial L A B ≠ 0 := by
  intro hp
  have hnonneg : 0 ≤ L ^ 2 * B ^ 2 :=
    mul_nonneg (sq_nonneg L) (sq_nonneg B)
  have hlead : -((1 : ℝ) / 4) - L ^ 2 * B ^ 2 ≠ 0 := by
    nlinarith
  have hcoeff := congrArg (fun p : Polynomial ℝ ↦ p.coeff 2) hp
  apply hlead
  norm_num [gammaTwoCircularIncidencePolynomial] at hcoeff ⊢
  exact hcoeff
""",
            """theorem gammaTwoCircularIncidencePolynomial_ne_zero
    (L A B : ℝ) :
    gammaTwoCircularIncidencePolynomial L A B ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval (0 : ℝ)) hp
  have h1 := congrArg (Polynomial.eval (1 : ℝ)) hp
  have hm1 := congrArg (Polynomial.eval (-1 : ℝ)) hp
  simp [gammaTwoCircularIncidencePolynomial_eval] at h0 h1 hm1
  have hnonneg : 0 ≤ L ^ 2 * B ^ 2 :=
    mul_nonneg (sq_nonneg L) (sq_nonneg B)
  nlinarith
""",
            1,
            "FunctionalAnalysis prove circular polynomial nonvanishing from symmetric evaluations",
        ),
        (
            """  rw [circular_lowerRowQuadratic_eq_affine] at hcleared
  have hsq := congrArg (fun x : ℝ ↦ x ^ 2) hcleared
  rw [modularCircularArcParam_im_sq] at hsq
  nlinarith
""",
            """  have htmem : (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [modularTileEdgeParameterSet] using t.property
  have hinside : 0 ≤ 1 - ((t : ℝ) / 2) ^ 2 := by
    nlinarith [htmem.1, htmem.2]
  have hsqrt :
      (Real.sqrt (1 - ((t : ℝ) / 2) ^ 2)) ^ 2 =
        1 - ((t : ℝ) / 2) ^ 2 :=
    Real.sq_sqrt hinside
  change
    Real.sqrt (1 - ((t : ℝ) / 2) ^ 2) =
      gammaTwoCuspLevel Y *
        ((gammaTwoCornerLowerLeft (e, .circularArc) q *
              ((t : ℝ) / 2) +
            gammaTwoCornerLowerRight (e, .circularArc) q) ^ 2 +
          gammaTwoCornerLowerLeft (e, .circularArc) q ^ 2 *
            (Real.sqrt (1 - ((t : ℝ) / 2) ^ 2)) ^ 2) at hcleared
  nlinarith
""",
            1,
            "FunctionalAnalysis eliminate the circular square root in the raw parameter expression",
        ),
    ])


def main() -> int:
    pass132.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
