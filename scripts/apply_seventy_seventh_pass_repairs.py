from __future__ import annotations

from pathlib import Path

import apply_seventy_sixth_pass_repairs as pass76
import apply_seventy_fifth_pass_repairs as pass75
import apply_seventy_third_pass_repairs as pass73
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def _ref_type(text: str, namespace: str, theorem: str) -> str:
    return pass75._ref_type(text, namespace, theorem)


def _conj(*types: str) -> str:
    return pass75._conj(*types)


def _forall(binder: str, typ: str) -> str:
    return pass75._forall(binder, typ)


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    paper = "PaperDataInstancePayloadCertificate"
    remaining = "RemainingAdvancedClaimPayloadCertificate"
    spt = "SPTKernelRequirementPayloadCertificate"
    exact = "ExactCoefficientRequirementPayloadCertificate"
    padic = "PAdicRequirementPayloadCertificate"
    entropy = "EntropyReproRequirementPayloadCertificate"

    fields = {
        "object_schema_payload": _conj(
            _ref_type(text, paper, "claim_registry_at"),
            _forall("claim : RemainingAdvancedClaim", _ref_type(text, paper, "claim_covered_at")),
            _ref_type(text, remaining, "object_schema_concrete_at"),
            _forall("n : Nat", _ref_type(text, paper, "object_coefficient_at")),
            _ref_type(text, paper, "paper_object_instance_at"),
            _forall("n : Nat", _ref_type(text, paper, "scalar_jacobi_at")),
        ),
        "t1t5_payload": _conj(
            _ref_type(text, paper, "matrix_solution_at"),
            _ref_type(text, paper, "matrix_rows_at"),
            _ref_type(text, paper, "matrix_rhs_rows_at"),
            _ref_type(text, paper, "matrix_solution_columns_at"),
            _ref_type(text, remaining, "principal_part_rational_solve_at"),
            _ref_type(text, remaining, "completion_shadow_holomorphic_at"),
            _ref_type(text, remaining, "cusp_transport_at"),
            _ref_type(text, remaining, "appell_lerch_block_formula_at"),
            _ref_type(text, remaining, "principal_exponent_formula_at"),
            _ref_type(text, remaining, "fixed_shadow_unary_theta_at"),
            _forall("n : Nat", _ref_type(text, remaining, "inside_outside_qseries_at")),
        ),
        "spt_payload": _conj(
            _ref_type(text, spt, "nat_gcd_lcm_at"),
            _ref_type(text, spt, "primewise_thickness_at"),
            _ref_type(text, spt, "valuation_certificate_at"),
            _ref_type(text, spt, "obstruction_failure_at"),
            _ref_type(text, spt, "base_change_at"),
        ),
        "kernel_payload": _conj(
            _ref_type(text, spt, "kernel_selection_at"),
            _ref_type(text, spt, "multiplier_phase_at"),
            _ref_type(text, spt, "cusp_convergence_at"),
            _ref_type(text, spt, "transport_family_at"),
            _ref_type(text, spt, "kernel_table_at"),
            _ref_type(text, spt, "multiplier_input_at"),
            _ref_type(text, spt, "cusp_input_at"),
            _ref_type(text, spt, "transport_across_cusps_at"),
        ),
        "exact_payload": _conj(
            _forall("n : Nat", _ref_type(text, exact, "coefficient_separation_at")),
            _ref_type(text, exact, "theta_character_at"),
            _ref_type(text, exact, "spectral_kloosterman_at"),
            _ref_type(text, exact, "local_euler_at"),
            _ref_type(text, exact, "root_filter_at"),
            _forall("n : Nat", _ref_type(text, exact, "exact_formula_at")),
            _ref_type(text, exact, "paper_formula_fields_at"),
        ),
        "padic_payload": _conj(
            _forall("n : Nat", _ref_type(text, padic, "normalization_at")),
            _forall("n : Nat", _ref_type(text, padic, "overlap_at")),
            _forall("n : Nat", _ref_type(text, padic, "mahler_at")),
            _forall(
                "n : Nat",
                _forall(
                    "hn : referenceAdvancedClaimsIICompletionCertificate."
                    "padicAnalyticRange.cutoff <= n",
                    _ref_type(text, padic, "tail_zero_at"),
                ),
            ),
            _ref_type(text, padic, "face_tracking_at"),
            _ref_type(text, padic, "denominator_data_at"),
            _forall("n : Nat", _ref_type(text, padic, "chart_vectors_at")),
            _forall("n : Nat", _ref_type(text, padic, "mahler_table_at")),
            _forall(
                "n : Nat",
                _forall(
                    "hn : referenceAdvancedClaimsIICompletionCertificate."
                    "padicAnalyticRange.cutoff <= n",
                    _ref_type(text, padic, "predicate_at"),
                ),
            ),
            _ref_type(text, padic, "obstruction_failure_at"),
        ),
        "entropy_payload": _conj(
            _ref_type(text, entropy, "regression_cardy_at"),
            _ref_type(text, entropy, "rademacher_tail_at"),
            _ref_type(text, entropy, "entropy_cardy_wrapper_at"),
            _ref_type(text, entropy, "alpha_extraction_at"),
            _forall("n : Nat", _ref_type(text, entropy, "degeneracy_at")),
            _ref_type(text, entropy, "ols_interval_at"),
            _ref_type(text, entropy, "growth_stability_at"),
            _ref_type(text, entropy, "reproducibility_schema_at"),
            _ref_type(text, entropy, "external_rows_at"),
        ),
    }

    applied = 0
    for field, typ in fields.items():
        text, did = pass73._replace_structure_field_type(
            text, "AdvancedClaimsIIFormulaLevelPromptLedgerCertificate", field, typ)
        changed |= did
        applied += int(did)

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock1Advanced type the formula-level prompt ledger payloads: applied {applied}")
    else:
        print("Mock1Advanced type the formula-level prompt ledger payloads: already applied")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """      wedge a (wedge b c) := by
  apply ChartForm.ext <;> simp [GradedForm.cast, wedge] <;> ring
""",
            """      wedge a (wedge b c) := by
  apply ChartForm.ext <;> simp [wedge] <;> ring
""",
            "Mock2 use the chart cast projection simp lemmas without unfolding Eq.rec",
        ),
        (
            """@[simp] theorem differential_zero (n : ℕ) :
    differential (0 : ChartForm n) = 0 := by
  ext <;> simp [differential]
""",
            """@[simp] theorem differential_zero (n : ℕ) :
    differential (0 : ChartForm n) = 0 := by
  apply ChartForm.ext <;> simp [differential]
""",
            "Mock2 stop differential-zero extensionality at chart fields",
        ),
        (
            """theorem differential_add {n : ℕ} (a b : ChartForm n) :
    differential (a + b) = differential a + differential b := by
  ext <;> simp [differential, Polynomial.derivative_add]
""",
            """theorem differential_add {n : ℕ} (a b : ChartForm n) :
    differential (a + b) = differential a + differential b := by
  apply ChartForm.ext <;>
    simp [differential, chartFormAdd, Polynomial.derivative_add]
""",
            "Mock2 stop differential-add extensionality at chart fields",
        ),
        (
            """@[simp] theorem differential_squared {n : ℕ} (a : ChartForm n) :
    differential (differential a) = 0 := by
  ext <;> simp [differential]
""",
            """@[simp] theorem differential_squared {n : ℕ} (a : ChartForm n) :
    differential (differential a) = 0 := by
  apply ChartForm.ext <;> simp [differential]
""",
            "Mock2 stop differential-square extensionality at chart fields",
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
            """  have hbound :
      ‖ConcreteUnaryTheta.theta thetaNonzeroPoint - 1‖ ≤
        2 /
            (1 - Real.exp
              (-Real.pi * thetaNonzeroPoint.im)) *
          Real.exp (-Real.pi * thetaNonzeroPoint.im) := by
    simpa only [ConcreteUnaryTheta.theta] using
      (norm_jacobiTheta_sub_one_le thetaNonzeroPoint.im_pos)
""",
            """  have hbound :
      ‖ConcreteUnaryTheta.theta thetaNonzeroPoint - 1‖ ≤
        2 /
            (1 - Real.exp
              (-Real.pi * thetaNonzeroPoint.im)) *
          Real.exp (-Real.pi * thetaNonzeroPoint.im) := by
    change
      ‖jacobiTheta (thetaNonzeroPoint : ℂ) - 1‖ ≤
        2 / (1 - Real.exp (-Real.pi * (thetaNonzeroPoint : ℂ).im)) *
          Real.exp (-Real.pi * (thetaNonzeroPoint : ℂ).im)
    exact norm_jacobiTheta_sub_one_le thetaNonzeroPoint.im_pos
""",
            "Mock2Advanced expose the complex imaginary part in the theta bound",
        ),
        (
            """  have hbase :
      (p : GenuineGamma2Metaplectic.Element × Circle).1 =
        (q : GenuineGamma2Metaplectic.Element × Circle).1 := by
    simpa only [thetaCovariantProjection] using hpq
""",
            """  have hbase :
      (p : GenuineGamma2Metaplectic.Element × Circle).1 =
        (q : GenuineGamma2Metaplectic.Element × Circle).1 := by
    change
      (p : GenuineGamma2Metaplectic.Element × Circle).1 =
        (q : GenuineGamma2Metaplectic.Element × Circle).1 at hpq
    exact hpq
""",
            "Mock2Advanced unfold the covariance projection in its injectivity proof",
        ),
        (
            """    have hbase :
        (p : GenuineGamma2Metaplectic.Element × Circle).1 = a := by
      simpa only [thetaCovariantProjection] using hp
    simpa only [hbase] using p.property
""",
            """    have hbase :
        (p : GenuineGamma2Metaplectic.Element × Circle).1 = a := by
      change (p : GenuineGamma2Metaplectic.Element × Circle).1 = a at hp
      exact hp
    change IsThetaCovariant
      (p : GenuineGamma2Metaplectic.Element × Circle).1
      (p : GenuineGamma2Metaplectic.Element × Circle).2 at p.property
    rw [← hbase]
    exact p.property
""",
            "Mock2Advanced unfold projection and subgroup membership in surjectivity",
        ),
        (
            """  intro a τ
  simpa only [factor, thetaMultiplierOfFullCovariance] using
    chosenThetaPhase_covariant hfull a τ
""",
            """  intro a τ
  change ConcreteUnaryTheta.theta (gamma2Act a.matrix τ) =
    (chosenThetaPhase hfull a : ℂ) * a.sqrtFactor τ *
      ConcreteUnaryTheta.theta τ
  exact chosenThetaPhase_covariant hfull a τ
""",
            "Mock2Advanced unfold the constructed theta multiplier at application",
        ),
        (
            """  rw [map_mul, mul_inv_rev]
  ring
""",
            """  rw [map_mul, Circle.coe_mul, mul_inv_rev]
  ring
""",
            "Mock2Advanced expose the complex coercion of circle multiplication",
        ),
        (
            """  exact density_invariant a (ν a) τ (u τ)
""",
            """  exact GenuineInverseHalfWeightAutomorphy.density_invariant
    a (ν a) τ (u τ)
""",
            "Mock2Advanced qualify the base density invariance theorem",
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
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  field_simp [ModularForm.eta_ne_zero (δ • z).2]
""",
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  ring
""",
            "FunctionalAnalysis normalize the cleared inverse-eta identity",
        ),
        (
            """noncomputable instance gammaTwoCountable : Countable GammaTwo := by
  infer_instance
""",
            """noncomputable instance gammaTwoCountable : Countable GammaTwo :=
  (show Function.Injective
      (fun γ : GammaTwo =>
        ((((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
         (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
         (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
         (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) from by
      intro a b h
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp_all).countable
""",
            "FunctionalAnalysis derive GammaTwo countability from its four integer entries",
        ),
        (
            """  refine Matrix.SpecialLinearGroup.isEmbedding_toGL.of_comp ?_
""",
            """  refine
    (Matrix.SpecialLinearGroup.isEmbedding_toGL
      (n := Fin 2) (R := ℝ)).of_comp ?_
""",
            "FunctionalAnalysis specify the real special-linear embedding parameters",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass76.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
