from __future__ import annotations

from pathlib import Path
import re

import apply_seventy_eighth_pass_repairs as pass78
import apply_seventy_fifth_pass_repairs as pass75
import apply_seventy_third_pass_repairs as pass73
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def _ref_type(text: str, namespace: str, theorem: str) -> str:
    return pass75._ref_type(text, namespace, theorem)


def _conj(*types: str) -> str:
    return pass75._conj(*types)


def _replace_top_level_theorem_result(
    text: str, theorem: str, result_type: str
) -> tuple[str, bool]:
    start = text.index(f"theorem {theorem}")
    assignment = text.index(" :=\n", start)
    delimiter = text.rfind(":\n", start, assignment)
    if delimiter < 0:
        raise RuntimeError(f"{theorem}: result delimiter absent")
    result_start = delimiter + 2
    rendered = pass71._render_type(result_type)
    if text[result_start:assignment] == rendered:
        return text, False
    return text[:result_start] + rendered + text[assignment:], True


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

    targets = {
        "reference_formula_level_prompt_object_registry":
            _ref_type(text, paper, "claim_registry_at"),
        "reference_formula_level_prompt_object_claim_covered":
            _ref_type(text, paper, "claim_covered_at"),
        "reference_formula_level_prompt_object_schema_concrete":
            _ref_type(text, remaining, "object_schema_concrete_at"),
        "reference_formula_level_prompt_object_coefficient":
            _ref_type(text, paper, "object_coefficient_at"),
        "reference_formula_level_prompt_paper_object_instance":
            _ref_type(text, paper, "paper_object_instance_at"),
        "reference_formula_level_prompt_scalar_jacobi":
            _ref_type(text, paper, "scalar_jacobi_at"),
        "reference_formula_level_prompt_matrix_solution":
            _ref_type(text, paper, "matrix_solution_at"),
        "reference_formula_level_prompt_matrix_rows":
            _ref_type(text, paper, "matrix_rows_at"),
        "reference_formula_level_prompt_matrix_rhs_rows":
            _ref_type(text, paper, "matrix_rhs_rows_at"),
        "reference_formula_level_prompt_matrix_solution_columns":
            _ref_type(text, paper, "matrix_solution_columns_at"),
        "reference_formula_level_prompt_principal_part_solve":
            _ref_type(text, remaining, "principal_part_rational_solve_at"),
        "reference_formula_level_prompt_spt_arithmetic": _conj(
            _ref_type(text, spt, "nat_gcd_lcm_at"),
            _ref_type(text, spt, "primewise_thickness_at"),
            _ref_type(text, spt, "valuation_certificate_at"),
        ),
        "reference_formula_level_prompt_spt_obstruction_base_change": _conj(
            _ref_type(text, spt, "obstruction_failure_at"),
            _ref_type(text, spt, "base_change_at"),
        ),
        "reference_formula_level_prompt_kernel_selection_table": _conj(
            _ref_type(text, spt, "kernel_selection_at"),
            _ref_type(text, spt, "kernel_table_at"),
        ),
        "reference_formula_level_prompt_multiplier_cusp_transport": _conj(
            _ref_type(text, spt, "multiplier_phase_at"),
            _ref_type(text, spt, "cusp_convergence_at"),
            _ref_type(text, spt, "transport_family_at"),
            _ref_type(text, spt, "transport_across_cusps_at"),
        ),
        "reference_formula_level_prompt_kernel_actual_inputs": _conj(
            _ref_type(text, spt, "multiplier_input_at"),
            _ref_type(text, spt, "cusp_input_at"),
        ),
        "reference_formula_level_prompt_exact_boundaries": _conj(
            _ref_type(text, exact, "coefficient_separation_at"),
            _ref_type(text, exact, "exact_formula_at"),
        ),
        "reference_formula_level_prompt_exact_global_inputs": _conj(
            _ref_type(text, exact, "theta_character_at"),
            _ref_type(text, exact, "spectral_kloosterman_at"),
            _ref_type(text, exact, "local_euler_at"),
            _ref_type(text, exact, "root_filter_at"),
            _ref_type(text, exact, "paper_formula_fields_at"),
        ),
        "reference_formula_level_prompt_padic_pointwise": _conj(
            _ref_type(text, padic, "normalization_at"),
            _ref_type(text, padic, "overlap_at"),
            _ref_type(text, padic, "mahler_at"),
        ),
        "reference_formula_level_prompt_padic_tail":
            _ref_type(text, padic, "tail_zero_at"),
        "reference_formula_level_prompt_padic_actual_inputs": _conj(
            _ref_type(text, padic, "chart_vectors_at"),
            _ref_type(text, padic, "mahler_table_at"),
        ),
        "reference_formula_level_prompt_padic_global": _conj(
            _ref_type(text, padic, "face_tracking_at"),
            _ref_type(text, padic, "denominator_data_at"),
            _ref_type(text, padic, "obstruction_failure_at"),
        ),
        "reference_formula_level_prompt_entropy_core": _conj(
            _ref_type(text, entropy, "regression_cardy_at"),
            _ref_type(text, entropy, "rademacher_tail_at"),
            _ref_type(text, entropy, "entropy_cardy_wrapper_at"),
        ),
        "reference_formula_level_prompt_entropy_pointwise":
            _ref_type(text, entropy, "degeneracy_at"),
        "reference_formula_level_prompt_entropy_reproducibility": _conj(
            _ref_type(text, entropy, "alpha_extraction_at"),
            _ref_type(text, entropy, "ols_interval_at"),
            _ref_type(text, entropy, "growth_stability_at"),
            _ref_type(text, entropy, "reproducibility_schema_at"),
            _ref_type(text, entropy, "external_rows_at"),
        ),
    }

    applied = 0
    for theorem, typ in targets.items():
        text, did = _replace_top_level_theorem_result(text, theorem, typ)
        changed |= did
        applied += int(did)
    print(
        f"Mock1Advanced type formula-level prompt atoms explicitly: applied {applied}"
        if applied else
        "Mock1Advanced type formula-level prompt atoms explicitly: already applied"
    )

    entropy_field = (
        "forall n : Nat,\n  " + _ref_type(text, entropy, "degeneracy_at")
    )
    text, did = pass73._replace_structure_field_type(
        text,
        "AdvancedClaimsIIFormulaLevelMergeAuditCertificate",
        "entropy_degeneracy",
        entropy_field,
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def _mark_noncomputable(text: str, names: list[str]) -> tuple[str, int]:
    count = 0
    for name in names:
        pattern = re.compile(
            rf"(?m)^(?P<indent>\s*)(?P<prefix>private\s+)?(?P<kind>def|instance)\s+{re.escape(name)}\b"
        )
        def repl(match: re.Match[str]) -> str:
            nonlocal count
            count += 1
            return (
                f"{match.group('indent')}{match.group('prefix') or ''}noncomputable "
                f"{match.group('kind')} {name}"
            )
        text = pattern.sub(repl, text)
    return text, count


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """def toCurvatureAlgebra : CurvatureAlgebra X where
  Form := fun _ U => Ω U
""",
        """@[reducible] def toCurvatureAlgebra : CurvatureAlgebra X where
  Form := fun _ U => Ω U
""",
        1,
        "Mock2 expose the truncated curvature adapter definitionally",
    )
    changed |= did

    text, count = _mark_noncomputable(text, [
        "covariantSubpresheaf", "AqPresheaf", "curvatureFamily", "gaugeTransform",
    ])
    if count:
        changed = True
        print(f"Mock2 propagate four remaining noncomputable definitions: applied {count}")
    else:
        print("Mock2 propagate four remaining noncomputable definitions: already applied")

    replacements = [
        (
            """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U (g * A) B) =
      g * (show Ω U from (G.toCurvatureAlgebra).wedge U A B) := by
  simpa only [toCurvatureAlgebra] using (mul_assoc g A B)
""",
            """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U (g * A) B) =
      g * (show Ω U from (G.toCurvatureAlgebra).wedge U A B) := by
  change (g * A) * B = g * (A * B)
  exact mul_assoc g A B
""",
            "Mock2 expose the left wedge multiplication definitionally",
        ),
        (
            """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U A (B * g)) =
      (show Ω U from (G.toCurvatureAlgebra).wedge U A B) * g := by
  simpa only [toCurvatureAlgebra] using (mul_assoc A B g).symm
""",
            """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U A (B * g)) =
      (show Ω U from (G.toCurvatureAlgebra).wedge U A B) * g := by
  change A * (B * g) = (A * B) * g
  exact (mul_assoc A B g).symm
""",
            "Mock2 expose the right wedge multiplication definitionally",
        ),
        (
            """theorem potential_action_assoc (C : Core U) (s : LocalFramedSection U) :
""",
            """set_option maxHeartbeats 800000 in
theorem potential_action_assoc (C : Core U) (s : LocalFramedSection U) :
""",
            "Mock2 localize additional heartbeats to matrix action associativity",
        ),
        (
            """      wedge_add_left, wedge_add_right, wedge_assoc] <;> abel
""",
            """      wedge_add_left, wedge_add_right] <;> abel_nf
""",
            "Mock2 normalize the four polynomial action-associativity goals",
        ),
        (
            """theorem curvature_restrict (C : Core U)
    {V : TopologicalSpace.Opens X} (hVU : V ≤ U) :
    (C.restrict hVU).curvature = restrictHom hVU C.curvature := by
  rw [curvature_formula, curvature_formula, restrict_potential,
    restrict_add, restrict_matrixDifferential, restrict_matrixWedge]
""",
            """theorem curvature_restrict (C : Core U)
    {V : TopologicalSpace.Opens X} (hVU : V ≤ U) :
    (C.restrict hVU).curvature = restrictHom hVU C.curvature := by
  rw [curvature_formula, curvature_formula, restrict_potential,
    restrict_add, restrict_matrixDifferential]
  exact congrArg
    (fun T => matrixDifferential (restrictHom hVU C.potential) + T)
    (restrict_matrixWedge hVU C.potential C.potential).symm
""",
            "Mock2 prove curvature restriction through the explicit wedge restriction theorem",
        ),
        (
            """      simp [identityZeroForm, zeroFormMatrix, matrixWedge,
        Fin.sum_univ_two, zeroFormCoefficient, wedge]
""",
            """      simp [identityZeroForm, zeroFormMatrix, matrixWedge,
        Fin.sum_univ_two, zeroFormCoefficient, wedge, Matrix.one_apply]
""",
            "Mock2 simplify both matrix identity wedge proofs entrywise",
        ),
    ]
    for old, new, label in replacements:
        expected = 2 if "both matrix identity" in label else 1
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]
    for old, new in {
        "IsAutomorphic ν": "GenuineInverseHalfWeightAutomorphy.IsAutomorphic ν",
        "IsAEAutomorphic ν": "GenuineInverseHalfWeightAutomorphy.IsAEAutomorphic ν",
    }.items():
        block, count = re.subn(rf"(?<![A-Za-z0-9_.]){re.escape(old)}", new, block)
        if count:
            changed = True
            print(f"Mock2Advanced qualify {old}: applied {count}")
    text = text[:start] + block + text[end:]

    replacements = [
        (
            """        exact (M.core_equivariant v hv).isAE)
""",
            """        exact (M.core_equivariant v hv).isAE μ)
""",
            "Mock2Advanced supply the target measure to automorphy a.e. conversion",
        ),
        (
            """  apply hclosure
  simpa only [Submodule.topologicalClosure_coe] using u.property
""",
            """  apply hclosure
  rw [← Submodule.topologicalClosure_coe]
  exact u.property
""",
            "Mock2Advanced transport Sobolev membership across topological closure",
        ),
        (
            """  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      simp_rw [abelRemainder]
      ring
""",
            """  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      have hrem :
          (Finset.range N).sum (abelRemainder a b) =
            ∑ x ∈ Finset.range N,
              (prefixSum a x * b x - prefixSum a x * b (1 + x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        unfold abelRemainder
        rw [Nat.add_comm]
        ring
      rw [hrem]
      ring
""",
            "Mock2Advanced prove finite Abel summation by termwise remainder expansion",
        ),
        (
            """theorem pSeriesMajorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (pSeriesMajorant δ) := by
  simpa only [pSeriesMajorant] using
    (Real.summable_one_div_nat_add_rpow 1 (1 + δ)).2 (by linarith)
""",
            """theorem pSeriesMajorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (pSeriesMajorant δ) := by
  change Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 + δ))
  exact (Real.summable_one_div_nat_add_rpow 1 (1 + δ)).2 (by linarith)
""",
            "Mock2Advanced expose the p-series majorant before applying summability",
        ),
    ]
    for old, new, label in replacements:
        expected = 2 if "target measure" in label else 1
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """theorem inverseEtaRawFactor_mul (γ δ : SL(2, ℤ)) (z : ℍ) :
    inverseEtaRawFactor (γ * δ) z =
      inverseEtaRawFactor γ (δ • z) * inverseEtaRawFactor δ z := by
  rw [inverseEtaRawFactor_eq, inverseEtaRawFactor_eq,
    inverseEtaRawFactor_eq, mul_smul]
  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
            """theorem inverseEtaRawFactor_mul (γ δ : SL(2, ℤ)) (z : ℍ) :
    inverseEtaRawFactor (γ * δ) z =
      inverseEtaRawFactor γ (δ • z) * inverseEtaRawFactor δ z := by
  rw [inverseEtaRawFactor_eq, inverseEtaRawFactor_eq,
    inverseEtaRawFactor_eq, mul_smul]
  simp only [div_eq_mul_inv]
  calc
    ModularForm.eta ↑z * (ModularForm.eta ↑(γ • δ • z))⁻¹ =
        (ModularForm.eta ↑(δ • z) *
          (ModularForm.eta ↑(δ • z))⁻¹) *
            (ModularForm.eta ↑z *
              (ModularForm.eta ↑(γ • δ • z))⁻¹) := by
      rw [mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), one_mul]
    _ =
        (ModularForm.eta ↑(δ • z) *
          (ModularForm.eta ↑(γ • δ • z))⁻¹) *
            (ModularForm.eta ↑z *
              (ModularForm.eta ↑(δ • z))⁻¹) := by ring
""",
            "FunctionalAnalysis prove the inverse-eta cocycle by cancellation and ring normalization",
        ),
        (
            """theorem gammaTwoToSL2Real_isClosedEmbedding :
    Topology.IsClosedEmbedding gammaTwoToSL2Real := by
  refine
    (Matrix.SpecialLinearGroup.isEmbedding_toGL
      (n := Fin 2) (R := ℝ)).of_comp ?_
  convert
    (Matrix.SpecialLinearGroup.isClosedEmbedding_mapGLInt
      (n := Fin 2)).comp
      ((isClosed_discrete (GammaTwo : Set SL(2, ℤ))).isClosedEmbedding_subtypeVal)
    using 1 <;> rfl
""",
            """theorem gammaTwoToSL2Real_isClosedEmbedding :
    Topology.IsClosedEmbedding gammaTwoToSL2Real := by
  convert
    (Matrix.SpecialLinearGroup.isClosedEmbedding_mapGLInt
      (n := Fin 2)).comp
      ((isClosed_discrete (GammaTwo : Set SL(2, ℤ))).isClosedEmbedding_subtypeVal)
    using 1 <;> rfl
""",
            "FunctionalAnalysis compose the two closed embeddings directly",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if "apply generateFrom_le" in text:
        text = text.replace(
            "apply generateFrom_le", "apply MeasurableSpace.generateFrom_le", 1)
        changed = True
        print("FunctionalAnalysis qualify measurable-space generation monotonicity: applied")
    elif "apply MeasurableSpace.generateFrom_le" in text:
        print("FunctionalAnalysis qualify measurable-space generation monotonicity: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass78.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
