from __future__ import annotations

from pathlib import Path
import re

import apply_seventy_seventh_pass_repairs as pass77
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


def _move_block_before(text: str, start_marker: str, end_marker: str,
                       destination_marker: str, label: str) -> tuple[str, bool]:
    start = text.index(start_marker)
    end = text.index(end_marker, start)
    destination = text.index(destination_marker)
    if start < destination:
        block = text[start:end]
        text = text[:start] + text[end:]
        destination = text.index(destination_marker)
        text = text[:destination] + block + text[destination:]
        print(f"{label}: applied")
        return text, True
    print(f"{label}: already applied")
    return text, False


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = _move_block_before(
        text,
        "def claimGroupLeafStatements\n",
        "def promptObjectiveAudit\n",
        "def promptBulletStatement\n",
        "Mock1Advanced order claim-group audit before its leaf projection",
    )
    changed |= did

    text, did = _move_block_before(
        text,
        "theorem reference_advanced_claims_ii_reference_atomic_checklist :\n",
        "theorem reference_advanced_claims_ii_coverage_matrix :\n",
        "/-!\nFormula-level prompt ledger.\n",
        "Mock1Advanced place the reference atomic checklist after its helper theorems",
    )
    changed |= did

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
    projections = {
        "object_schema_payload_at": fields["object_schema_payload"],
        "t1t5_payload_at": fields["t1t5_payload"],
        "spt_payload_at": fields["spt_payload"],
        "kernel_payload_at": fields["kernel_payload"],
        "exact_payload_at": fields["exact_payload"],
        "padic_payload_at": fields["padic_payload"],
        "entropy_payload_at": fields["entropy_payload"],
    }
    applied = 0
    for theorem, typ in projections.items():
        text, did = pass73._replace_theorem_result(
            text, "AdvancedClaimsIIFormulaLevelPromptLedgerCertificate", theorem, typ)
        changed |= did
        applied += int(did)
    print(f"Mock1Advanced type formula-level ledger projections: applied {applied}" if applied
          else "Mock1Advanced type formula-level ledger projections: already applied")

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
            line_start = match.group(0)
            if "noncomputable" in line_start:
                return line_start
            count += 1
            return (f"{match.group('indent')}{match.group('prefix') or ''}noncomputable "
                    f"{match.group('kind')} {name}")
        text = pattern.sub(repl, text)
    return text, count


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    ((G.toCurvatureAlgebra).wedge U (g * A) B : Ω U) =
      g * ((G.toCurvatureAlgebra).wedge U A B : Ω U) := by
  simpa only [toCurvatureAlgebra] using (mul_assoc g A B)
""",
            """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U (g * A) B) =
      g * (show Ω U from (G.toCurvatureAlgebra).wedge U A B) := by
  simpa only [toCurvatureAlgebra] using (mul_assoc g A B)
""",
            "Mock2 force both left wedge values into the shared matrix carrier",
        ),
        (
            """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    ((G.toCurvatureAlgebra).wedge U A (B * g) : Ω U) =
      ((G.toCurvatureAlgebra).wedge U A B : Ω U) * g := by
  simpa only [toCurvatureAlgebra] using (mul_assoc A B g).symm
""",
            """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U A (B * g)) =
      (show Ω U from (G.toCurvatureAlgebra).wedge U A B) * g := by
  simpa only [toCurvatureAlgebra] using (mul_assoc A B g).symm
""",
            "Mock2 force both right wedge values into the shared matrix carrier",
        ),
        (
            """def ofCoordinates {X : Type u} [TopologicalSpace X]
    {U : TopologicalSpace.Opens X} (coordinate : X → ℂ)
    (s : LocalFramedSection U) : PolynomialBundleSection coordinate where
""",
            """def ofCoordinates {X : Type u} [TopologicalSpace X]
    {U : TopologicalSpace.Opens X} (coordinate : X → ℂ)
    (s : LocalFramedSection U) : PolynomialBundleSection (U := U) coordinate where
""",
            "Mock2 expose the open-set parameter in the polynomial bundle section",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    names = [
        "wedge", "restrictHom", "matrixWedge", "matrixDifferential",
        "matrixDifferentialHom", "zeroFormCoefficient", "zeroFormMatrix",
        "coordinateX", "dx", "gradedDGA", "curvatureAlgebra",
        "vectorDifferential", "matrixVectorWedge", "nabla", "nablaHom",
        "nablaBundleSection", "nablaOne", "curvature", "curvatureAction",
        "nablaSquared", "restrict", "identityZeroForm", "identity",
        "conjugateOne", "conjugateTwo", "pureGauge", "transformPotential",
        "transformConnection", "transformSection", "forwardSection", "zero",
    ]
    text, count = _mark_noncomputable(text, names)
    if count:
        changed = True
        print(f"Mock2 propagate noncomputability through polynomial chart constructions: applied {count}")
    else:
        print("Mock2 propagate noncomputability through polynomial chart constructions: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    change IsThetaCovariant
      (p : GenuineGamma2Metaplectic.Element × Circle).1
      (p : GenuineGamma2Metaplectic.Element × Circle).2 at p.property
    rw [← hbase]
    exact p.property
""",
            """    have hpCov := p.property
    change IsThetaCovariant
      (p : GenuineGamma2Metaplectic.Element × Circle).1
      (p : GenuineGamma2Metaplectic.Element × Circle).2 at hpCov
    rw [← hbase]
    exact hpCov
""",
            "Mock2Advanced name the subtype proof before changing its exposed type",
        ),
        (
            """      simp only [abelRemainder]
      ring
""",
            """      simp_rw [abelRemainder]
      ring
""",
            "Mock2Advanced unfold every finite Abel remainder under the sum",
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
  ring
""",
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
            "FunctionalAnalysis cancel the intermediate eta value after clearing denominators",
        ),
        (
            """      apply Matrix.SpecialLinearGroup.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp_all).countable
""",
            """      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all).countable
""",
            "FunctionalAnalysis prove matrix equality entrywise after special-linear extensionality",
        ),
        (
            """abbrev hyperbolicMeasure : Measure ℍ :=
  volume
""",
            """noncomputable abbrev hyperbolicMeasure : Measure ℍ :=
  volume
""",
            "FunctionalAnalysis mark the chosen hyperbolic measure abbreviation noncomputable",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if "Set.frontier" in text:
        count = text.count("Set.frontier")
        text = text.replace("Set.frontier", "frontier")
        changed = True
        print(f"FunctionalAnalysis use the current unnamespaced frontier constant: applied {count}")
    else:
        print("FunctionalAnalysis use the current unnamespaced frontier constant: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass77.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
