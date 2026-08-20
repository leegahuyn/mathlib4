from __future__ import annotations

from pathlib import Path
import re

import apply_seventy_fourth_pass_repairs as pass74
import apply_seventy_third_pass_repairs as pass73
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def _ref_type(text: str, namespace: str, theorem: str) -> str:
    typ = pass71._theorem_result(text, namespace, theorem)
    return re.sub(r"\bC\b", "referenceAdvancedClaimsIICompletionCertificate", typ)


def _conj(*types: str) -> str:
    return " /\\\n".join(f"({typ})" for typ in types)


def _forall(binder: str, typ: str) -> str:
    return f"forall {binder},\n  {typ}"


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    rem = "RemainingAdvancedClaimPayloadCertificate"
    paper = "PaperDataInstancePayloadCertificate"
    spt = "SPTKernelRequirementPayloadCertificate"

    fields = {
        "remaining_registry_eq_all": _ref_type(text, rem, "claim_registry_eq_all_at"),
        "remaining_claim_covered": _forall(
            "claim : RemainingAdvancedClaim",
            _ref_type(text, rem, "claim_registry_at")),
        "remaining_object_coefficient": _forall(
            "n : Nat", _ref_type(text, rem, "object_coefficient_schema_at")),
        "remaining_scalar_flags": _conj(
            _ref_type(text, rem, "scalar_ellStar_zero_at"),
            _ref_type(text, rem, "scalar_weights_two_sign_at"),
            _ref_type(text, rem, "scalar_usesScalar_true_at")),
        "remaining_scalar_relation": _forall(
            "n : Nat", _ref_type(text, rem, "scalar_jacobi_at")),
        "remaining_rational_solve_rows": _conj(
            _ref_type(text, rem, "rational_solve_matrix_rows_at"),
            _ref_type(text, rem, "rational_solve_rhs_rows_at"),
            _ref_type(text, rem, "rational_solve_solution_columns_at")),
        "remaining_rational_solve": _ref_type(
            text, rem, "principal_part_rational_solve_at"),
        "remaining_completion_shadow": _ref_type(
            text, rem, "completion_shadow_holomorphic_at"),
        "remaining_cusp_transport": _ref_type(text, rem, "cusp_transport_at"),
        "remaining_appell_lerch": _ref_type(text, rem, "appell_lerch_block_formula_at"),
        "remaining_principal_exponent": _ref_type(
            text, rem, "principal_exponent_formula_at"),
        "remaining_fixed_shadow": _ref_type(
            text, rem, "fixed_shadow_unary_theta_at"),
        "remaining_inside_outside": _forall(
            "n : Nat", _ref_type(text, rem, "inside_outside_qseries_at")),
        "paper_registry_atoms": _conj(
            _ref_type(text, paper, "registry_eq_all_at"),
            _ref_type(text, paper, "registry_name_nonempty_at"),
            _ref_type(text, paper, "registry_source_nonempty_at")),
        "paper_object_schema_atoms": _conj(
            _ref_type(text, paper, "schema_object_name_at"),
            _ref_type(text, paper, "schema_family_object_name_at"),
            _ref_type(text, paper, "schema_concrete_object_at"),
            _ref_type(text, paper, "coefficient_schema_eq_object_schema_at")),
        "paper_instance_atoms": _conj(
            _ref_type(text, paper, "paper_instance_concrete_at"),
            _ref_type(text, paper, "paper_instance_family_at"),
            _ref_type(text, paper, "paper_instance_object_name_at"),
            _ref_type(text, paper, "paper_instance_family_name_at"),
            _ref_type(text, paper, "paper_instance_source_nonempty_at")),
        "paper_family_atoms": _conj(
            _ref_type(text, paper, "family_weight_numerator_at"),
            _ref_type(text, paper, "family_weight_denominator_at"),
            _ref_type(text, paper, "family_level_positive_at"),
            _ref_type(text, paper, "family_qShift_zero_at"),
            _ref_type(text, paper, "family_working_cusp_at"),
            _ref_type(text, paper, "family_transported_cusp_at"),
            _ref_type(text, paper, "family_z0_at")),
        "paper_matrix_atoms": _conj(
            _ref_type(text, paper, "matrix_source_nonempty_at"),
            _ref_type(text, paper, "matrix_rows_at"),
            _ref_type(text, paper, "matrix_rhs_rows_at"),
            _ref_type(text, paper, "matrix_solution_columns_at")),
        "paper_appell_atoms": _conj(
            _ref_type(text, paper, "appell_source_nonempty_at"),
            _ref_type(text, paper, "appell_m_mem_at"),
            _ref_type(text, paper, "appell_r_mem_at"),
            _ref_type(text, paper, "appell_tauCoeff_diff_zero_at"),
            _ref_type(text, paper, "appell_constDiff_eq_z0_at")),
        "paper_fixed_shadow_atoms": _conj(
            _ref_type(text, paper, "fixed_shadow_source_nonempty_at"),
            _ref_type(text, paper, "fixed_shadow_symbol_nonempty_at"),
            _ref_type(text, paper, "fixed_shadow_z0_at"),
            _ref_type(text, paper, "fixed_shadow_nonzero_case_at"),
            _ref_type(text, paper, "fixed_shadow_scale_nonzero_at")),
        "spt_arithmetic_atoms": _conj(
            _ref_type(text, spt, "nat_gcd_lcm_at"),
            _ref_type(text, spt, "primewise_thickness_at"),
            _ref_type(text, spt, "valuation_certificate_at"),
            _ref_type(text, spt, "obstruction_failure_at")),
    }

    applied = 0
    for field, typ in fields.items():
        text, did = pass73._replace_structure_field_type(
            text, "AdvancedClaimsIIReferenceAtomicChecklistCertificate", field, typ)
        changed |= did
        applied += int(did)

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock1Advanced type the first reference atomic checklist field batch: applied {applied}")
    else:
        print("Mock1Advanced type the first reference atomic checklist field batch: already applied")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """      multiplication_associative :=
        TruncatedGaugeCovariantDGA.multiplication_associative (G := G)
      multiplication_left_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_left_distributive (G := G)
      multiplication_right_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_right_distributive (G := G)
""",
            """      multiplication_associative :=
        TruncatedGaugeCovariantDGA.multiplication_associative
      multiplication_left_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_left_distributive
      multiplication_right_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_right_distributive
""",
            "Mock2 use the multiplication laws that do not retain the unused DGA parameter",
        ),
        (
            """instance chartFormAddCommGroup (n : ℕ) : AddCommGroup (ChartForm n) where
""",
            """noncomputable instance chartFormAddCommGroup (n : ℕ) : AddCommGroup (ChartForm n) where
""",
            "Mock2 mark the chart-form additive instance noncomputable",
        ),
        (
            """  add_zero a := by
    apply ChartForm.ext <;> simp [chartFormAdd, chartFormZero]
  zero_add a := by
    apply ChartForm.ext <;> simp [chartFormAdd, chartFormZero]
  add_comm a b := by
    apply ChartForm.ext <;> simp [chartFormAdd, add_comm]
  add_assoc a b c := by
    apply ChartForm.ext <;> simp [chartFormAdd, add_assoc]
  neg_add_cancel a := by
    apply ChartForm.ext <;> simp [chartFormAdd, chartFormNeg, chartFormZero]
""",
            """  add_zero a := by
    apply ChartForm.ext
    · change a.c0 + 0 = a.c0; exact add_zero _
    · change a.cx + 0 = a.cx; exact add_zero _
    · change a.cy + 0 = a.cy; exact add_zero _
    · change a.cxy + 0 = a.cxy; exact add_zero _
  zero_add a := by
    apply ChartForm.ext
    · change 0 + a.c0 = a.c0; exact zero_add _
    · change 0 + a.cx = a.cx; exact zero_add _
    · change 0 + a.cy = a.cy; exact zero_add _
    · change 0 + a.cxy = a.cxy; exact zero_add _
  add_comm a b := by
    apply ChartForm.ext
    · change a.c0 + b.c0 = b.c0 + a.c0; exact add_comm _ _
    · change a.cx + b.cx = b.cx + a.cx; exact add_comm _ _
    · change a.cy + b.cy = b.cy + a.cy; exact add_comm _ _
    · change a.cxy + b.cxy = b.cxy + a.cxy; exact add_comm _ _
  add_assoc a b c := by
    apply ChartForm.ext
    · change (a.c0 + b.c0) + c.c0 = a.c0 + (b.c0 + c.c0); exact add_assoc _ _ _
    · change (a.cx + b.cx) + c.cx = a.cx + (b.cx + c.cx); exact add_assoc _ _ _
    · change (a.cy + b.cy) + c.cy = a.cy + (b.cy + c.cy); exact add_assoc _ _ _
    · change (a.cxy + b.cxy) + c.cxy = a.cxy + (b.cxy + c.cxy); exact add_assoc _ _ _
  neg_add_cancel a := by
    apply ChartForm.ext
    · change -a.c0 + a.c0 = 0; exact neg_add_cancel _
    · change -a.cx + a.cx = 0; exact neg_add_cancel _
    · change -a.cy + a.cy = 0; exact neg_add_cancel _
    · change -a.cxy + a.cxy = 0; exact neg_add_cancel _
""",
            "Mock2 prove chart-form additive laws field by field",
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
            """  rw [CongruenceSubgroup.Gamma_mem]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num
""",
            """  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [show (-1 : ZMod 2) = 1 by decide]
""",
            "Mock2Advanced normalize minus one in the characteristic-two target",
        ),
        (
            """  exact Metric.mem_sphere_zero_iff_norm.mpr (by
    simp only [norm_neg, Complex.norm_I])
""",
            """  exact (mem_sphere_zero_iff_norm).mpr (by
    simp only [norm_neg, Complex.norm_I])
""",
            "Mock2Advanced use the current unnamespaced sphere membership lemma for minus I",
        ),
        (
            """  exact Metric.mem_sphere_zero_iff_norm.mpr (by norm_num)
""",
            """  exact (mem_sphere_zero_iff_norm).mpr (by norm_num)
""",
            "Mock2Advanced use the current unnamespaced sphere membership lemma for minus one",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    aliases = [
        "globalPoincare_sq_def2_1",
        "orderedKernel_and_bound_def2_2",
        "lemma37_nonnegativity_proved",
        "proposition1_holder_proved",
    ]
    for name in aliases:
        old = f"theorem {name} := @"
        new = f"def {name} := @"
        if old in text:
            text = text.replace(old, new, 1)
            changed = True
            print(f"Mock2Advanced make inferred proof alias {name} a definition: applied")
        elif new in text:
            print(f"Mock2Advanced make inferred proof alias {name} a definition: already applied")
        else:
            raise RuntimeError(f"Mock2Advanced inferred alias {name} absent")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    if "import Mathlib.Topology.Maps.Basic\n" not in text:
        marker = "import Mathlib.Topology.Constructions\n"
        if marker not in text:
            raise RuntimeError("FunctionalAnalysis topology import marker absent")
        text = text.replace(marker, marker + "import Mathlib.Topology.Maps.Basic\n", 1)
        changed = True
        print("FunctionalAnalysis import the current closed-embedding API: applied")

    text, did = replace_exact(
        text,
        """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
        """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
""",
        1,
        "FunctionalAnalysis let field_simp close the inverse-eta cocycle directly",
    )
    changed |= did

    if "noncomputable instance gammaTwoCountable : Countable GammaTwo" not in text:
        marker = """/-- The effective image is countable because it is a quotient image of the
countable matrix group `Gamma(2)`. -/
"""
        insertion = """noncomputable instance gammaTwoCountable : Countable GammaTwo :=
  Countable.of_injective
    (fun γ : GammaTwo =>
      ((((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
       (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
       (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
       (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1))
    (by
      intro a b h
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp_all)

"""
        if marker not in text:
            raise RuntimeError("FunctionalAnalysis countability insertion marker absent")
        text = text.replace(marker, insertion + marker, 1)
        changed = True
        print("FunctionalAnalysis construct countability of GammaTwo from its four integer entries: applied")

    text, did = replace_exact(
        text,
        """    intro z
    simpa only [gammaTwoEffectiveElement_smul] using (hγ z).symm
""",
        """    intro z
    change gammaTwoEffectiveElement γ z = a z
    exact (hγ z).symm
""",
        1,
        "FunctionalAnalysis compare effective transformations as functions",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass74.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
