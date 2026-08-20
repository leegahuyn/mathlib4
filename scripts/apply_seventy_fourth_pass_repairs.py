from __future__ import annotations

from pathlib import Path
import re

import apply_seventy_third_pass_repairs as pass73
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def _instantiate_completion_type(typ: str) -> str:
    return re.sub(
        r"\bC\b",
        "referenceAdvancedClaimsIICompletionCertificate",
        typ,
    )


def _replace_nullary_theorem_result(
    text: str, theorem: str, result_type: str
) -> tuple[str, bool]:
    start = text.index(f"theorem {theorem} :")
    result_start = text.index(":\n", start) + 2
    assignment = text.index(" :=\n", result_start)
    rendered = pass71._render_type(result_type)
    if text[result_start:assignment] == rendered:
        return text, False
    return text[:result_start] + rendered + text[assignment:], True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    actual = {
        "object": _instantiate_completion_type(pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "object_schema_actual_inputs_at")),
        "t1t5": _instantiate_completion_type(pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "t1t5_actual_inputs_at")),
        "kernel": _instantiate_completion_type(pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "kernel_actual_inputs_at")),
        "exact": _instantiate_completion_type(pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "exact_actual_inputs_at")),
        "padic": _instantiate_completion_type(pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "padic_actual_inputs_at")),
        "entropy": _instantiate_completion_type(pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "entropy_actual_inputs_at")),
        "spt": _instantiate_completion_type(pass71._theorem_result(
            text, "AdvancedClaimsIIClaimGroupAuditCertificate",
            "spt_actual_valuation_at")),
    }

    targets = {
        "reference_advanced_claims_ii_claimwise_actual_padic": actual["padic"],
        "reference_advanced_claims_ii_atomic_entropy_external_rows":
            "referenceAdvancedClaimsIICompletionCertificate.tables.paperTables."
            "externalScript.rows.length = 16",
        "reference_advanced_claims_ii_section_object_actual": actual["object"],
        "reference_advanced_claims_ii_section_t1t5_actual": actual["t1t5"],
        "reference_advanced_claims_ii_section_spt_actual": actual["spt"],
        "reference_advanced_claims_ii_section_kernel_actual": actual["kernel"],
        "reference_advanced_claims_ii_section_exact_actual": actual["exact"],
        "reference_advanced_claims_ii_section_padic_actual": actual["padic"],
        "reference_advanced_claims_ii_section_entropy_actual": actual["entropy"],
        "reference_advanced_claims_ii_actual_object_schema_inputs": actual["object"],
        "reference_advanced_claims_ii_actual_t1t5_inputs": actual["t1t5"],
        "reference_advanced_claims_ii_actual_kernel_inputs": actual["kernel"],
        "reference_advanced_claims_ii_actual_exact_inputs": actual["exact"],
        "reference_advanced_claims_ii_actual_padic_inputs": actual["padic"],
        "reference_advanced_claims_ii_actual_entropy_inputs": actual["entropy"],
    }
    applied = 0
    for theorem, typ in targets.items():
        text, did = _replace_nullary_theorem_result(text, theorem, typ)
        changed |= did
        applied += int(did)

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock1Advanced replace reference proof terms used as types: applied {applied}")
    else:
        print("Mock1Advanced replace reference proof terms used as types: already applied")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    (G.toCurvatureAlgebra).wedge U (g * A) B =
      g * ((G.toCurvatureAlgebra).wedge U A B : Ω U) := by
  change (g * A) * B = g * (A * B)
  exact mul_assoc g A B
""",
            """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    ((G.toCurvatureAlgebra).wedge U (g * A) B : Ω U) =
      g * ((G.toCurvatureAlgebra).wedge U A B : Ω U) := by
  simpa only [toCurvatureAlgebra] using (mul_assoc g A B)
""",
            "Mock2 expose both degree-two wedge values in the ambient ring",
        ),
        (
            """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    (G.toCurvatureAlgebra).wedge U A (B * g) =
      ((G.toCurvatureAlgebra).wedge U A B : Ω U) * g := by
  change A * (B * g) = (A * B) * g
  exact (mul_assoc A B g).symm
""",
            """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    ((G.toCurvatureAlgebra).wedge U A (B * g) : Ω U) =
      ((G.toCurvatureAlgebra).wedge U A B : Ω U) * g := by
  simpa only [toCurvatureAlgebra] using (mul_assoc A B g).symm
""",
            "Mock2 expose the right degree-two wedge value in the ambient ring",
        ),
        (
            """      multiplication_associative :=
        TruncatedGaugeCovariantDGA.multiplication_associative G
      multiplication_left_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_left_distributive G
      multiplication_right_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_right_distributive G
""",
            """      multiplication_associative :=
        TruncatedGaugeCovariantDGA.multiplication_associative (G := G)
      multiplication_left_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_left_distributive (G := G)
      multiplication_right_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_right_distributive (G := G)
""",
            "Mock2 supply the truncated DGA argument by name",
        ),
        (
            """private def chartFormAdd {n : ℕ} (a b : ChartForm n) : ChartForm n :=
""",
            """private noncomputable def chartFormAdd {n : ℕ} (a b : ChartForm n) : ChartForm n :=
""",
            "Mock2 mark chart-form addition noncomputable",
        ),
        (
            """private def chartFormNeg {n : ℕ} (a : ChartForm n) : ChartForm n :=
""",
            """private noncomputable def chartFormNeg {n : ℕ} (a : ChartForm n) : ChartForm n :=
""",
            "Mock2 mark chart-form negation noncomputable",
        ),
        (
            """  add_zero a := by ext <;> simp [chartFormAdd, chartFormZero]
  zero_add a := by ext <;> simp [chartFormAdd, chartFormZero]
  add_comm a b := by ext <;> simp [chartFormAdd, add_comm]
  add_assoc a b c := by ext <;> simp [chartFormAdd, add_assoc]
  neg_add_cancel a := by ext <;> simp [chartFormAdd, chartFormNeg, chartFormZero]
""",
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
            "Mock2 restrict additive extensionality to chart-form data fields",
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
            """  simp [GenuineGamma2Metaplectic.realMatrix, gamma2TranslationTwo,
    UpperHalfPlane.denom, ModularGroup.coe_T_zpow]
""",
            """  norm_num [GenuineGamma2Metaplectic.realMatrix,
    gamma2TranslationTwo, UpperHalfPlane.denom, pow_two,
    Matrix.mul_apply, Fin.sum_univ_two]
""",
            "Mock2Advanced compute the lower row of the concrete T-squared matrix",
        ),
        (
            """  rw [CongruenceSubgroup.Gamma_mem]
  norm_num
""",
            """  rw [CongruenceSubgroup.Gamma_mem]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num
""",
            "Mock2Advanced prove minus identity equals identity entrywise modulo two",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if "λ" in text:
        count = text.count("λ")
        text = text.replace("λ", "lam")
        changed = True
        print(f"Mock2Advanced rename reserved lambda-token binders: applied {count}")
    else:
        print("Mock2Advanced rename reserved lambda-token binders: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
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
        1,
        "FunctionalAnalysis cancel the remaining eta value after clearing denominators",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass73.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
