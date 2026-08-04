from __future__ import annotations

from pathlib import Path
import re

import apply_seventy_second_pass_repairs as pass72
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def _replace_theorem_result(
    text: str, namespace: str, theorem: str, result_type: str
) -> tuple[str, bool]:
    ns_start = text.index(f"namespace {namespace}")
    ns_end = text.index(f"end {namespace}", ns_start)
    start = text.index(f"theorem {theorem}\n", ns_start, ns_end)
    assignment = text.index(" :=\n", start, ns_end)
    signature = text[start:assignment]
    delimiter = ") :\n"
    result_start = signature.rfind(delimiter)
    if result_start < 0:
        raise RuntimeError(f"{namespace}.{theorem}: result delimiter absent")
    absolute = start + result_start + len(delimiter)
    current = text[absolute:assignment]
    rendered = pass71._render_type(result_type)
    if current == rendered:
        return text, False
    return text[:absolute] + rendered + text[assignment:], True


def _replace_structure_field_type(
    text: str, structure: str, field: str, result_type: str
) -> tuple[str, bool]:
    start = text.index(f"structure {structure}")
    try:
        end = text.index(f"\nnamespace {structure}", start)
    except ValueError:
        end = text.find("\nstructure ", start + 10)
        if end < 0:
            end = len(text)
    marker = f"  {field} :\n"
    field_start = text.index(marker, start, end)
    body_start = field_start + len(marker)
    next_field = re.search(r"^  [A-Za-z_][A-Za-z0-9_']*\s*:", text[body_start:end], re.M)
    body_end = body_start + next_field.start() if next_field else end
    rendered = pass71._render_type(result_type) + "\n"
    if text[body_start:body_end] == rendered:
        return text, False
    return text[:body_start] + rendered + text[body_end:], True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    actual = {
        "object_schema_actual_inputs_at": pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "object_schema_actual_inputs_at"),
        "t1t5_actual_inputs_at": pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "t1t5_actual_inputs_at"),
        "kernel_actual_inputs_at": pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "kernel_actual_inputs_at"),
        "exact_actual_inputs_at": pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "exact_actual_inputs_at"),
        "padic_actual_inputs_at": pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "padic_actual_inputs_at"),
        "entropy_actual_inputs_at": pass71._theorem_result(
            text, "AdvancedClaimsIIActualInputAuditCertificate",
            "entropy_actual_inputs_at"),
    }
    spt_type = pass71._theorem_result(
        text, "AdvancedClaimsIIClaimGroupAuditCertificate",
        "spt_actual_valuation_at")

    claimwise_theorems = {
        "object_schema_actual_inputs_at": actual["object_schema_actual_inputs_at"],
        "t1t5_actual_inputs_at": actual["t1t5_actual_inputs_at"],
        "kernel_actual_inputs_at": actual["kernel_actual_inputs_at"],
        "exact_actual_inputs_at": actual["exact_actual_inputs_at"],
        "padic_actual_inputs_at": actual["padic_actual_inputs_at"],
        "entropy_actual_inputs_at": actual["entropy_actual_inputs_at"],
    }
    for theorem, typ in claimwise_theorems.items():
        text, did = _replace_theorem_result(
            text,
            "AdvancedClaimsIIClaimwiseMathematicalClosureCertificate",
            theorem,
            typ,
        )
        changed |= did

    spine_fields = {
        "object_actual": actual["object_schema_actual_inputs_at"],
        "t1t5_actual": actual["t1t5_actual_inputs_at"],
        "spt_actual_valuation": spt_type,
        "kernel_actual": actual["kernel_actual_inputs_at"],
        "exact_actual": actual["exact_actual_inputs_at"],
        "padic_actual": actual["padic_actual_inputs_at"],
        "entropy_actual": actual["entropy_actual_inputs_at"],
    }
    for field, typ in spine_fields.items():
        text, did = _replace_structure_field_type(
            text, "AdvancedClaimsIIObjectiveCategorySpineCertificate", field, typ)
        changed |= did

    spine_theorems = {
        "object_actual_at": actual["object_schema_actual_inputs_at"],
        "t1t5_actual_at": actual["t1t5_actual_inputs_at"],
        "spt_actual_valuation_at": spt_type,
        "kernel_actual_at": actual["kernel_actual_inputs_at"],
        "exact_actual_at": actual["exact_actual_inputs_at"],
        "padic_actual_at": actual["padic_actual_inputs_at"],
        "entropy_actual_at": actual["entropy_actual_inputs_at"],
    }
    for theorem, typ in spine_theorems.items():
        text, did = _replace_theorem_result(
            text, "AdvancedClaimsIIObjectiveCategorySpineCertificate", theorem, typ)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1Advanced replace twenty proof terms used as theorem or field types: applied")
    else:
        print("Mock1Advanced replace proof terms used as theorem or field types: already applied")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  admissible := by
    simpa only [Units.coe_map] using
      G.gaugeAdmissible_restrict hUV (g.unit : Ω V) g.admissible
""",
            """  admissible := by
    change G.gaugeAdmissible U (G.res hUV (g.unit : Ω V))
    exact G.gaugeAdmissible_restrict hUV (g.unit : Ω V) g.admissible
""",
            "Mock2 expose the restricted unit through the ring homomorphism",
        ),
        (
            """    (G.toCurvatureAlgebra).wedge U (g * A) B =
      g * (G.toCurvatureAlgebra).wedge U A B := by
""",
            """    (G.toCurvatureAlgebra).wedge U (g * A) B =
      g * ((G.toCurvatureAlgebra).wedge U A B : Ω U) := by
""",
            "Mock2 type the degree-two wedge result for left multiplication",
        ),
        (
            """    (G.toCurvatureAlgebra).wedge U A (B * g) =
      (G.toCurvatureAlgebra).wedge U A B * g := by
""",
            """    (G.toCurvatureAlgebra).wedge U A (B * g) =
      ((G.toCurvatureAlgebra).wedge U A B : Ω U) * g := by
""",
            "Mock2 type the degree-two wedge result for right multiplication",
        ),
        (
            """      multiplication_associative := G.multiplication_associative
      multiplication_left_distributive := G.multiplication_left_distributive
      multiplication_right_distributive := G.multiplication_right_distributive
""",
            """      multiplication_associative :=
        TruncatedGaugeCovariantDGA.multiplication_associative G
      multiplication_left_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_left_distributive G
      multiplication_right_distributive :=
        TruncatedGaugeCovariantDGA.multiplication_right_distributive G
""",
            "Mock2 call the multiplication laws without invalid field notation",
        ),
        (
            """private def chartFormZero (n : ℕ) : ChartForm n :=
""",
            """private noncomputable def chartFormZero (n : ℕ) : ChartForm n :=
""",
            "Mock2 mark the polynomial-valued zero chart form noncomputable",
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
        """theorem continuous_factor
    (ν : Multiplier)
    (a : GenuineGamma2Metaplectic.Element) :
    Continuous (factor ν a) := by
  simpa only [factor] using
    (continuous_const.mul a.continuous_sqrtFactor)
""",
        """theorem continuous_factor
    (ν : Multiplier)
    (a : GenuineGamma2Metaplectic.Element) :
    Continuous (factor ν a) := by
  change Continuous (fun τ : UpperHalfPlane =>
    (ν a : ℂ) * a.sqrtFactor τ)
  exact continuous_const.mul a.continuous_sqrtFactor
""",
        1,
        "Mock2Advanced expose the genuine factor as a pointwise product",
    )
    changed |= did

    start = text.index("namespace StartingIntegralIdentity")
    end = text.index("end StartingIntegralIdentity", start)
    block = text[start:end]
    if re.search(r"\binclude\b", block):
        block = re.sub(r"\binclude\b", "incl", block)
        block = block.replace(
            "  incl : T →L[ℂ] V\n  include_injective : Function.Injective incl\n",
            "  «include» : T →L[ℂ] V\n  include_injective : Function.Injective «include»\n",
            1,
        )
        block = block.replace(
            "    realization (incl t) = testRealization t\n",
            "    realization («include» t) = testRealization t\n",
            1,
        )
        block = block.replace("I.incl", "I.«include»")
        text = text[:start] + block + text[end:]
        changed = True
        print("Mock2Advanced escape the public include field and rename local include binders: applied")
    elif "«include»" in block:
        print("Mock2Advanced escape the public include field and rename local include binders: already applied")
    else:
        raise RuntimeError("Mock2Advanced StartingIntegralIdentity include binders absent")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  field_simp [ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
""",
        """  ring
""",
        1,
        "FunctionalAnalysis finish the cleared eta cocycle by ring normalization",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass72.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
