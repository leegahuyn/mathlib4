from __future__ import annotations

from pathlib import Path
import re

import apply_seventieth_pass_repairs as pass70

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass70.replace_exact


def _structure_fields(text: str, name: str) -> dict[str, str]:
    start = text.index(f"structure {name}")
    try:
        end = text.index(f"\nnamespace {name}", start)
    except ValueError:
        end = text.find("\nstructure ", start + 10)
        if end < 0:
            end = len(text)
    block = text[start:end]
    body = block[block.index(" where\n") + len(" where\n"):]
    starts = list(re.finditer(
        r"^  ([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(.*)$", body, re.M))
    result: dict[str, str] = {}
    for index, match in enumerate(starts):
        stop = starts[index + 1].start() if index + 1 < len(starts) else len(body)
        lines = body[match.start():stop].rstrip().splitlines()
        first = lines[0].split(":", 1)[1].strip()
        continuation = [
            line[4:] if line.startswith("    ") else line.lstrip()
            for line in lines[1:]
        ]
        result[match.group(1)] = "\n".join(
            ([first] if first else []) + continuation).rstrip()
    return result


def _render_type(typ: str, indent: str = "    ") -> str:
    return indent + ("\n" + indent).join(typ.splitlines())


def _theorem_result(text: str, namespace: str, theorem: str) -> str:
    ns = text.index(f"namespace {namespace}")
    start = text.index(f"theorem {theorem}\n", ns)
    assignment = text.index(" :=\n", start)
    signature = text[start:assignment]
    delimiter = ") :\n"
    result_start = signature.rfind(delimiter)
    if result_start < 0:
        raise RuntimeError(f"cannot parse {namespace}.{theorem}")
    return signature[result_start + len(delimiter):]


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    pattern = re.compile(
        r"(theorem\s+([A-Za-z_][A-Za-z0-9_']*)\n"
        r"\s*\{C : AdvancedClaimsIICompletionCertificate\}\n"
        r"\s*\(([A-Z]) : ([A-Za-z_][A-Za-z0-9_']*) C\)) : _ :=\n"
        r"\s*\3\.([A-Za-z_][A-Za-z0-9_']*)",
        re.M,
    )
    matches = list(pattern.finditer(text))
    if matches:
        if len(matches) != 66:
            raise RuntimeError(
                f"Mock1Advanced expected 66 inferred projection types, got {len(matches)}")
        cache: dict[str, dict[str, str]] = {}

        def repl(match: re.Match[str]) -> str:
            struct = match.group(4)
            field = match.group(5)
            fields = cache.setdefault(struct, _structure_fields(text, struct))
            if field not in fields:
                raise RuntimeError(f"{struct}: missing field {field}")
            return (match.group(1) + " :\n" + _render_type(fields[field]) +
                    " :=\n  " + match.group(3) + "." + field)

        text = pattern.sub(repl, text)
        changed = True
        print("Mock1Advanced restore 66 projection theorem result types: applied")
    elif ") : _ :=" not in text:
        print("Mock1Advanced restore projection theorem result types: already applied")
    else:
        raise RuntimeError("Mock1Advanced unexpected inferred theorem placeholders remain")

    structure_start = text.index(
        "structure AdvancedClaimsIIClaimwiseMathematicalClosureCertificate")
    structure_end = text.index(
        "\nnamespace AdvancedClaimsIIClaimwiseMathematicalClosureCertificate",
        structure_start,
    )
    block = text[structure_start:structure_end]
    theorem_fields = [
        ("object_schema_actual_inputs", "object_schema_actual_inputs_at"),
        ("t1t5_actual_inputs", "t1t5_actual_inputs_at"),
        ("kernel_actual_inputs", "kernel_actual_inputs_at"),
        ("exact_actual_inputs", "exact_actual_inputs_at"),
        ("padic_actual_inputs", "padic_actual_inputs_at"),
        ("entropy_actual_inputs", "entropy_actual_inputs_at"),
    ]
    repaired = 0
    for field, theorem in theorem_fields:
        old = (
            f"  {field} :\n"
            f"    AdvancedClaimsIIActualInputAuditCertificate.{theorem}\n"
            f"      actual_input_audit"
        )
        if old in block:
            typ = _theorem_result(
                text, "AdvancedClaimsIIActualInputAuditCertificate", theorem)
            block = block.replace(old, f"  {field} :\n" + _render_type(typ), 1)
            repaired += 1
    if repaired:
        if repaired != 6:
            raise RuntimeError(
                f"Mock1Advanced expected six proof-as-type repairs, got {repaired}")
        text = text[:structure_start] + block + text[structure_end:]
        changed = True
        print("Mock1Advanced replace six proof terms used as field types: applied")
    elif "AdvancedClaimsIIActualInputAuditCertificate.object_schema_actual_inputs_at" not in block:
        print("Mock1Advanced replace proof terms used as field types: already applied")
    else:
        raise RuntimeError("Mock1Advanced proof-as-type fields did not match")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    (resolutionAtOne M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
""",
            """    (resolutionAtOne M).Exact := by
  unfold resolutionAtOne
  rw [ShortComplex.moduleCat_exact_iff]
""",
            "Mock2 unfold the degree-one short complex before introducing its carrier",
        ),
        (
            """      rw [tensorResolutionComplex_d_two_one]
      rw [comp_zero])
""",
            """      rw [tensorResolutionComplex_d_two_one]
      rw [comp_zero, zero_comp])
""",
            "Mock2 normalize both sides of the zero differential square",
        ),
        (
            """    { predicate_restriction_stable := fun hUV {A} hA =>
        lemma6_1_covariance_restrict F Covariant hCov hUV hA
""",
            """    { predicate_restriction_stable := by
        intro U V hUV A hA
        exact lemma6_1_covariance_restrict F Covariant hCov hUV hA
""",
            "Mock2 introduce every implicit binder of predicate restriction stability",
        ),
        (
            """      lemma6_1 := fun hVU {A} hA =>
        lemma6_1_restriction_stability F Covariant hCov hVU hA
""",
            """      lemma6_1 := by
        intro V U hVU A hA
        exact lemma6_1_restriction_stability F Covariant hCov hVU hA
""",
            "Mock2 introduce every implicit binder of the Aq restriction theorem",
        ),
        (
            """theorem existsUnique_gluing {ι : Type u} (C : OpenCoverData X ι)
""",
            """theorem existsUnique_gluing (hF : IsSheafLike F)
    {ι : Type u} (C : OpenCoverData X ι)
""",
            "Mock2 make the sheaf witness explicit in existsUnique_gluing",
        ),
        (
            """theorem global_gluing_unique {ι : Type u}
""",
            """theorem global_gluing_unique (hF : IsSheafLike F) {ι : Type u}
""",
            "Mock2 make the sheaf witness explicit in global_gluing_unique",
        ),
        (
            """theorem global_existsUnique_gluing {ι : Type u}
""",
            """theorem global_existsUnique_gluing (hF : IsSheafLike F) {ι : Type u}
""",
            "Mock2 make the sheaf witness explicit in global_existsUnique_gluing",
        ),
        (
            """      (C.curvature Aglobal) := by
  intro i
  calc
    C.res 2 (K.piece_le_target i) (C.curvature Aglobal) =
""",
            """      (C.curvature Aglobal) := by
  intro i
  change C.res 2 (K.piece_le_target i) (C.curvature Aglobal) =
    C.curvature (A i)
  calc
    C.res 2 (K.piece_le_target i) (C.curvature Aglobal) =
""",
            "Mock2 expose the curvature-family component before the calc chain",
        ),
        (
            """    _ = C.curvature (A i) :=
      congrArg (fun a : C.Form 1 (K.piece i) => C.curvature a) (hA i)
    _ = C.curvatureFamily K A i := rfl
""",
            """    _ = C.curvature (A i) :=
      congrArg (fun a : C.Form 1 (K.piece i) => C.curvature a) (hA i)
""",
            "Mock2 remove the definitionally redundant final curvature calc step",
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
            """theorem group_inv_mul (a : Element) :
    a⁻¹ * a = 1 :=
  inv_mul a
""",
            """theorem group_inv_mul (a : Element) :
    a⁻¹ * a = 1 := by
  simp
""",
            "Mock2Advanced use the group simplifier for inverse multiplication",
        ),
        (
            """      apply b.sqrtFactor_ne_zero τ
      exact CharZero.eq_neg_self_iff.mp (heq.symm.trans hneg)
""",
            """      exact (sqrtFactor_ne_zero b τ)
        (CharZero.eq_neg_self_iff.mp (heq.symm.trans hneg))
""",
            "Mock2Advanced call the square-root nonvanishing theorem explicitly",
        ),
        (
            """  · simp only [matrix_mul, deckNeg_matrix, one_mul]
""",
            """  · simp only [matrix_mul, matrix_one, deckNeg_matrix, one_mul]
""",
            "Mock2Advanced include the matrix projection of one",
        ),
        (
            """  rw [a.im_gamma2Act_eq_div_norm_sqrtFactor_pow_four,
""",
            """  rw [im_gamma2Act_eq_div_norm_sqrtFactor_pow_four a,
""",
            "Mock2Advanced call the imaginary-part theorem explicitly",
        ),
    ]
    for old, new, label in replacements:
        count = 2 if label == "Mock2Advanced call the imaginary-part theorem explicitly" else 1
        text, did = replace_exact(text, old, new, count, label)
        changed |= did

    text, did = replace_exact(
        text,
        """a.sqrtFactor_ne_zero""",
        """sqrtFactor_ne_zero a""",
        7,
        "Mock2Advanced replace seven remaining square-root field-notation calls",
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
        """  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
        """  field_simp [ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
""",
        1,
        "FunctionalAnalysis clear the residual eta quotient after cancellation",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
