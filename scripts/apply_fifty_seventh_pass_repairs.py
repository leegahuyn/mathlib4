from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(
    text: str, old: str, new: str, expected: int, label: str
) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        print(f"{label}: source changed; skipped")
        return text, False
    raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")


def theorem_statement(text: str, namespace: str, theorem: str) -> str:
    ns_start = text.find(f"namespace {namespace}")
    if ns_start < 0:
        raise RuntimeError(f"namespace {namespace}: not found")
    ns_end = text.find(f"end {namespace}", ns_start)
    if ns_end < 0:
        raise RuntimeError(f"namespace {namespace}: end marker not found")
    pos = text.find(f"theorem {theorem}", ns_start, ns_end)
    if pos < 0:
        raise RuntimeError(f"{namespace}.{theorem}: declaration not found")

    lines = text[pos:].splitlines()
    return_start = None
    for i, line in enumerate(lines[1:], 1):
        if line.rstrip().endswith(") :"):
            return_start = i + 1
            break
    if return_start is None:
        raise RuntimeError(f"{namespace}.{theorem}: return type start not found")

    result: list[str] = []
    for line in lines[return_start:]:
        if ":=" in line:
            before = line.split(":=", 1)[0].rstrip()
            if before:
                result.append(before)
            break
        result.append(line.rstrip())
    while result and not result[0].strip():
        result.pop(0)
    if not result:
        raise RuntimeError(f"{namespace}.{theorem}: empty return type")
    return "\n".join(result)


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start_marker = "structure AdvancedClaimsIIRequirementLeafLedger"
    end_marker = "namespace AdvancedClaimsIIRequirementLeafLedger"
    start = text.find(start_marker)
    end = text.find(end_marker, start)
    if start < 0 or end < 0:
        raise RuntimeError("Mock1Advanced leaf-ledger structure markers not found")
    block = text[start:end]

    declarations = [
        ("PaperDataInstancePayloadCertificate", "paper_object_instance_at"),
        ("RemainingAdvancedClaimPayloadCertificate", "principal_part_rational_solve_at"),
        ("RemainingAdvancedClaimPayloadCertificate", "completion_shadow_holomorphic_at"),
        ("RemainingAdvancedClaimPayloadCertificate", "cusp_transport_at"),
        ("PaperDataInstancePayloadCertificate", "appell_lerch_at"),
        ("PaperDataInstancePayloadCertificate", "principal_exponent_at"),
        ("PaperDataInstancePayloadCertificate", "matrix_solution_at"),
        ("PaperDataInstancePayloadCertificate", "fixed_shadow_at"),
        ("PaperDataInstancePayloadCertificate", "inside_outside_at"),
        ("SPTKernelRequirementPayloadCertificate", "nat_gcd_lcm_at"),
        ("SPTKernelRequirementPayloadCertificate", "primewise_thickness_at"),
        ("SPTKernelRequirementPayloadCertificate", "valuation_certificate_at"),
        ("SPTKernelRequirementPayloadCertificate", "obstruction_failure_at"),
        ("SPTKernelRequirementPayloadCertificate", "base_change_at"),
        ("SPTKernelRequirementPayloadCertificate", "kernel_selection_at"),
        ("SPTKernelRequirementPayloadCertificate", "multiplier_phase_at"),
        ("SPTKernelRequirementPayloadCertificate", "cusp_convergence_at"),
        ("SPTKernelRequirementPayloadCertificate", "transport_family_at"),
        ("SPTKernelRequirementPayloadCertificate", "kernel_table_at"),
        ("SPTKernelRequirementPayloadCertificate", "multiplier_input_at"),
        ("SPTKernelRequirementPayloadCertificate", "cusp_input_at"),
        ("SPTKernelRequirementPayloadCertificate", "transport_across_cusps_at"),
        ("ExactCoefficientRequirementPayloadCertificate", "coefficient_separation_at"),
        ("ExactCoefficientRequirementPayloadCertificate", "theta_character_at"),
        ("ExactCoefficientRequirementPayloadCertificate", "spectral_kloosterman_at"),
        ("ExactCoefficientRequirementPayloadCertificate", "local_euler_at"),
        ("ExactCoefficientRequirementPayloadCertificate", "root_filter_at"),
        ("ExactCoefficientRequirementPayloadCertificate", "exact_formula_at"),
        ("ExactCoefficientRequirementPayloadCertificate", "paper_formula_fields_at"),
        ("PAdicRequirementPayloadCertificate", "normalization_at"),
        ("PAdicRequirementPayloadCertificate", "overlap_at"),
        ("PAdicRequirementPayloadCertificate", "mahler_at"),
        ("PAdicRequirementPayloadCertificate", "tail_zero_at"),
        ("PAdicRequirementPayloadCertificate", "face_tracking_at"),
        ("PAdicRequirementPayloadCertificate", "denominator_data_at"),
        ("PAdicRequirementPayloadCertificate", "chart_vectors_at"),
        ("PAdicRequirementPayloadCertificate", "mahler_table_at"),
        ("PAdicRequirementPayloadCertificate", "predicate_at"),
        ("PAdicRequirementPayloadCertificate", "obstruction_failure_at"),
        ("EntropyReproRequirementPayloadCertificate", "regression_cardy_at"),
        ("EntropyReproRequirementPayloadCertificate", "rademacher_tail_at"),
        ("EntropyReproRequirementPayloadCertificate", "entropy_cardy_wrapper_at"),
        ("EntropyReproRequirementPayloadCertificate", "alpha_extraction_at"),
        ("EntropyReproRequirementPayloadCertificate", "degeneracy_at"),
        ("EntropyReproRequirementPayloadCertificate", "ols_interval_at"),
        ("EntropyReproRequirementPayloadCertificate", "growth_stability_at"),
        ("EntropyReproRequirementPayloadCertificate", "reproducibility_schema_at"),
        ("EntropyReproRequirementPayloadCertificate", "external_rows_at"),
    ]

    applied = 0
    for namespace, theorem in declarations:
        qualified = f"{namespace}.{theorem}"
        statement = theorem_statement(text, namespace, theorem)
        pattern = re.compile(
            re.escape(qualified) + r"\s*\n\s+C\.[^\n]+"
        )
        block, count = pattern.subn(statement, block, count=1)
        if count == 1:
            applied += 1
        elif qualified in block:
            raise RuntimeError(f"Mock1Advanced {qualified}: application shape changed")

    if applied:
        text = text[:start] + block + text[end:]
        changed = True
        print(
            "Mock1Advanced replace leaf-ledger theorem proof terms with their exact propositions: "
            f"applied {applied}"
        )
    else:
        print("Mock1Advanced leaf-ledger propositions: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """          simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
        have hexp :
""",
        """          simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
            Nat.cast_pow]
        have hexp :
""",
        1,
        "Mock2 normalize the integer power cast in the source representative",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring
""",
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ac_rfl
""",
        1,
        "Mock2 close the commutative power-factor rearrangement",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """@[simp] theorem freeResolutionComplex_X_add_two (M n : ℕ) :
    (freeResolutionComplex M).X (n + 2) = 0 :=
  rfl
""",
        """@[simp] theorem freeResolutionComplex_X_add_two (M n : ℕ) :
    (freeResolutionComplex M).X (n + 2) = zeroIntegerModule :=
  rfl
""",
        1,
        "Mock2 state the higher free-resolution object as the explicit zero module",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  rw [denseRange_inclusion_iff]
  intro x hx
  exact hx
""",
        """  rw [denseRange_inclusion_iff]
  exact M.core.le_topologicalClosure
""",
        2,
        "Mock2Advanced use the core-to-closure inclusion directly",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    rw [← Lp.compMeasurePreserving_id_apply F]
    simpa only [Function.comp_def, chart.coord.apply_symm_apply] using hcomp.symm
""",
        """    simpa only [Function.comp_def, chart.coord.apply_symm_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        1,
        "Mock2Advanced simplify the forward-backward Lp composition in one step",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    rw [← Lp.compMeasurePreserving_id_apply u]
    simpa only [Function.comp_def, chart.coord.symm_apply_apply] using hcomp.symm
""",
        """    simpa only [Function.comp_def, chart.coord.symm_apply_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        1,
        "Mock2Advanced simplify the backward-forward Lp composition in one step",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  rw [ModularGroup.im_smul_eq_div_normSq]
  norm_num [gammaTwoHyperbolic, UpperHalfPlane.I, UpperHalfPlane.denom,
    Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.mapGL,
    Matrix.SpecialLinearGroup.toGL, Complex.normSq]
"""
    new = """  rw [ModularGroup.im_smul_eq_div_normSq]
  have h11 :
      (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
          gammaTwoHyperbolic : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 3 := by
    rfl
  have h10 :
      (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
          gammaTwoHyperbolic : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 4 := by
    rfl
  rw [h11, h10]
  norm_num
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "FunctionalAnalysis expose the two concrete Gamma(2) matrix entries",
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
