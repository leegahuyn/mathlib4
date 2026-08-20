from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(text: str, old: str, new: str, expected: int, label: str) -> tuple[str, bool]:
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


DECLARATIONS = [
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


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.find("def AdvancedClaimsIIObjectSchemaPromptObjective")
    end = text.find("inductive AdvancedClaimsIIPromptBullet", start)
    if start < 0 or end < 0:
        raise RuntimeError("Mock1Advanced prompt-objective region not found")
    block = text[start:end]
    replaced = 0
    for namespace, theorem in DECLARATIONS:
        qualified = f"{namespace}.{theorem}"
        statement = theorem_statement(text, namespace, theorem)
        pattern = re.compile(
            re.escape(qualified)
            + r"\s+C\.[A-Za-z0-9_.]+(?:\s+n)?(?:\s+hn)?"
        )
        block, count = pattern.subn(statement, block)
        replaced += count
    if replaced:
        text = text[:start] + block + text[end:]
        changed = True
        print(f"Mock1Advanced restore exact propositions in prompt objectives/accessors: applied {replaced}")
    else:
        print("Mock1Advanced prompt objective propositions already restored")

    text, did = replace_exact(
        text,
        """theorem mem_all
    (b : AdvancedClaimsIIPromptBullet) :
    List.Mem b all := by
  cases b <;> simp [all]
""",
        """theorem mem_all
    (b : AdvancedClaimsIIPromptBullet) :
    List.Mem b all := by
  decide
""",
        1,
        "Mock1Advanced decide closed prompt-bullet membership",
    )
    changed |= did

    final_case = """  | finalInstance =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
"""
    if final_case in text:
        text = text.replace(final_case, "", 1)
        changed = True
        print("Mock1Advanced remove impossible Section.finalInstance branch")

    text, did = replace_exact(
        text,
        """private theorem mem_all_aux (r : AdvancedClaimsIIRequirement) :
    List.Mem r all := by
""",
        """private theorem mem_all_aux (r : AdvancedClaimsIIRequirement) :
    List.Mem r AdvancedClaimsIIRequirement.all := by
""",
        1,
        "Mock1Advanced qualify requirement registry in mem_all_aux",
    )
    changed |= did

    section_start = text.find("theorem sectionOf_objectSchema_at")
    section_end = text.find("theorem objectSchema_mem_all", section_start)
    if section_start >= 0 and section_end >= 0:
        section_block = text[section_start:section_end]
        count = section_block.count("    sectionOf r = Section.")
        if count:
            section_block = section_block.replace(
                "    sectionOf r = Section.",
                "    AdvancedClaimsIIRequirement.sectionOf r = Section.",
            )
            text = text[:section_start] + section_block + text[section_end:]
            changed = True
            print(f"Mock1Advanced qualify requirement section classifier: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring_nf
""",
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring
""",
        1,
        "Mock2 close the commutative power-factor identity",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    simpa using hz
""",
        """    simpa only [map_zero] using hz
""",
        1,
        "Mock2 normalize the zero image in resolution exactness",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  | zero => exact zero_comp _ _
  | succ n => exact zero_comp _ _
""",
        """  | zero => exact zero_comp _
  | succ n => exact zero_comp _
""",
        1,
        "Mock2 use the current zero_comp signature",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  change freeResolutionD M (n + 2) = 0
  rfl
""",
        """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl
""",
        1,
        "Mock2 prove higher zero differential extensionally",
    )
    changed |= did

    normalized = text.rstrip() + "\n"
    if normalized != text:
        text = normalized
        changed = True
        print("Mock2 normalize final newline")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  rw [denseRange_inclusion_iff]
  · exact M.core.le_topologicalClosure
  · intro x hx
    exact hx
""",
        """  rw [denseRange_inclusion_iff]
  · intro x hx
    exact hx
  · intro x hx
    exact M.core.le_topologicalClosure hx
""",
        2,
        "Mock2Advanced discharge closure goals in the correct order",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    conv_rhs => rw [← Lp.compMeasurePreserving_id_apply F]
    exact hcomp.symm
""",
        """    have hfun : (chart.coord ∘ chart.coord.symm) = id := by
      funext x
      exact chart.coord.apply_symm_apply x
    rw [hfun] at hcomp
    simpa only [Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        1,
        "Mock2Advanced identify the forward-backward chart composition",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    conv_rhs => rw [← Lp.compMeasurePreserving_id_apply u]
    exact hcomp.symm
""",
        """    have hfun : (chart.coord.symm ∘ chart.coord) = id := by
      funext x
      exact chart.coord.symm_apply_apply x
    rw [hfun] at hcomp
    simpa only [Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        1,
        "Mock2Advanced identify the backward-forward chart composition",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  · simpa [etaSqrtFactor, UpperHalfPlane.denom, g, hc] using
      (continuous_const : Continuous
        (fun _ : ℍ ↦ Complex.sqrt (g 1 1)))
"""
    new = """  · have hfun : etaSqrtFactor γ =
        (fun _ : ℍ ↦ Complex.sqrt (g 1 1)) := by
      funext z
      simp [etaSqrtFactor, UpperHalfPlane.denom, g, hc]
    rw [hfun]
    exact continuous_const
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "FunctionalAnalysis identify the constant eta square-root factor",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    exact (Complex.continuousAt_sqrt (Or.inr him)).comp' hdenom
""",
        """    exact (Complex.continuousAt_sqrt (Or.inr him)).comp z hdenom
""",
        1,
        "FunctionalAnalysis compose square-root continuity at the upper-half-plane point",
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
