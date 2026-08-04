from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path("PrimalitySheafVerification")
BASELINE = "ff31ad252cf938395b8bd39cede018baa3fe0b06"


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


def replace_region(
    text: str, start: str, end: str, replacement: str, label: str
) -> tuple[str, bool]:
    i = text.find(start)
    if i < 0:
        raise RuntimeError(f"{label}: start marker absent")
    j = text.find(end, i)
    if j < 0:
        raise RuntimeError(f"{label}: end marker absent")
    if text[i:j] == replacement:
        print(f"{label}: already applied")
        return text, False
    print(f"{label}: applied")
    return text[:i] + replacement + text[j:], True


def baseline_source(path: str) -> str:
    spec = f"{BASELINE}:{path}"
    try:
        return subprocess.check_output(["git", "show", spec], text=True)
    except subprocess.CalledProcessError:
        subprocess.run(
            ["git", "fetch", "--depth=1", "origin", BASELINE],
            check=True,
        )
        return subprocess.check_output(["git", "show", spec], text=True)


def theorem_statement(text: str, namespace: str, theorem: str) -> str:
    ns_start = text.find(f"namespace {namespace}")
    ns_end = text.find(f"end {namespace}", ns_start)
    pos = text.find(f"theorem {theorem}", ns_start, ns_end)
    if min(ns_start, ns_end, pos) < 0:
        raise RuntimeError(f"{namespace}.{theorem}: declaration not found")
    lines = text[pos:].splitlines()
    return_start = None
    for i, line in enumerate(lines[1:], 1):
        if line.rstrip().endswith(") :"):
            return_start = i + 1
            break
    if return_start is None:
        raise RuntimeError(f"{namespace}.{theorem}: return type start absent")
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


PROMPT_ITEMS = [
    ("PaperDataInstancePayloadCertificate", "paper_object_instance_at", "C.paperDataInstancePayload", ""),
    ("RemainingAdvancedClaimPayloadCertificate", "principal_part_rational_solve_at", "C.remainingAdvancedClaimPayload", ""),
    ("RemainingAdvancedClaimPayloadCertificate", "completion_shadow_holomorphic_at", "C.remainingAdvancedClaimPayload", ""),
    ("RemainingAdvancedClaimPayloadCertificate", "cusp_transport_at", "C.remainingAdvancedClaimPayload", ""),
    ("PaperDataInstancePayloadCertificate", "appell_lerch_at", "C.paperDataInstancePayload", ""),
    ("PaperDataInstancePayloadCertificate", "principal_exponent_at", "C.paperDataInstancePayload", ""),
    ("PaperDataInstancePayloadCertificate", "matrix_solution_at", "C.paperDataInstancePayload", ""),
    ("PaperDataInstancePayloadCertificate", "fixed_shadow_at", "C.paperDataInstancePayload", ""),
    ("PaperDataInstancePayloadCertificate", "inside_outside_at", "C.paperDataInstancePayload", "n"),
    ("SPTKernelRequirementPayloadCertificate", "nat_gcd_lcm_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "primewise_thickness_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "valuation_certificate_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "obstruction_failure_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "base_change_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "kernel_selection_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "multiplier_phase_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "cusp_convergence_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "transport_family_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "kernel_table_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "multiplier_input_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "cusp_input_at", "C.sptKernelRequirementPayload", ""),
    ("SPTKernelRequirementPayloadCertificate", "transport_across_cusps_at", "C.sptKernelRequirementPayload", ""),
    ("ExactCoefficientRequirementPayloadCertificate", "coefficient_separation_at", "C.exactCoefficientRequirementPayload", "n"),
    ("ExactCoefficientRequirementPayloadCertificate", "theta_character_at", "C.exactCoefficientRequirementPayload", ""),
    ("ExactCoefficientRequirementPayloadCertificate", "spectral_kloosterman_at", "C.exactCoefficientRequirementPayload", ""),
    ("ExactCoefficientRequirementPayloadCertificate", "local_euler_at", "C.exactCoefficientRequirementPayload", ""),
    ("ExactCoefficientRequirementPayloadCertificate", "root_filter_at", "C.exactCoefficientRequirementPayload", ""),
    ("ExactCoefficientRequirementPayloadCertificate", "exact_formula_at", "C.exactCoefficientRequirementPayload", "n"),
    ("ExactCoefficientRequirementPayloadCertificate", "paper_formula_fields_at", "C.exactCoefficientRequirementPayload", ""),
    ("PAdicRequirementPayloadCertificate", "normalization_at", "C.pAdicRequirementPayload", "n"),
    ("PAdicRequirementPayloadCertificate", "overlap_at", "C.pAdicRequirementPayload", "n"),
    ("PAdicRequirementPayloadCertificate", "mahler_at", "C.pAdicRequirementPayload", "n"),
    ("PAdicRequirementPayloadCertificate", "tail_zero_at", "C.pAdicRequirementPayload", "n hn"),
    ("PAdicRequirementPayloadCertificate", "face_tracking_at", "C.pAdicRequirementPayload", ""),
    ("PAdicRequirementPayloadCertificate", "denominator_data_at", "C.pAdicRequirementPayload", ""),
    ("PAdicRequirementPayloadCertificate", "chart_vectors_at", "C.pAdicRequirementPayload", "n"),
    ("PAdicRequirementPayloadCertificate", "mahler_table_at", "C.pAdicRequirementPayload", "n"),
    ("PAdicRequirementPayloadCertificate", "predicate_at", "C.pAdicRequirementPayload", "n hn"),
    ("PAdicRequirementPayloadCertificate", "obstruction_failure_at", "C.pAdicRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "regression_cardy_at", "C.entropyReproRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "rademacher_tail_at", "C.entropyReproRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "entropy_cardy_wrapper_at", "C.entropyReproRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "alpha_extraction_at", "C.entropyReproRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "degeneracy_at", "C.entropyReproRequirementPayload", "n"),
    ("EntropyReproRequirementPayloadCertificate", "ols_interval_at", "C.entropyReproRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "growth_stability_at", "C.entropyReproRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "reproducibility_schema_at", "C.entropyReproRequirementPayload", ""),
    ("EntropyReproRequirementPayloadCertificate", "external_rows_at", "C.entropyReproRequirementPayload", ""),
]


def corrected_prompt_region(baseline: str) -> str:
    start = baseline.index("def AdvancedClaimsIIObjectSchemaPromptObjective")
    end = baseline.index("inductive AdvancedClaimsIIPromptBullet", start)
    region = baseline[start:end]
    total = 0
    for namespace, theorem, payload, args in PROMPT_ITEMS:
        qualified = f"{namespace}.{theorem}"
        pattern = re.escape(qualified) + r"\s+" + re.escape(payload)
        for arg in args.split():
            pattern += r"\s+" + re.escape(arg)
        pattern += r"(?![A-Za-z0-9_])"
        proposition = theorem_statement(baseline, namespace, theorem)
        region, count = re.subn(pattern, f"(\n{proposition}\n)", region)
        if count != 2:
            raise RuntimeError(f"{qualified}: expected two prompt occurrences, found {count}")
        total += count
    print(f"Mock1Advanced regenerated {total} parenthesized prompt propositions")
    return region


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    baseline = baseline_source(str(path))
    changed = False

    ns = baseline.index("namespace Section")
    mem_start = baseline.index("theorem mem_all (s : Section)", ns)
    mem_end = baseline.index("end Section", mem_start)
    baseline_mem = baseline[mem_start:mem_end]
    current_ns = text.index("namespace Section")
    current_mem = text.index("theorem mem_all (s : Section)", current_ns)
    current_end = text.index("end Section", current_mem)
    if text[current_mem:current_end] != baseline_mem:
        text = text[:current_mem] + baseline_mem + text[current_end:]
        changed = True
        print("Mock1Advanced restored all Section membership branches")

    text, did = replace_region(
        text,
        "def AdvancedClaimsIIObjectSchemaPromptObjective",
        "inductive AdvancedClaimsIIPromptBullet",
        corrected_prompt_region(baseline),
        "Mock1Advanced restore prompt objectives/accessors with explicit proposition grouping",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  have hz' :
      ((((quotientStep M N : ℕ) : ℤ) * (a - b) : ℤ) : ZMod N) = 0 := by
    simpa only [map_zero] using hz
""",
        """  have hz' :
      ((((quotientStep M N : ℕ) : ℤ) * (a - b) : ℤ) : ZMod N) = 0 := by
    simpa only [Int.cast_mul, Int.cast_natCast] using hz
""",
        1,
        "Mock2 normalize quotient-step integer product cast",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring
""",
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring_nf
""",
        1,
        "Mock2 normalize prime-power commutative product",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa only [map_zero] using hz
""",
        """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    rw [map_zero]
    exact hz
""",
        1,
        "Mock2 orient multiplication-by-M zero image",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  | zero => exact zero_comp _
  | succ n => exact zero_comp _
""",
        """  | zero => exact zero_comp
  | succ n => exact zero_comp
""",
        1,
        "Mock2 use zero_comp without explicit arguments",
    )
    changed |= did

    if changed:
        path.write_text(text.rstrip() + "\n", encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """    have hfun : (chart.coord ∘ chart.coord.symm) = id := by
      funext x
      exact chart.coord.apply_symm_apply x
    rw [hfun] at hcomp
    simpa only [Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        """    calc
      _ = Lp.compMeasurePreserving (chart.coord ∘ chart.coord.symm)
            (hcoord.comp hsymm) F := hcomp.symm
      _ = F := by
        convert Lp.compMeasurePreserving_id_apply F using 1
        funext x
        exact chart.coord.apply_symm_apply x
""",
        1,
        "Mock2Advanced prove forward-backward Lp composition by conversion",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    have hfun : (chart.coord.symm ∘ chart.coord) = id := by
      funext x
      exact chart.coord.symm_apply_apply x
    rw [hfun] at hcomp
    simpa only [Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        """    calc
      _ = Lp.compMeasurePreserving (chart.coord.symm ∘ chart.coord)
            (hsymm.comp hcoord) u := hcomp.symm
      _ = u := by
        convert Lp.compMeasurePreserving_id_apply u using 1
        funext x
        exact chart.coord.symm_apply_apply x
""",
        1,
        "Mock2Advanced prove backward-forward Lp composition by conversion",
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
        """    exact (Complex.continuousAt_sqrt (Or.inr him)).comp z hdenom
""",
        """    exact (Complex.continuousAt_sqrt (Or.inr him)).comp hdenom
""",
        1,
        "FunctionalAnalysis use the current ContinuousAt.comp signature",
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
