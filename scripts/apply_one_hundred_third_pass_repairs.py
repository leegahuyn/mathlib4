from __future__ import annotations

from pathlib import Path

import apply_one_hundred_second_pass_repairs as pass102
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    for index, value in enumerate([9, 1, 7, 14, 24]):
        old = f"""    have hv : AdvancedClaimsIIPaperI2ExtrapolatedValue ({index} : Fin 5) = {value} := by decide
    rw [hv] at h
"""
        new = f"""    change AdvancedClaimsIIPaperI2PrecisionTube
      (AdvancedClaimsIIPaperI2ExtrapolatedValue ({index} : Fin 5)) at h
    have hv : AdvancedClaimsIIPaperI2ExtrapolatedValue ({index} : Fin 5) = {value} := by decide
    rw [hv] at h
"""
        text, did = replace_exact(
            text, old, new, 1,
            f"Mock1Advanced standardize extrapolated Fin index {index}",
        )
        changed |= did

    for theorem in [
        "advanced_claims_ii_paper_i2_extrapolated_value_table",
        "advanced_claims_ii_paper_i2_extrapolated_residue_table",
    ]:
        start = text.index(f"theorem {theorem}")
        end = text.index("\n\ntheorem ", start)
        block = text[start:end]
        if "  native_decide\n" in block:
            block = block.replace("  native_decide\n", "  decide\n", 1)
            text = text[:start] + block + text[end:]
            changed = True
            print(f"Mock1Advanced replace native decision in {theorem}: applied")
        elif "  decide\n" in block:
            print(f"Mock1Advanced replace native decision in {theorem}: already applied")
        else:
            raise RuntimeError(f"{theorem}: decision proof absent")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    old = "[LinearOrderedAddCommGroup Energy]"
    new = "[AddCommGroup Energy] [LinearOrder Energy] [IsOrderedAddMonoid Energy]"
    count = text.count(old)
    if count:
        text = text.replace(old, new)
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock2 replace removed ordered-add-group class by current components: applied {count}")
    elif new in text:
        print("Mock2 replace removed ordered-add-group class by current components: already applied")
    else:
        raise RuntimeError("Mock2 ordered energy class occurrences absent")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  simpa [Function.comp_apply] using
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
""",
            """  convert
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
    using 1 <;> rfl
""",
            "Mock2Advanced identify reciprocal-Gamma composition definitionally",
        ),
        (
            """    simpa [Function.comp_apply] using
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
""",
            """    convert
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
      using 1 <;> rfl
""",
            "Mock2Advanced identify the negative-exponent composition definitionally",
        ),
        (
            """    simpa [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
""",
            """    convert
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hpowR
      using 1 <;> rfl
""",
            "Mock2Advanced identify the complex-cast composition definitionally",
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

    old = """    exact measure_mono_null (by
      intro z hz
      rw [Set.mem_diff, ← gammaTwoOpenCarrier_isOpen.interior_eq] at hz
      exact hz) gammaTwoOpenCarrier_frontier_null
"""
    new = """    exact measure_mono_null (by
      intro z hz
      rw [Set.mem_diff] at hz
      change z ∈ closure gammaTwoOpenCarrier ∧
        z ∉ interior gammaTwoOpenCarrier
      simpa [gammaTwoOpenCarrier_isOpen.interior_eq] using hz)
      gammaTwoOpenCarrier_frontier_null
"""
    text, changed = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis identify closure-minus-open with the frontier",
    )
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass102.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
