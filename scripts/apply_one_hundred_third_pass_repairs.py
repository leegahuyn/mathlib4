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

    replacements = [
        (
            """  fin_cases i <;> decide
""",
            """  fin_cases i <;> native_decide
""",
            1,
            "Mock1Advanced evaluate the five finite precision-tube obstructions natively",
        ),
        (
            """  fin_cases j <;> decide
""",
            """  fin_cases j <;> native_decide
""",
            1,
            "Mock1Advanced evaluate the six finite Mahler congruences natively",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

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
