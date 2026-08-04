from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fourteenth_pass_repairs as pass114
import apply_one_hundred_fifteenth_pass_repairs as pass115
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  · simpa [modularTileEdgeEndpoints, modularTileEdgeParameterSet] using hx
  · simpa [modularTileEdgeEndpoints, modularTileEdgeParameterSet] using hx
""",
            """  · have hx0 : x = 0 := by
      simpa [modularTileEdgeEndpoints] using hx
    subst x
    exact le_rfl
  · have hx0 : x = 0 := by
      simpa [modularTileEdgeEndpoints] using hx
    subst x
    exact le_rfl
""",
            1,
            "FunctionalAnalysis turn both vertical endpoint equalities into nonnegativity",
        ),
        (
            """    mul_nonneg (sub_nonneg.mpr t.property.2)
      (add_nonneg.mpr t.property.1)
""",
            """    mul_nonneg (sub_nonneg.mpr t.property.2)
      (by linarith [t.property.1])
""",
            3,
            "FunctionalAnalysis derive all shifted-parameter nonnegativity facts",
        ),
        (
            """  · change ‖(modularCircularArcParam t : ℂ)‖ = 1
    have hsq : ‖(modularCircularArcParam t : ℂ)‖ ^ 2 = 1 := by
""",
            """  · change (modularCircularArcParam t : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖(modularCircularArcParam t : ℂ)‖ ^ 2 = 1 := by
""",
            1,
            "FunctionalAnalysis expose circular boundary membership before norm reduction",
        ),
    ]

    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass114.main()
    # Pass 114 already installs the explicit constructor-by-constructor
    # requirement-membership proof.  The later pass-115 rewrite replaced it
    # with a broad simp proof that leaves all 51 closed membership goals open
    # under Lean 4.33.  Preserve the stronger structural proof instead.
    pass115.repair_mock2()
    pass115.repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
