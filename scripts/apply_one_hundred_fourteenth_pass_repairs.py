from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twelfth_pass_repairs as pass112
import apply_one_hundred_thirteenth_pass_repairs as pass113
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  cases e <;>
    simp [modularTileEdgeEndpoints, modularTileEdgeParameterSet]
""",
            """  cases e <;> intro x hx
  · simp [modularTileEdgeEndpoints, modularTileEdgeParameterSet] at hx ⊢
    rcases hx with rfl | rfl <;> constructor <;> norm_num
  · simpa [modularTileEdgeEndpoints, modularTileEdgeParameterSet] using hx
  · simpa [modularTileEdgeEndpoints, modularTileEdgeParameterSet] using hx
""",
            1,
            "FunctionalAnalysis verify every modular-edge endpoint explicitly",
        ),
        (
            """  cases e <;>
    simpa [GammaTwoModularTileEdge.pairedParameter,
      GammaTwoModularTileEdge.paired, modularTileEdgeEndpoints] using ht
""",
            """  cases e with
  | circularArc =>
      simp only [GammaTwoModularTileEdge.pairedParameter,
        GammaTwoModularTileEdge.paired, modularTileEdgeEndpoints,
        Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      rcases ht with ht | ht
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  | leftVerticalSegment =>
      simpa [GammaTwoModularTileEdge.pairedParameter,
        GammaTwoModularTileEdge.paired, modularTileEdgeEndpoints] using ht
  | rightVerticalSegment =>
      simpa [GammaTwoModularTileEdge.pairedParameter,
        GammaTwoModularTileEdge.paired, modularTileEdgeEndpoints] using ht
""",
            1,
            "FunctionalAnalysis transport circular and vertical endpoints separately",
        ),
        (
            """def modularCircularArcParam (t : Set.Icc (-1 : ℝ) 1) : ℍ :=
""",
            """noncomputable def modularCircularArcParam (t : Set.Icc (-1 : ℝ) 1) : ℍ :=
""",
            1,
            "FunctionalAnalysis mark the circular parametrization noncomputable",
        ),
        (
            """def modularLeftVerticalParam (t : Set.Ici (0 : ℝ)) : ℍ :=
""",
            """noncomputable def modularLeftVerticalParam (t : Set.Ici (0 : ℝ)) : ℍ :=
""",
            1,
            "FunctionalAnalysis mark the left vertical parametrization noncomputable",
        ),
        (
            """def modularRightVerticalParam (t : Set.Ici (0 : ℝ)) : ℍ :=
""",
            """noncomputable def modularRightVerticalParam (t : Set.Ici (0 : ℝ)) : ℍ :=
""",
            1,
            "FunctionalAnalysis mark the right vertical parametrization noncomputable",
        ),
        (
            """def modularTileEdgeParam :
""",
            """noncomputable def modularTileEdgeParam :
""",
            1,
            "FunctionalAnalysis mark the edge parametrization dispatcher noncomputable",
        ),
        (
            """      mul_nonneg (sub_nonneg.mpr t.property.2)
        (add_nonneg.mpr t.property.1)
""",
            """      mul_nonneg (sub_nonneg.mpr t.property.2)
        (by linarith [t.property.1])
""",
            1,
            "FunctionalAnalysis derive the shifted-parameter nonnegativity fact",
        ),
        (
            """    rw [hsqrt]
    ring
""",
            """    nlinarith [hsqrt]
""",
            1,
            "FunctionalAnalysis normalize the circular norm-square identity",
        ),
        (
            """      refine ⟨hnormSq.le, ?_⟩
""",
            """      refine ⟨hnormSq.ge, ?_⟩
""",
            1,
            "FunctionalAnalysis use the correct orientation of the norm-square equality",
        ),
        (
            """  · rw [mem_sphere_zero_iff_norm]
    have hsq : ‖(modularCircularArcParam t : ℂ)‖ ^ 2 = 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hnormSq
    nlinarith [norm_nonneg (modularCircularArcParam t : ℂ)]
""",
            """  · change ‖(modularCircularArcParam t : ℂ)‖ = 1
    have hsq : ‖(modularCircularArcParam t : ℂ)‖ ^ 2 = 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hnormSq
    nlinarith [norm_nonneg (modularCircularArcParam t : ℂ)]
""",
            1,
            "FunctionalAnalysis expose circular sphere membership as a norm equality",
        ),
    ]

    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass112.main()
    pass113.repair_mock1_advanced()
    pass113.repair_mock2()
    pass113.repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
