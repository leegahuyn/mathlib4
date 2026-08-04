from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fourteenth_pass_repairs as pass114
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """  classical
  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass]
""",
            """  classical
  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass,
      List.mem_cons, List.mem_singleton]
""",
            1,
            "Mock1Advanced reduce explicit requirement-list membership propositions",
        ),
        (
            """    simp [finiteExactRequirements, all, evidenceClass]
""",
            """    simp [finiteExactRequirements, all, evidenceClass,
      List.mem_cons, List.mem_singleton]
""",
            1,
            "Mock1Advanced prove the finite witness membership structurally",
        ),
        (
            """    simp [analyticBoundaryRequirements, all, evidenceClass]
""",
            """    simp [analyticBoundaryRequirements, all, evidenceClass,
      List.mem_cons, List.mem_singleton]
""",
            1,
            "Mock1Advanced prove the analytic witness membership structurally",
        ),
        (
            """    simp [diagnosticMetadataRequirements, all, evidenceClass]
""",
            """    simp [diagnosticMetadataRequirements, all, evidenceClass,
      List.mem_cons, List.mem_singleton]
""",
            1,
            "Mock1Advanced prove the diagnostic witness membership structurally",
        ),
        (
            """    simp [aggregateRequirements, all, evidenceClass]
""",
            """    simp [aggregateRequirements, all, evidenceClass,
      List.mem_cons, List.mem_singleton]
""",
            1,
            "Mock1Advanced prove the aggregate witness membership structurally",
        ),
    ])


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  res_id :
    ∀ U : TopologicalSpace.Opens X,
      (@res U U (le_refl U)) = 𝟙 (obj U)
  res_comp :
    ∀ {U V W : TopologicalSpace.Opens X}
      (hUV : U ≤ V) (hVW : V ≤ W),
      (@res V W hVW) ≫ (@res U V hUV) =
        @res U W (le_trans hUV hVW)
""",
            """  res_id :
    ∀ (U : TopologicalSpace.Opens X) (s : obj U),
      res (le_refl U) s = s
  res_comp :
    ∀ {U V W : TopologicalSpace.Opens X}
      (hUV : U ≤ V) (hVW : V ≤ W) (s : obj W),
      res hUV (res hVW s) = res (le_trans hUV hVW) s
""",
            1,
            "Mock2 state linear-presheaf laws pointwise to avoid morphism coercion",
        ),
        (
            """  res_id := by
    intro U s
    have h := congrArg (fun f : F.obj U ⟶ F.obj U => f s) (F.res_id U)
    simpa using h
  res_comp := by
    intro U V W hUV hVW s
    have h := congrArg (fun f : F.obj W ⟶ F.obj U => f s)
      (F.res_comp hUV hVW)
    simpa using h
""",
            """  res_id := by
    intro U s
    exact F.res_id U s
  res_comp := by
    intro U V W hUV hVW s
    exact F.res_comp hUV hVW s
""",
            1,
            "Mock2 transfer pointwise linear-presheaf laws to PresheafLike",
        ),
        (
            """  res_id := locallyConstantRestriction_id E
  res_comp := locallyConstantRestriction_comp E
""",
            """  res_id U s := by rfl
  res_comp hUV hVW s := by rfl
""",
            1,
            "Mock2 prove locally-constant restriction laws pointwise",
        ),
        (
            """  res_id U := by
    apply ModuleCat.hom_ext
    simpa using tensorRestriction_id L M U
  res_comp hUV hVW := by
    apply ModuleCat.hom_ext
    simpa using tensorRestriction_comp L M hUV hVW
""",
            """  res_id U s := by
    exact DFunLike.congr_fun (tensorRestriction_id L M U) s
  res_comp hUV hVW s := by
    exact DFunLike.congr_fun (tensorRestriction_comp L M hUV hVW) s
""",
            1,
            "Mock2 prove tensor restriction laws pointwise",
        ),
        (
            """  res_id U := by
    apply ModuleCat.hom_ext
    simpa using pairRestriction_id L M U
  res_comp hUV hVW := by
    apply ModuleCat.hom_ext
    simpa using pairRestriction_comp L M hUV hVW
""",
            """  res_id U s := by
    exact DFunLike.congr_fun (pairRestriction_id L M U) s
  res_comp hUV hVW s := by
    exact DFunLike.congr_fun (pairRestriction_comp L M hUV hVW) s
""",
            1,
            "Mock2 prove pair restriction laws pointwise",
        ),
    ]

    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  rw [narrowSmoothTentFunction_even T hT]
""",
            """  have heven :
      (fun t : ℝ => narrowSmoothTentFunction T hT t *
        narrowSmoothTentFunction T hT (-t)) =
      (fun t : ℝ => narrowSmoothTentFunction T hT t *
        narrowSmoothTentFunction T hT t) := by
    funext t
    rw [narrowSmoothTentFunction_even T hT t]
  rw [heven]
""",
            1,
            "Mock2Advanced rewrite the reflected bump under the integral extensionally",
        ),
        (
            """  simp only [Complex.ofReal_one, mul_one]
  rw [integral_complex_ofReal,
""",
            """  simp only [Complex.ofReal_one, one_mul, mul_one]
  rw [integral_complex_ofReal,
""",
            1,
            "Mock2Advanced remove the left unit before the real-integral rewrite",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
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
            1,
            "FunctionalAnalysis derive circular-parameter shifted nonnegativity",
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
    ])


def main() -> int:
    pass114.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
