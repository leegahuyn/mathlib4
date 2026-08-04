from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twelfth_pass_repairs as pass112
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
            """  cases r <;> decide
""",
            """  classical
  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass]
""",
            1,
            "Mock1Advanced prove evidence classification by explicit finite reduction",
        ),
        (
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  native_decide
""",
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  intro h
  have hm : List.Mem objectClaimRegistry finiteExactRequirements := by
    simp [finiteExactRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            1,
            "Mock1Advanced witness a finite-exact requirement directly",
        ),
        (
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  native_decide
""",
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  intro h
  have hm : List.Mem principalPartRationalSolve analyticBoundaryRequirements := by
    simp [analyticBoundaryRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            1,
            "Mock1Advanced witness an analytic-boundary requirement directly",
        ),
        (
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  native_decide
""",
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  intro h
  have hm : List.Mem regressionCardySkeleton diagnosticMetadataRequirements := by
    simp [diagnosticMetadataRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            1,
            "Mock1Advanced witness a diagnostic requirement directly",
        ),
        (
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  native_decide
""",
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  intro h
  have hm : List.Mem namedConcretePaperInstance aggregateRequirements := by
    simp [aggregateRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            1,
            "Mock1Advanced witness an aggregate requirement directly",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """  simpa only [mul_assoc] using (Summable.const_smul c ha)
""",
            """  simpa only [smul_eq_mul, mul_assoc] using
    (Summable.const_smul c ha)
""",
            1,
            "Mock2 normalize complex scalar multiplication in summability",
        ),
        (
            """      res (U := U) (V := U) (le_refl U) = 𝟙 (obj U)
""",
            """      (@res U U (le_refl U)) = 𝟙 (obj U)
""",
            1,
            "Mock2 apply the dependent restriction field explicitly at identity",
        ),
        (
            """      res (U := V) (V := W) hVW ≫
          res (U := U) (V := V) hUV =
        res (U := U) (V := W) (le_trans hUV hVW)
""",
            """      (@res V W hVW) ≫ (@res U V hUV) =
        @res U W (le_trans hUV hVW)
""",
            1,
            "Mock2 apply all dependent restriction fields explicitly in composition",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  simp_rw [narrowSmoothTentFunction_even T hT]
""",
            """  rw [narrowSmoothTentFunction_even T hT]
""",
            1,
            "Mock2Advanced rewrite the reflected narrow bump once",
        ),
        (
            """  have hbContC : Continuous
      (fun x : ℝ => (narrowSmoothTentFunction T hT x : ℂ)) :=
    Complex.continuous_ofReal.comp
      (narrowSmoothTentFunction_smooth T hT).continuous
  rw [ofReal_smoothTentAutocorrelationRaw_eq T hT,
    Real.fourier_mul_convolution_eq hbIntC hbIntC hbContC hbContC ξ]
""",
            """  rw [ofReal_smoothTentAutocorrelationRaw_eq T hT,
    Real.fourier_mul_convolution_eq hbIntC hbIntC ξ]
""",
            1,
            "Mock2Advanced use the current Fourier convolution theorem signature",
        ),
        (
            """  simpa only [fourierPositiveSmoothTentFunction, Pi.mul_apply] using
    (HasCompactSupport.mul_left
      (f := fun _ : ℝ => smoothTentAutocorrelationScale T hT)
      (smoothTentAutocorrelationRaw_compactSupport T hT))
""",
            """  change HasCompactSupport
    ((smoothTentAutocorrelationScale T hT) •
      smoothTentAutocorrelationRaw T hT)
  exact (smoothTentAutocorrelationRaw_compactSupport T hT).smul_left
""",
            1,
            "Mock2Advanced express autocorrelation scaling through scalar action",
        ),
        (
            """  rw [show besselEnvelope 1 = 1 by simp [besselEnvelope]]
""",
            """  have hbessel : besselEnvelope 1 = 1 := by simp [besselEnvelope]
  rw [hbessel]
""",
            1,
            "Mock2Advanced avoid nested tactic brackets in the Bessel value rewrite",
        ),
    ])


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
            2,
            "FunctionalAnalysis derive both shifted-parameter nonnegativity facts",
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
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
