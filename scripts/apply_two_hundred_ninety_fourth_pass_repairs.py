from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """private theorem denseRange_energyCompletionMap_of_denseRange
    (f : E →ₗᵢ[ℂ] F) (hf : DenseRange f) :
    DenseRange (energyCompletionMap f) := by
  apply DenseRange.of_comp (g := ((↑) : E → UniformSpace.Completion E))
  have h := (UniformSpace.Completion.denseRange_coe :
      DenseRange ((↑) : F → UniformSpace.Completion F)).comp
    hf UniformSpace.Completion.continuous_coe
  simpa only [Function.comp_apply, energyCompletionMap_coe] using h
""",
        """private theorem denseRange_energyCompletionMap_of_denseRange
    (f : E →ₗᵢ[ℂ] F) (hf : DenseRange f) :
    DenseRange (energyCompletionMap f) := by
  apply DenseRange.of_comp (g := ((↑) : E → UniformSpace.Completion E))
  have hcoe : Continuous ((↑) : F → UniformSpace.Completion F) :=
    UniformSpace.Completion.continuous_coe
  have h :
      DenseRange (((↑) : F → UniformSpace.Completion F) ∘ (f : E → F)) :=
    (UniformSpace.Completion.denseRange_coe :
      DenseRange ((↑) : F → UniformSpace.Completion F)).comp hf hcoe
  simpa only [Function.comp_apply, energyCompletionMap_coe] using h
""",
        "FunctionalAnalysis completion map density",
    )
    fa = replace_exact(
        fa,
        """  rw [(UniformSpace.Completion.isUniformInducing_coe F).isInducing
    .closure_eq_preimage_closure_image (Set.range f)]
""",
        """  rw [(UniformSpace.Completion.isUniformInducing_coe F).isInducing.closure_eq_preimage_closure_image
    (Set.range f)]
""",
        "FunctionalAnalysis inducing closure transport",
    )
    fa = replace_exact(
        fa,
        """variable (I : CompatibleCoreInclusion Qc Qs)

@[simp]
theorem graph_compat (u : Vc) :
    Qs.graph (I.inclusion u) = Qc.graph u := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact I.base_compat u
  · apply WithLp.ofLp_injective 2
    exact Prod.ext (I.raise_compat u) (I.lower_compat u)

theorem graphRange_le : Qc.GraphRange ≤ Qs.GraphRange := by
  rintro _ ⟨u, rfl⟩
  exact ⟨I.inclusion u, I.graph_compat u⟩

noncomputable def graphRangeIsometry :
    Qc.GraphRange →ₗᵢ[ℂ] Qs.GraphRange where
  toLinearMap := Submodule.inclusion I.graphRange_le
  norm_map' _ := rfl

/-- Canonical isometric completion map associated to a supplied compatible
core inclusion. -/
noncomputable def completionInclusion :
    Qc.SobolevCompletion →ₗᵢ[ℂ] Qs.SobolevCompletion :=
  energyCompletionIsometry I.graphRangeIsometry

/-- The two completions coincide only after proving graph-density. -/
theorem denseRange_graphRange_iff_completion_surjective :
    DenseRange I.graphRangeIsometry ↔
      Function.Surjective I.completionInclusion := by
  simpa [completionInclusion] using
    denseRange_iff_surjective_energyCompletionIsometry I.graphRangeIsometry

/-- Once graph density is supplied, the page-4 and page-12 completions are
canonically linearly isometric. -/
noncomputable def completionEquiv
    (h : DenseRange I.graphRangeIsometry) :
    Qc.SobolevCompletion ≃ₗᵢ[ℂ] Qs.SobolevCompletion :=
  LinearIsometryEquiv.ofSurjective I.completionInclusion
    (I.denseRange_graphRange_iff_completion_surjective.mp h)

@[simp]
theorem completionEquiv_apply
    (h : DenseRange I.graphRangeIsometry) (x : Qc.SobolevCompletion) :
    I.completionEquiv h x = I.completionInclusion x := by
  rfl
""",
        """variable (incl : CompatibleCoreInclusion Qc Qs)

@[simp]
theorem graph_compat (u : Vc) :
    Qs.graph (incl.inclusion u) = Qc.graph u := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact incl.base_compat u
  · apply WithLp.ofLp_injective 2
    exact Prod.ext (incl.raise_compat u) (incl.lower_compat u)

theorem graphRange_le : Qc.GraphRange ≤ Qs.GraphRange := by
  rintro _ ⟨u, rfl⟩
  exact ⟨incl.inclusion u, graph_compat Qc Qs incl u⟩

noncomputable def graphRangeIsometry :
    Qc.GraphRange →ₗᵢ[ℂ] Qs.GraphRange where
  toLinearMap := Submodule.inclusion (graphRange_le Qc Qs incl)
  norm_map' _ := rfl

/-- Canonical isometric completion map associated to a supplied compatible
core inclusion. -/
noncomputable def completionInclusion :
    Qc.SobolevCompletion →ₗᵢ[ℂ] Qs.SobolevCompletion :=
  energyCompletionIsometry (graphRangeIsometry Qc Qs incl)

/-- The two completions coincide only after proving graph-density. -/
theorem denseRange_graphRange_iff_completion_surjective :
    DenseRange (graphRangeIsometry Qc Qs incl) ↔
      Function.Surjective (completionInclusion Qc Qs incl) := by
  simpa [completionInclusion] using
    denseRange_iff_surjective_energyCompletionIsometry
      (graphRangeIsometry Qc Qs incl)

/-- Once graph density is supplied, the page-4 and page-12 completions are
canonically linearly isometric. -/
noncomputable def completionEquiv
    (h : DenseRange (graphRangeIsometry Qc Qs incl)) :
    Qc.SobolevCompletion ≃ₗᵢ[ℂ] Qs.SobolevCompletion :=
  LinearIsometryEquiv.ofSurjective (completionInclusion Qc Qs incl)
    ((denseRange_graphRange_iff_completion_surjective Qc Qs incl).mp h)

@[simp]
theorem completionEquiv_apply
    (h : DenseRange (graphRangeIsometry Qc Qs incl))
    (x : Qc.SobolevCompletion) :
    completionEquiv Qc Qs incl h x = completionInclusion Qc Qs incl x := by
  rfl
""",
        "FunctionalAnalysis explicit compatible-core arguments",
    )
    fa = replace_exact(
        fa,
        """    [mu₀.IsOpenPosMeasure]
""",
        """    [MeasureTheory.Measure.IsOpenPosMeasure mu₀]
""",
        "FunctionalAnalysis fully qualified positive-open measure class",
    )
    fa = replace_exact(
        fa,
        """open WeightCorePetersson WeightCorePetersson.PeterssonCoreSpace
open FixedPhasePeterssonCoordinates

/-- The three concrete shifted Petersson coordinates on the canonical
""",
        """open WeightCorePetersson WeightCorePetersson.PeterssonCoreSpace
open FixedPhasePeterssonCoordinates

noncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) :=
  inferInstanceAs
    (AddCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance fixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) :=
  inferInstanceAs
    (Module ℂ (inverseEtaFixedPhaseStableCoreSubmodule n))

/-- The three concrete shifted Petersson coordinates on the canonical
""",
        "FunctionalAnalysis explicit fixed-phase core algebra",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
