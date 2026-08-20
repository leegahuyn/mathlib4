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
        """/-- Store the canonical completion inner product once, then use its parent
module and normed-space structures for every later bundled map. -/
noncomputable def sobolevCompletionInnerProductSpace :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.innerProductSpace

noncomputable local instance sobolevCompletionModule : Module ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace.toModule

noncomputable local instance sobolevCompletionNormedSpace :
    NormedSpace ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace.toNormedSpace

noncomputable local instance sobolevCompletionInner : Inner ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace.toInner

noncomputable local instance sobolevCompletionInnerProductSpaceInstance :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace

""",
        "",
        "FunctionalAnalysis restore canonical completion structures",
    )
    fa = replace_exact(
        fa,
        """theorem denseRange_coreEmbedding : DenseRange Q.coreEmbedding := by
  simpa [coreEmbedding] using
    (UniformSpace.Completion.denseRange_coe :
      DenseRange ((↑) : Q.GraphRange → Q.SobolevCompletion))
""",
        """theorem denseRange_coreEmbedding : DenseRange Q.coreEmbedding := by
  change DenseRange ((↑) : Q.GraphRange → Q.SobolevCompletion)
  exact UniformSpace.Completion.denseRange_coe
""",
        "FunctionalAnalysis identify the completion core embedding",
    )
    fa = replace_exact(
        fa,
        """theorem norm_sectionCoreMap_sq (u : V) :
    ‖Q.sectionCoreMap u‖ ^ 2 =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  simpa [sectionCoreMap, coreEmbedding] using Q.norm_toGraphRange_sq u
""",
        """theorem norm_sectionCoreMap_sq (u : V) :
    ‖Q.sectionCoreMap u‖ ^ 2 =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  change ‖(Q.toGraphRange u : Q.SobolevCompletion)‖ ^ 2 =
    ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2
  rw [UniformSpace.Completion.norm_coe]
  exact Q.norm_toGraphRange_sq u
""",
        "FunctionalAnalysis evaluate the completed graph norm on the core",
    )
    fa = replace_exact(
        fa,
        """theorem completionEnergyOperator_sectionCoreMap (u v : V) :
    Q.completionEnergyOperator (Q.sectionCoreMap u) (Q.sectionCoreMap v) =
      Q.energyForm v u := by
  rw [Q.completionEnergyOperator_apply]
  change ⟪(Q.toGraphRange v : Q.SobolevCompletion),
      (Q.toGraphRange u : Q.SobolevCompletion)⟫_ℂ = Q.energyForm v u
  rw [UniformSpace.Completion.inner_coe, Q.inner_toGraphRange]
""",
        """theorem completionEnergyOperator_sectionCoreMap (u v : V) :
    Q.completionEnergyOperator (Q.sectionCoreMap u) (Q.sectionCoreMap v) =
      Q.energyForm v u := by
  rw [Q.completionEnergyOperator_apply]
  change ⟪(Q.toGraphRange v : Q.SobolevCompletion),
      (Q.toGraphRange u : Q.SobolevCompletion)⟫_ℂ = Q.energyForm v u
  exact (UniformSpace.Completion.inner_coe _ _).trans
    (Q.inner_toGraphRange v u)
""",
        "FunctionalAnalysis evaluate the completed core inner product",
    )
    fa = replace_exact(
        fa,
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
        """@[simp]
theorem graph_compat
    (incl : CompatibleCoreInclusion Qc Qs) (u : Vc) :
    Qs.graph (CompatibleCoreInclusion.inclusion incl u) = Qc.graph u := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact CompatibleCoreInclusion.base_compat incl u
  · apply WithLp.ofLp_injective 2
    exact Prod.ext
      (CompatibleCoreInclusion.raise_compat incl u)
      (CompatibleCoreInclusion.lower_compat incl u)

theorem graphRange_le
    (incl : CompatibleCoreInclusion Qc Qs) :
    Qc.GraphRange ≤ Qs.GraphRange := by
  rintro _ ⟨u, rfl⟩
  exact ⟨CompatibleCoreInclusion.inclusion incl u,
    graph_compat Qc Qs incl u⟩

noncomputable def graphRangeIsometry
    (incl : CompatibleCoreInclusion Qc Qs) :
    Qc.GraphRange →ₗᵢ[ℂ] Qs.GraphRange where
  toLinearMap := Submodule.inclusion (graphRange_le Qc Qs incl)
  norm_map' _ := rfl

/-- Canonical isometric completion map associated to a supplied compatible
core inclusion. -/
noncomputable def completionInclusion
    (incl : CompatibleCoreInclusion Qc Qs) :
    Qc.SobolevCompletion →ₗᵢ[ℂ] Qs.SobolevCompletion :=
  energyCompletionIsometry (graphRangeIsometry Qc Qs incl)

/-- The two completions coincide only after proving graph-density. -/
theorem denseRange_graphRange_iff_completion_surjective
    (incl : CompatibleCoreInclusion Qc Qs) :
    DenseRange (graphRangeIsometry Qc Qs incl) ↔
      Function.Surjective (completionInclusion Qc Qs incl) := by
  simpa [completionInclusion] using
    denseRange_iff_surjective_energyCompletionIsometry
      (graphRangeIsometry Qc Qs incl)

/-- Once graph density is supplied, the page-4 and page-12 completions are
canonically linearly isometric. -/
noncomputable def completionEquiv
    (incl : CompatibleCoreInclusion Qc Qs)
    (h : DenseRange (graphRangeIsometry Qc Qs incl)) :
    Qc.SobolevCompletion ≃ₗᵢ[ℂ] Qs.SobolevCompletion :=
  LinearIsometryEquiv.ofSurjective (completionInclusion Qc Qs incl)
    ((denseRange_graphRange_iff_completion_surjective Qc Qs incl).mp h)

@[simp]
theorem completionEquiv_apply
    (incl : CompatibleCoreInclusion Qc Qs)
    (h : DenseRange (graphRangeIsometry Qc Qs incl))
    (x : Qc.SobolevCompletion) :
    completionEquiv Qc Qs incl h x = completionInclusion Qc Qs incl x := by
  rfl
""",
        "FunctionalAnalysis make the compatible-core adapter explicit",
    )
    fa = replace_exact(
        fa,
        "[IsFiniteMeasureOnCompacts mu₀]",
        "[MeasureTheory.IsFiniteMeasureOnCompacts mu₀]",
        "FunctionalAnalysis qualify compact-finite measures",
    )
    fa = replace_exact(
        fa,
        "[IsFiniteMeasureOnCompacts muR]",
        "[MeasureTheory.IsFiniteMeasureOnCompacts muR]",
        "FunctionalAnalysis qualify compact-finite raised measure",
    )
    fa = replace_exact(
        fa,
        "[IsFiniteMeasureOnCompacts muL]",
        "[MeasureTheory.IsFiniteMeasureOnCompacts muL]",
        "FunctionalAnalysis qualify compact-finite lowered measure",
    )
    fa = replace_exact(
        fa,
        """noncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) :=
  inferInstanceAs
    (AddCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance fixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) :=
  inferInstanceAs
    (Module ℂ (inverseEtaFixedPhaseStableCoreSubmodule n))

""",
        "",
        "FunctionalAnalysis restore canonical fixed-phase core algebra",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
