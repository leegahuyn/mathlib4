import Mathlib.Geometry.Manifold.ContMDiff.Defs

noncomputable section

open Set Topology Manifold
open scoped Manifold

universe u v w

variable {H : Type u} {M : Type v} {M' : Type w}
variable [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
variable [ChartedSpace H M]

namespace Homeomorph

/-- Pull a charted-space atlas back along a global homeomorphism. -/
@[instance_reducible]
noncomputable def pullbackChartedSpace (F : M' ≃ₜ M) : ChartedSpace H M' where
  atlas := {e | ∃ a ∈ atlas H M, e = F.toOpenPartialHomeomorph.trans a}
  chartAt x := F.toOpenPartialHomeomorph.trans (chartAt H (F x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt H (F x), chart_mem_atlas H (F x), rfl⟩

/-- Pulling back the atlas along a homeomorphism preserves any existing structure groupoid. -/
theorem pullback_hasGroupoid (F : M' ≃ₜ M) (G : StructureGroupoid H)
    [HasGroupoid M G] :
    letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
    HasGroupoid M' G := by
  letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
  refine { compatible := ?_ }
  intro e e' he he'
  rcases he with ⟨a, ha, rfl⟩
  rcases he' with ⟨b, hb, rfl⟩
  let f := F.toOpenPartialHomeomorph
  refine G.mem_of_eqOnSource (G.compatible ha hb) ?_
  calc
    (f.trans a).symm.trans (f.trans b) =
        (a.symm.trans f.symm).trans (f.trans b) := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    _ = a.symm.trans ((f.symm.trans f).trans b) := by
      simp only [OpenPartialHomeomorph.trans_assoc]
    _ ≈ a.symm.trans
        ((OpenPartialHomeomorph.ofSet f.target f.open_target).trans b) :=
      OpenPartialHomeomorph.EqOnSource.trans'
        (Setoid.refl _)
        (OpenPartialHomeomorph.EqOnSource.trans'
          (OpenPartialHomeomorph.symm_trans_self f)
          (Setoid.refl _))
    _ = a.symm.trans b := by simp [f]

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- The defining homeomorphism is smooth for its pulled-back source atlas. -/
theorem pullback_contMDiff (F : M' ≃ₜ M) :
    letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
    ContMDiff I I n F := by
  letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
  intro x
  rw [contMDiffAt_iff]
  refine ⟨F.continuous.continuousAt, ?_⟩
  apply contDiffWithinAt_id.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    simp [pullbackChartedSpace, extChartAt, Function.comp_def, hz]
  · simp [pullbackChartedSpace, extChartAt]

end Smooth

end Homeomorph
