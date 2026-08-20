import Mathlib.Geometry.Manifold.ContMDiff.Defs

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff

universe u v w

variable {H : Type u} {M : Type v} {M' : Type w}
variable [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
variable [ChartedSpace H M]

namespace Homeomorph

@[instance_reducible]
noncomputable def pullbackChartedSpace (F : M' ≃ₜ M) : ChartedSpace H M' where
  atlas := {e | ∃ a ∈ atlas H M, e = F.toOpenPartialHomeomorph.trans a}
  chartAt x := F.toOpenPartialHomeomorph.trans (chartAt H (F x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt H (F x), chart_mem_atlas H (F x), rfl⟩

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

@[simp] theorem pullback_extChartAt_apply (F : M' ≃ₜ M) (x y : M') :
    letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
    extChartAt I x y = extChartAt I (F x) (F y) := by
  rfl

theorem pullback_contMDiff (F : M' ≃ₜ M) :
    letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
    ContMDiff I I n F := by
  letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
  intro x
  rw [contMDiffAt_iff]
  refine ⟨F.continuous.continuousAt, ?_⟩
  apply contDiffWithinAt_id.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    have hr := PartialEquiv.right_inv (extChartAt I x) hz
    rw [pullback_extChartAt_apply (F := F) (I := I)] at hr
    exact hr
  · have hx : (extChartAt I x).symm (extChartAt I x x) = x :=
      PartialEquiv.left_inv (extChartAt I x) (by simp)
    simp only [Function.comp_apply, hx, id_eq]
    exact (pullback_extChartAt_apply (F := F) (I := I) x x).symm

theorem pullback_symm_contMDiff (F : M' ≃ₜ M) :
    letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
    ContMDiff I I n F.symm := by
  letI : ChartedSpace H M' := F.pullbackChartedSpace (H := H)
  intro x
  rw [contMDiffAt_iff]
  refine ⟨F.symm.continuous.continuousAt, ?_⟩
  apply contDiffWithinAt_id.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    have hr := PartialEquiv.right_inv (extChartAt I x) hz
    simpa only [Function.comp_apply, pullback_extChartAt_apply,
      F.apply_symm_apply, id_eq] using hr
  · have hx : (extChartAt I x).symm (extChartAt I x x) = x :=
      PartialEquiv.left_inv (extChartAt I x) (by simp)
    simp only [Function.comp_apply, hx, id_eq,
      pullback_extChartAt_apply, F.apply_symm_apply]

end Smooth

end Homeomorph
