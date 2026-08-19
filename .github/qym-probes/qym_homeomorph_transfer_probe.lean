import Mathlib.Geometry.Manifold.IsManifold.Basic

noncomputable section

open Set Topology Manifold
open scoped Manifold

universe u v w

variable {H : Type u} {M : Type v} {M' : Type w}
variable [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
variable [ChartedSpace H M]

section

variable (F : M ≃ₜ M') (G : StructureGroupoid H)
variable [HasGroupoid M G]

example :
    letI : ChartedSpace H M' := F.chartedSpace
    HasGroupoid M' G := by
  letI : ChartedSpace H M' := F.chartedSpace
  infer_instance

end
