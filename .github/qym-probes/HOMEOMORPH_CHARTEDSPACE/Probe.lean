import Mathlib

open Set Topology Manifold

universe u v w u₁ u₂

variable {H : Type u} {M : Type v} {M' : Type w}
variable [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
variable [ChartedSpace H M]
variable (G : StructureGroupoid H) [HasGroupoid M G]
variable (f : M ≃ₜ M')

example :
    letI : ChartedSpace H M' := f.chartedSpace
    HasGroupoid M' G := by
  letI : ChartedSpace H M' := f.chartedSpace
  infer_instance

variable {𝕜 : Type u₁} {E : Type u₂}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E H)
variable [IsManifold I ∞ M]

example :
    letI : ChartedSpace H M' := f.chartedSpace
    IsManifold I ∞ M' := by
  letI : ChartedSpace H M' := f.chartedSpace
  infer_instance
