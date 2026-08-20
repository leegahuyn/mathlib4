import Mathlib

open Set Topology Manifold
open scoped ComplexConjugate ENNReal InnerProduct

#check ContMDiff.congr
#check extChartAt_comp
#check mem_extChartAt_target

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

example (u : E) : ((↑‖u‖ : ℂ) ^ 2).re = 0 ↔ u = 0 := by
  simp [sq_eq_zero_iff]

example (a b : ℝ) :
    RCLike.re ((a : ℂ) ^ 2 + (((1 : ℝ) / 4 : ℝ) : ℂ) * (b : ℂ) ^ 2) =
      a ^ 2 + (1 / 4 : ℝ) * b ^ 2 := by
  norm_num
