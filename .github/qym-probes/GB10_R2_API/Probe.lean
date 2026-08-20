import Mathlib

open Set Topology Manifold
open scoped ComplexConjugate ENNReal InnerProduct

#check OpenPartialHomeomorph.extend_target
#check Complex.ofReal_pow
#check Complex.ofReal_mul
#check Complex.ofReal_add
#check Complex.ofReal_re

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

example (u : E) : ((↑‖u‖ : ℂ) ^ 2).re = 0 ↔ u = 0 := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [sq_eq_zero_iff, norm_eq_zero]

example (a b : ℝ) :
    RCLike.re ((a : ℂ) ^ 2 + (((1 : ℝ) / 4 : ℝ) : ℂ) * (b : ℂ) ^ 2) =
      a ^ 2 + (1 / 4 : ℝ) * b ^ 2 := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
