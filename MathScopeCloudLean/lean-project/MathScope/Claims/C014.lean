import Mathlib

namespace MathScope.Claims.C014

/--
C-014: the exact coordinate slice x₄ = c of the unit 3-sphere satisfies
x₁² + x₂² + x₃² = 1 - c².

This algebraic identity is intentionally separate from the topological claim
that the nondegenerate slice is homeomorphic to S².
-/
theorem c014_slice_radius
    (x1 x2 x3 x4 c : ℝ)
    (hSphere : x1^2 + x2^2 + x3^2 + x4^2 = 1)
    (hSlice : x4 = c) :
    x1^2 + x2^2 + x3^2 = 1 - c^2 := by
  subst x4
  nlinarith [hSphere]

end MathScope.Claims.C014
