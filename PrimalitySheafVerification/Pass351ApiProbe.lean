import Mathlib

open UpperHalfPlane MeasureTheory

#check @Submodule.mem_orthogonal
#check @Submodule.orthogonal_orthogonal_eq_closure
#check @RCLike.inner_apply
#check @Complex.inner_apply
#check @Matrix.SpecialLinearGroup.toGL
#check @Matrix.SpecialLinearGroup.mapGL

example (g : SL(2, ℝ)) (z : ℍ) :
    g • z = Matrix.SpecialLinearGroup.toGL g • z := by
  rfl

example (a b : ℂ) : inner ℂ a b = star a * b := by
  rfl

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (g : Submodule ℂ E) (x : E) :
    x ∈ g.orthogonal ↔ ∀ y ∈ g, inner ℂ y x = 0 := by
  exact Submodule.mem_orthogonal

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (g : Submodule ℂ E) :
    g.orthogonal.orthogonal = g.topologicalClosure := by
  exact g.orthogonal_orthogonal_eq_closure
