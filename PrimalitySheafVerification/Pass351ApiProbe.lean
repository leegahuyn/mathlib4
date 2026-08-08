import Mathlib

open UpperHalfPlane MeasureTheory

#check @Submodule.mem_orthogonal
#check @Submodule.orthogonal_orthogonal_eq_closure
#check @RCLike.inner_apply
#check @Matrix.SpecialLinearGroup.toGL
#check @Matrix.SpecialLinearGroup.mapGL

example (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    g • z = Matrix.SpecialLinearGroup.toGL g • z := by
  rfl

example (a b : ℂ) : inner ℂ a b = b * star a := by
  exact RCLike.inner_apply a b

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (g : Submodule ℂ E) (x : E) :
    x ∈ g.orthogonal ↔ ∀ y ∈ g, inner ℂ y x = 0 := by
  exact @Submodule.mem_orthogonal ℂ E _ _ _ g x

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (g : Submodule ℂ E) :
    g.orthogonal.orthogonal = g.topologicalClosure := by
  exact @Submodule.orthogonal_orthogonal_eq_closure ℂ E _ _ _ g _

noncomputable def exactHyperbolicDensityProbe (z : ℍ) : NNReal :=
  (1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2

example : Continuous exactHyperbolicDensityProbe := by
  simpa only [exactHyperbolicDensityProbe] using
    ((continuous_const.div₀
      (UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)).pow 2)

noncomputable abbrev upperEuclideanMeasureProbe : Measure ℍ :=
  volume.comap UpperHalfPlane.coe

example :
    hyperbolicMeasure =
      upperEuclideanMeasureProbe.withDensity fun z => exactHyperbolicDensityProbe z := by
  simpa only [upperEuclideanMeasureProbe, exactHyperbolicDensityProbe] using
    hyperbolicMeasure_def
