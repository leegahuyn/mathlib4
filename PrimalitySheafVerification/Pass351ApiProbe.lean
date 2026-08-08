import Mathlib

open UpperHalfPlane MeasureTheory

#check @Submodule.mem_orthogonal
#check @Submodule.orthogonal_orthogonal_eq_closure
#check @RCLike.inner_apply
#check @Matrix.SpecialLinearGroup.toGL
#check @Matrix.SpecialLinearGroup.mapGL
#check UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff
#check @MeasurableEmbedding.memLp_map_measure_iff

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

example {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    ‖(0 : ContinuousSesquilinearForm H)‖ = 0 :=
  (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)

noncomputable def exactHyperbolicDensityProbe (z : ℍ) : NNReal :=
  ((1 : NNReal) / NNReal.mk z.im z.im_pos.le) ^ 2

example : Continuous exactHyperbolicDensityProbe := by
  have hOne : Continuous (fun _ : ℍ => (1 : NNReal)) := continuous_const
  have hIm : Continuous (fun z : ℍ => NNReal.mk z.im z.im_pos.le) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  exact (hOne.div₀ hIm (fun z hz => by
    apply z.im_ne_zero
    have hcoe := congrArg (fun x : NNReal => (x : ℝ)) hz
    simpa using hcoe)).pow 2

example (z : ℍ) :
    exactHyperbolicDensityProbe z =
      ((1 : NNReal) / NNReal.mk z.im z.im_pos.le) ^ 2 :=
  rfl

example (s t : Set ℍ) :
    {z : ℍ | ¬(z ∈ s → z ∈ t)} = s \ t := by
  ext z
  simp
