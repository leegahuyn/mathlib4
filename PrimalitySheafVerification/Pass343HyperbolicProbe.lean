import Mathlib

open UpperHalfPlane MeasureTheory

/-- Candidate NNReal hyperbolic density written through inversion in `ℝ`. -/
noncomputable def hyperbolicDensityProbe (z : ℍ) : NNReal :=
  ⟨z.im⁻¹ ^ 2, sq_nonneg _⟩

@[simp]
theorem hyperbolicDensityProbe_coe (z : ℍ) :
    (hyperbolicDensityProbe z : ℝ) = z.im⁻¹ ^ 2 :=
  rfl

theorem hyperbolicDensityProbe_continuous :
    Continuous hyperbolicDensityProbe := by
  exact
    ((UpperHalfPlane.continuous_im.inv₀ (fun z => z.im_ne_zero)).pow 2).subtype_mk
      (fun z => sq_nonneg (z.im⁻¹))

noncomputable abbrev upperEuclideanMeasureProbe : Measure ℍ :=
  volume.comap UpperHalfPlane.coe

#check hyperbolicMeasure_def

theorem hyperbolicMeasure_eq_probe :
    hyperbolicMeasure =
      upperEuclideanMeasureProbe.withDensity fun z => hyperbolicDensityProbe z := by
  simpa only [upperEuclideanMeasureProbe, hyperbolicDensityProbe, one_div] using
    hyperbolicMeasure_def
