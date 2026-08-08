import Mathlib

open Set Filter

noncomputable section

noncomputable def probeLeftParam (t : ℝ) : ℂ :=
  (((-(1 / 2 : ℝ)) : ℂ) +
    ((Real.sqrt 3 / 2 + t : ℝ) : ℂ) * Complex.I)

noncomputable def probeRightParam (t : ℝ) : ℂ :=
  ((((1 / 2 : ℝ)) : ℂ) +
    ((Real.sqrt 3 / 2 + t : ℝ) : ℂ) * Complex.I)

set_option backward.isDefEq.respectTransparency false in
example (t : ℝ) : HasDerivAt probeLeftParam Complex.I t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  dsimp [probeLeftParam]
  push_cast
  field_simp [hs]
  ring

set_option backward.isDefEq.respectTransparency false in
example (t : ℝ) : HasDerivAt probeRightParam Complex.I t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  dsimp [probeRightParam]
  push_cast
  field_simp [hs]
  ring

example (t : ℝ) :
    (((1 / 2 : ℝ) : ℂ) +
        (((-t / (4 * Real.sqrt (1 - t ^ 2 / 4)) : ℝ) : ℂ) * Complex.I)) =
      ({ re := 1 / 2
         im := -t / (4 * Real.sqrt (1 - t ^ 2 / 4)) } : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
      sub_zero, add_zero, zero_add]
