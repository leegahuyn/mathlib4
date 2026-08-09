import Mathlib

noncomputable section

open MeasureTheory Set Function Topology Filter
open scoped RealInnerProductSpace

local instance probeSL2ZMeasurableConstSMul :
    MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul g := by
    change Measurable (fun z : ℍ => ((g : GL (Fin 2) ℝ) • z))
    exact (continuous_const_smul _).measurable

noncomputable abbrev probeParameterMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))

example (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 probeParameterMeasure := by
  letI : MeasurableSpace ℝ := Real.measureSpace.toMeasurableSpace
  apply (memLp_two_iff_integrable_sq_norm
    hf.aestronglyMeasurable).2
  change IntegrableOn (fun x => ‖f x‖ ^ 2)
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) volume
  simpa only [Pi.pow_apply] using
    (hf.norm.pow 2).continuousOn.integrableOn_Icc

example {f : ℝ → ℂ} (hf : Differentiable ℝ f) (y : ℝ) :
    deriv (fun r : ℝ => r * ‖f r‖ ^ 2) y =
      ‖f y‖ ^ 2 + 2 * y * ⟪f y, deriv f y⟫_ℝ := by
  have hnorm := (hf y).hasDerivAt.norm_sq
  have hprod := (hasDerivAt_id y).mul hnorm
  convert hprod.deriv using 1 <;> ring

example {f : ℝ → ℂ} (hcompact : HasCompactSupport f) :
    HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
  simpa only [Function.comp_apply] using
    hcompact.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)

example {f : ℝ → ℂ}
    (hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2)) :
    HasCompactSupport (fun y : ℝ => y * ‖f y‖ ^ 2) := by
  apply hnormSq.mono
  intro y hy hzero
  apply hy
  simp only [hzero, mul_zero]

example {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (r : ℝ) :
    ‖‖deriv (fun s : ℝ => ‖f s‖ ^ 2) r‖‖ ≤
      ‖‖f r‖ ^ 2 + ‖deriv f r‖ ^ 2‖ := by
  have hpoint :
      ‖deriv (fun s : ℝ => ‖f s‖ ^ 2) r‖ ≤
        ‖f r‖ ^ 2 + ‖deriv f r‖ ^ 2 := by
    have hinner := abs_real_inner_le_norm (f r) (deriv f r)
    rw [(hf.differentiable (by norm_num) r).hasDerivAt.norm_sq.deriv,
      Real.norm_eq_abs]
    calc
      2 * |⟪f r, deriv f r⟫_ℝ| ≤
          2 * (‖f r‖ * ‖deriv f r‖) := by
        exact mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ ‖f r‖ ^ 2 + ‖deriv f r‖ ^ 2 := by
        nlinarith [sq_nonneg (‖f r‖ - ‖deriv f r‖)]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))] using hpoint

example (hcomplex : Continuous (fun t : ℝ =>
    (t : ℂ) + (2 : ℂ) * Complex.I)) :
    Continuous (fun t : ℝ =>
      (⟨(t : ℂ) + (2 : ℂ) * Complex.I, by norm_num⟩ : ℍ)) := by
  exact hcomplex.upperHalfPlaneMk _
