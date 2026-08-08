import Mathlib

open Set

noncomputable section

noncomputable def probeLeftParam (t : ℝ) : ℂ :=
  (((-(1 / 2 : ℝ)) : ℂ) +
    ((Real.sqrt 3 / 2 + t : ℝ) : ℂ) * Complex.I)

noncomputable def probeRightParam (t : ℝ) : ℂ :=
  ((((1 / 2 : ℝ)) : ℂ) +
    ((Real.sqrt 3 / 2 + t : ℝ) : ℂ) * Complex.I)

set_option backward.isDefEq.respectTransparency false in
example (t : Set.Ici (0 : ℝ)) :
    HasDerivAt probeLeftParam Complex.I (t : ℝ) := by
  have hxR : HasDerivAt (fun _s : ℝ => -(1 / 2 : ℝ)) 0 t :=
    hasDerivAt_const (t : ℝ) _
  have hyR : HasDerivAt
      (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      (hasDerivAt_const (t : ℝ) (Real.sqrt 3 / 2)).add
        (hasDerivAt_id (t : ℝ))
  unfold probeLeftParam
  exact hxR.ofReal_comp.add (hyR.ofReal_comp.mul_const Complex.I)

set_option backward.isDefEq.respectTransparency false in
example (t : Set.Ici (0 : ℝ)) :
    HasDerivAt probeRightParam Complex.I (t : ℝ) := by
  have hxR : HasDerivAt (fun _s : ℝ => (1 / 2 : ℝ)) 0 t :=
    hasDerivAt_const (t : ℝ) _
  have hyR : HasDerivAt
      (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      (hasDerivAt_const (t : ℝ) (Real.sqrt 3 / 2)).add
        (hasDerivAt_id (t : ℝ))
  unfold probeRightParam
  exact hxR.ofReal_comp.add (hyR.ofReal_comp.mul_const Complex.I)
