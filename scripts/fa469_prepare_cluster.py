#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa467_prepare_horizontal_close.py"
spec = importlib.util.spec_from_file_location("fa467base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa467 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa467
spec.loader.exec_module(fa467)

fa466 = fa467.fa466
b = fa466.b

SMOOTH = """by
  have hnum : RealSmooth
      (fun z => heightC (selectedCosetAction q z)) :=
    RealSmooth.comp_selectedCosetAction realSmooth_heightC q
  have hdenInv : RealSmooth (fun z => (heightC z)⁻¹) :=
    RealSmooth.inv realSmooth_heightC (fun z => heightC_ne_zero z)
  have hfun :
      selectedCosetConformalScaleC q =
        (fun z => heightC (selectedCosetAction q z)) *
          (fun z => (heightC z)⁻¹) := by
    funext z
    simp only [selectedCosetConformalScaleC, Pi.mul_apply,
      div_eq_mul_inv]
  rw [hfun]
  exact RealSmooth.mul hnum hdenInv"""

SCALE_EQ = """by
  have haction : selectedCosetAction q z = selectedCosetGL q • z := by
    apply UpperHalfPlane.ext
    simp [selectedCosetAction, selectedCosetGL]
  unfold selectedCosetConformalScaleC
  rw [haction]
  unfold heightC
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp only [selectedCosetGL_det, Int.reduceAbs, one_mul,
    Complex.ofReal_div, Complex.ofReal_one]
  field_simp [z.im_ne_zero] <;> simp"""

DX_SCALE = """by
  let N : ℍ → ℂ := fun w => heightC (selectedCosetAction q w)
  let Dinv : ℍ → ℂ := fun w => (heightC w)⁻¹
  have hN : RealSmooth N :=
    RealSmooth.comp_selectedCosetAction realSmooth_heightC q
  have hDinv : RealSmooth Dinv :=
    RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)
  have hdxN : dx N z = selectedCosetB q z := by
    simpa only [N, dx_heightC, dy_heightC, mul_zero, mul_one,
      zero_add] using
        dx_comp_selectedCosetAction q realSmooth_heightC z
  have hdxDinv : dx Dinv z = 0 := by
    change d1 Dinv z 1 = 0
    rw [show d1 Dinv z 1 =
        -(d1 heightC z 1) / heightC z ^ 2 by
      simpa only [Dinv] using
        d1_inv realSmooth_heightC z 1 (heightC_ne_zero z),
      d1_heightC]
    simp
  have hfun : selectedCosetConformalScaleC q = N * Dinv := by
    funext w
    simp only [selectedCosetConformalScaleC, N, Dinv,
      Pi.mul_apply, div_eq_mul_inv]
  rw [hfun, dx_mul hN hDinv, hdxN, hdxDinv]
  simp only [mul_zero, add_zero, Dinv, Pi.mul_apply, div_eq_mul_inv]"""

DY_SCALE = """by
  let N : ℍ → ℂ := fun w => heightC (selectedCosetAction q w)
  let Dinv : ℍ → ℂ := fun w => (heightC w)⁻¹
  have hN : RealSmooth N :=
    RealSmooth.comp_selectedCosetAction realSmooth_heightC q
  have hDinv : RealSmooth Dinv :=
    RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)
  have hdyN : dy N z = selectedCosetA q z := by
    simpa only [N, dx_heightC, dy_heightC, mul_zero, mul_one,
      add_zero, zero_add] using
        dy_comp_selectedCosetAction q realSmooth_heightC z
  have hdyDinv : dy Dinv z = -(1 / heightC z ^ 2) := by
    change d1 Dinv z Complex.I = _
    rw [show d1 Dinv z Complex.I =
        -(d1 heightC z Complex.I) / heightC z ^ 2 by
      simpa only [Dinv] using
        d1_inv realSmooth_heightC z Complex.I (heightC_ne_zero z),
      d1_heightC]
    field_simp [heightC_ne_zero z] <;> ring_nf
  have hfun : selectedCosetConformalScaleC q = N * Dinv := by
    funext w
    simp only [selectedCosetConformalScaleC, N, Dinv,
      Pi.mul_apply, div_eq_mul_inv]
  rw [hfun, dy_mul hN hDinv, hdyN, hdyDinv]
  simp only [Dinv, N, Pi.mul_apply, div_eq_mul_inv]
  have hz : heightC z ≠ 0 := heightC_ne_zero z
  field_simp [hz]
  <;> ring"""

NORM_DERIV = """by
  have hden :
      UpperHalfPlane.denom (selectedCosetGL q) z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero (selectedCosetGL q) z
  rw [selectedCosetConformalScaleC_eq_inv_normSq_denom]
  unfold selectedCosetDerivative selectedCosetDenom
  rw [Complex.norm_real,
    abs_of_pos (one_div_pos.mpr (Complex.normSq_pos.mpr hden)),
    norm_div, norm_one, norm_pow, Complex.normSq_eq_norm_sq]"""

DX_PULLBACK = """by
  unfold selectedCosetUnitaryPullback
  change dx
      (selectedCosetConformalScaleC q *
        fun w => f (selectedCosetAction q w)) z = _
  rw [dx_mul (selectedCosetConformalScaleC_realSmooth q)
    (RealSmooth.comp_selectedCosetAction hf q),
    dx_comp_selectedCosetAction q hf]"""

DY_PULLBACK = """by
  unfold selectedCosetUnitaryPullback
  change dy
      (selectedCosetConformalScaleC q *
        fun w => f (selectedCosetAction q w)) z = _
  rw [dy_mul (selectedCosetConformalScaleC_realSmooth q)
    (RealSmooth.comp_selectedCosetAction hf q),
    dy_comp_selectedCosetAction q hf]"""

HEIGHT_DY_PULLBACK = """by
  rw [dy_selectedCosetUnitaryPullback q hf]
  have hscale :
      heightC z * selectedCosetConformalScaleC q z =
        heightC (selectedCosetAction q z) := by
    unfold selectedCosetConformalScaleC
    exact mul_div_cancel₀ _ (heightC_ne_zero z)
  calc
    heightC z *
        (dy (selectedCosetConformalScaleC q) z *
            f (selectedCosetAction q z) +
          selectedCosetConformalScaleC q z *
            (-selectedCosetB q z * dx f (selectedCosetAction q z) +
              selectedCosetA q z * dy f (selectedCosetAction q z))) =
      (heightC z * dy (selectedCosetConformalScaleC q) z) *
          f (selectedCosetAction q z) +
        (heightC z * selectedCosetConformalScaleC q z) *
          (-selectedCosetB q z * dx f (selectedCosetAction q z) +
            selectedCosetA q z * dy f (selectedCosetAction q z)) := by
      ring
    _ = (selectedCosetA q z - selectedCosetConformalScaleC q z) *
          f (selectedCosetAction q z) +
        heightC (selectedCosetAction q z) *
          (-selectedCosetB q z * dx f (selectedCosetAction q z) +
            selectedCosetA q z * dy f (selectedCosetAction q z)) := by
      rw [height_mul_dy_selectedCosetConformalScaleC, hscale]
    _ = (selectedCosetA q z - selectedCosetConformalScaleC q z) *
          f (selectedCosetAction q z) -
        selectedCosetB q z *
          (heightC (selectedCosetAction q z) *
            dx f (selectedCosetAction q z)) +
        selectedCosetA q z *
          (heightC (selectedCosetAction q z) *
            dy f (selectedCosetAction q z)) := by
      ring"""

NORM_HEIGHT_DY_PULLBACK = """by
  rw [height_mul_dy_selectedCosetUnitaryPullback q hf]
  let A := selectedCosetA q z
  let B := selectedCosetB q z
  let S := selectedCosetConformalScaleC q z
  let F := f (selectedCosetAction q z)
  let Fx := heightC (selectedCosetAction q z) *
    dx f (selectedCosetAction q z)
  let Fy := heightC (selectedCosetAction q z) *
    dy f (selectedCosetAction q z)
  have hA : ‖A‖ ≤ ‖S‖ := norm_selectedCosetA_le_scale q z
  have hB : ‖B‖ ≤ ‖S‖ := norm_selectedCosetB_le_scale q z
  have hAS : ‖A - S‖ ≤ 2 * ‖S‖ := by
    calc
      ‖A - S‖ ≤ ‖A‖ + ‖S‖ := norm_sub_le _ _
      _ ≤ ‖S‖ + ‖S‖ := by
        exact add_le_add hA (le_refl ‖S‖)
      _ = 2 * ‖S‖ := by ring
  change ‖(A - S) * F - B * Fx + A * Fy‖ ≤
    ‖S‖ * (2 * ‖F‖ + ‖Fx‖ + ‖Fy‖)
  calc
    ‖(A - S) * F - B * Fx + A * Fy‖ ≤
        ‖(A - S) * F‖ + ‖B * Fx‖ + ‖A * Fy‖ := by
      calc
        _ ≤ ‖(A - S) * F - B * Fx‖ + ‖A * Fy‖ := norm_add_le _ _
        _ ≤ (‖(A - S) * F‖ + ‖B * Fx‖) + ‖A * Fy‖ := by
          exact add_le_add
            (norm_sub_le ((A - S) * F) (B * Fx))
            (le_refl ‖A * Fy‖)
    _ = ‖A - S‖ * ‖F‖ + ‖B‖ * ‖Fx‖ + ‖A‖ * ‖Fy‖ := by
      have hAF : ‖(A - S) * F‖ = ‖A - S‖ * ‖F‖ := norm_mul _ _
      have hBF : ‖B * Fx‖ = ‖B‖ * ‖Fx‖ := norm_mul _ _
      have hAY : ‖A * Fy‖ = ‖A‖ * ‖Fy‖ := norm_mul _ _
      rw [hAF, hBF, hAY]
    _ ≤ (2 * ‖S‖) * ‖F‖ + ‖S‖ * ‖Fx‖ + ‖S‖ * ‖Fy‖ := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_right hAS (norm_nonneg F))
          (mul_le_mul_of_nonneg_right hB (norm_nonneg Fx)))
        (mul_le_mul_of_nonneg_right hA (norm_nonneg Fy))
    _ = ‖S‖ * (2 * ‖F‖ + ‖Fx‖ + ‖Fy‖) := by ring"""

LOG_DRIFT_NONNEG = """by
  unfold logHeightTraceDrift
  exact add_nonneg (by norm_num)
    (div_nonneg (euclideanHorizontalDrift_nonneg n) (by norm_num))"""

L2_NORM = """by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner F F)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t =>
    inner_self_eq_norm_sq (𝕜 := ℂ) (F t)"""

fa466.SMOOTH = SMOOTH
fa466.SCALE_EQ = SCALE_EQ
fa466.NORM_DERIV = NORM_DERIV


def dxdy_repairs(text: str):
    text = b.replace_body(text, "dx_selectedCosetConformalScaleC", DX_SCALE)
    text = b.replace_body(text, "dy_selectedCosetConformalScaleC", DY_SCALE)
    return text, [{
        "declaration": "dx/dy_selectedCosetConformalScaleC",
        "strategy": "explicit_pi_product_and_typed_inverse_derivative",
    }]


def norm_repairs(text: str):
    text = b.replace_body(
        text, "norm_selectedCosetConformalScaleC_eq_derivative", NORM_DERIV)
    text = b.replace_in(
        text, "norm_selectedCosetA_le_scale",
        "simp only [selectedCosetA, Complex.norm_real]",
        "simp only [selectedCosetA, Complex.norm_real, Real.norm_eq_abs]")
    text = b.replace_in(
        text, "norm_selectedCosetB_le_scale",
        "simp only [selectedCosetB, Complex.norm_real]",
        "simp only [selectedCosetB, Complex.norm_real, Real.norm_eq_abs]")
    text = b.replace_in(
        text, "norm_height_mul_dy_selectedCosetConformalScaleC_le",
        "exact add_le_add_right (norm_selectedCosetA_le_scale q z) _",
        "exact add_le_add (norm_selectedCosetA_le_scale q z) "
        "(le_refl ‖selectedCosetConformalScaleC q z‖)")
    text = b.replace_body(text, "dx_selectedCosetUnitaryPullback", DX_PULLBACK)
    text = b.replace_body(text, "dy_selectedCosetUnitaryPullback", DY_PULLBACK)
    text = b.replace_body(
        text, "height_mul_dy_selectedCosetUnitaryPullback", HEIGHT_DY_PULLBACK)
    text = b.replace_body(
        text, "norm_height_mul_dy_selectedCosetUnitaryPullback_le",
        NORM_HEIGHT_DY_PULLBACK)
    text = b.replace_in(
        text, "norm_height_mul_dy_selectedCosetUnitaryPullback_le_graph",
        ":= by gcongr",
        ":= by\n        exact add_le_add\n"
        "          (add_le_add (le_refl (2 * F)) hX) hV")
    text = b.replace_body(text, "logHeightTraceDrift_nonneg", LOG_DRIFT_NONNEG)
    text = b.replace_in(
        text, "height_mul_normSq_selectedCuspPulledEuclideanGauge",
        "Complex.norm_real, abs_of_pos (Real.rpow_pos_of_pos hz _)",
        "Complex.norm_real, Real.norm_eq_abs,\n"
        "          abs_of_pos (Real.rpow_pos_of_pos hz _)")
    text = b.replace_in(
        text, "height_mul_normSq_selectedCuspPulledEuclideanGauge",
        "rw [norm_mul, Complex.norm_real, abs_of_pos hs, hGauge,",
        "rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, "
        "abs_of_pos hs, hGauge,")
    text = b.replace_in(
        text, "normSq_selectedCuspRestrictionRepresentative_eq_height_mul_pulled",
        "rw [Complex.norm_real,\n      abs_of_pos",
        "rw [Complex.norm_real, Real.norm_eq_abs,\n      abs_of_pos")
    text = b.replace_body(text, "selectedHorocycleL2_norm_sq_eq_integral", L2_NORM)
    return text, [{
        "declaration": "selectedCoset unitary/norm/cusp L2 cluster",
        "strategy": "typed_direct_log_evidence_repairs",
    }]


fa466.dxdy_repairs = dxdy_repairs
fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
