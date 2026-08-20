#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa469_prepare_cluster.py"
spec = importlib.util.spec_from_file_location("fa469base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa469 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa469
spec.loader.exec_module(fa469)

fa466 = fa469.fa466
b = fa469.b

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
    simpa only [Complex.I_im, Complex.ofReal_one, neg_div]
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
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (Complex.normSq_pos.mpr hden)),
    norm_div, norm_one, norm_pow, Complex.normSq_eq_norm_sq]"""

orig_dxdy_repairs = fa469.dxdy_repairs
orig_norm_repairs = fa469.norm_repairs


def dxdy_repairs(text: str):
    text, repairs = orig_dxdy_repairs(text)
    text = b.replace_body(text, "dy_selectedCosetConformalScaleC", DY_SCALE)
    return text, repairs + [{
        "declaration": "dy_selectedCosetConformalScaleC",
        "strategy": "normalize_Complex_I_im_after_inverse_derivative",
    }]


def norm_repairs(text: str):
    text, repairs = orig_norm_repairs(text)
    text = b.replace_body(
        text, "norm_selectedCosetConformalScaleC_eq_derivative", NORM_DERIV)
    text = b.replace_in(
        text, "height_mul_normSq_selectedCuspPulledEuclideanGauge",
        "Real.norm_eq_abs, abs_of_pos hs, hGauge,",
        "Real.norm_eq_abs, abs_of_pos hs, mul_pow, hGauge,")
    return text, repairs + [{
        "declaration": "norm derivative and cusp gauge square",
        "strategy": "real_norm_to_abs_and_expand_mul_pow",
    }]


fa466.dxdy_repairs = dxdy_repairs
fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
