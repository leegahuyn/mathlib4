#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT=Path.cwd()
spec=importlib.util.spec_from_file_location(
    "fa461_v1", ROOT / "scripts/fa461_prepare_gl_analytic_cluster1.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA461 v1 preparer")
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)

REAL_SMOOTH_SCALE = """by
  have hnum : RealSmooth
      (fun z => heightC (selectedCosetAction q z)) :=
    RealSmooth.comp_selectedCosetAction realSmooth_heightC q
  have hdenInv : RealSmooth (fun z => (heightC z)⁻¹) :=
    RealSmooth.inv realSmooth_heightC (fun z => heightC_ne_zero z)
  have hfun : selectedCosetConformalScaleC q =
      (fun z => heightC (selectedCosetAction q z)) *
        (fun z => (heightC z)⁻¹) := by
    funext z
    simp only [selectedCosetConformalScaleC, Pi.mul_apply, div_eq_mul_inv]
  rw [hfun]
  exact hnum.mul hdenInv"""

NORM_DERIV_V2 = """by
  have hden := selectedCosetDenom_ne_zero q z
  have hnorm : 0 < ‖selectedCosetDenom q z‖ := norm_pos_iff.mpr hden
  rw [selectedCosetConformalScaleC_eq_inv_normSq_denom]
  change
    ‖(1 / Complex.normSq (selectedCosetDenom q z) : ℝ)‖ =
      ‖1 / selectedCosetDenom q z ^ 2‖
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr
    (Complex.normSq_pos.mpr hden)), norm_div, norm_one, norm_pow,
    Complex.normSq_eq_norm_sq]"""

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
  rw [mul_add, height_mul_dy_selectedCosetConformalScaleC]
  calc
    _ = (selectedCosetA q z - selectedCosetConformalScaleC q z) *
          f (selectedCosetAction q z) +
        (heightC z * selectedCosetConformalScaleC q z) *
          (-selectedCosetB q z * dx f (selectedCosetAction q z) +
            selectedCosetA q z * dy f (selectedCosetAction q z)) := by ring
    _ = _ := by rw [hscale]; ring"""


def apply_cluster1_v2(text: str):
    repairs=[]
    text=mod.replace_body(text,"selectedCosetConformalScaleC_realSmooth",REAL_SMOOTH_SCALE)
    repairs.append({"declaration":"selectedCosetConformalScaleC_realSmooth","strategy":"rewrite_function_before_RealSmooth_mul"})
    text=mod.replace_in_decl(text,"dx_selectedCosetConformalScaleC",
        "realSmooth_heightC.inv (fun w => heightC_ne_zero w)",
        "RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)")
    text=mod.replace_in_decl(text,"dy_selectedCosetConformalScaleC",
        "realSmooth_heightC.inv (fun w => heightC_ne_zero w)",
        "RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)")
    text=mod.replace_in_decl(text,"dy_selectedCosetConformalScaleC",
        "simpa only [N, dx_heightC, dy_heightC, mul_zero, mul_one,\n      add_zero] using",
        "simpa only [N, dx_heightC, dy_heightC, mul_zero, mul_one,\n      add_zero, zero_add] using")
    repairs.append({"declaration":"dx/dy_selectedCosetConformalScaleC","strategy":"qualified_inv_and_zero_add_normalization"})
    text=mod.replace_body(text,"selectedCosetConformalScaleC_eq_inv_normSq_denom",mod.SCALE_EQ)
    repairs.append({"declaration":"selectedCosetConformalScaleC_eq_inv_normSq_denom","strategy":"selectedCosetGL_im_smul_formula"})
    text=mod.replace_body(text,"norm_selectedCosetConformalScaleC_eq_derivative",NORM_DERIV_V2)
    repairs.append({"declaration":"norm_selectedCosetConformalScaleC_eq_derivative","strategy":"real_norm_after_folded_selectedCosetDenom"})
    text=mod.replace_in_decl(text,"norm_selectedCosetA_le_scale",
        "simp only [selectedCosetA, Complex.norm_real]",
        "simp only [selectedCosetA, Complex.norm_real, Real.norm_eq_abs]")
    text=mod.replace_in_decl(text,"norm_selectedCosetB_le_scale",
        "simp only [selectedCosetB, Complex.norm_real]",
        "simp only [selectedCosetB, Complex.norm_real, Real.norm_eq_abs]")
    text=mod.replace_in_decl(text,"norm_height_mul_dy_selectedCosetConformalScaleC_le",
        "exact add_le_add_right (norm_selectedCosetA_le_scale q z) _",
        "exact add_le_add (norm_selectedCosetA_le_scale q z) (le_refl _)")
    repairs.append({"declaration":"selectedCoset norm bounds","strategy":"typed_add_le_add_and_real_norm"})
    text=mod.replace_body(text,"dx_selectedCosetUnitaryPullback",DX_PULLBACK)
    text=mod.replace_body(text,"dy_selectedCosetUnitaryPullback",DY_PULLBACK)
    repairs.append({"declaration":"dx/dy_selectedCosetUnitaryPullback","strategy":"change_to_pointwise_function_product_before_product_rule"})
    text=mod.replace_body(text,"height_mul_dy_selectedCosetUnitaryPullback",HEIGHT_DY_PULLBACK)
    repairs.append({"declaration":"height_mul_dy_selectedCosetUnitaryPullback","strategy":"factor_height_scale_then_rewrite"})
    text=mod.replace_in_decl(text,"norm_height_mul_dy_selectedCosetUnitaryPullback_le",
        "_ ≤ ‖S‖ + ‖S‖ := add_le_add_right hA _",
        "_ ≤ ‖S‖ + ‖S‖ := add_le_add hA (le_refl _)")
    repairs.append({"declaration":"norm_height_mul_dy_selectedCosetUnitaryPullback_le","strategy":"typed_add_le_add"})
    text=mod.replace_body(text,"logHeightTraceDrift_nonneg",mod.LOG_DRIFT)
    text=mod.replace_in_decl(text,"height_mul_normSq_selectedCuspPulledEuclideanGauge",
        "Complex.norm_real, abs_of_pos (Real.rpow_pos_of_pos hz _)",
        "Complex.norm_real, Real.norm_eq_abs,\n          abs_of_pos (Real.rpow_pos_of_pos hz _)")
    text=mod.replace_in_decl(text,"normSq_selectedCuspRestrictionRepresentative_eq_height_mul_pulled",
        "Complex.norm_real,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t)",
        "Complex.norm_real, Real.norm_eq_abs,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t)")
    repairs.append({"declaration":"selected cusp norm identities","strategy":"complex_norm_real_then_real_norm_abs"})
    text=mod.replace_body(text,"selectedHorocycleL2_norm_sq_eq_integral",mod.L2_NORM)
    repairs.append({"declaration":"selectedHorocycleL2_norm_sq_eq_integral","strategy":"explicit_complex_inner_scalar"})
    return text,repairs

mod.apply_cluster1=apply_cluster1_v2

if __name__=="__main__":
    mod.main()
