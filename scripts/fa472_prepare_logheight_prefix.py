#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa471_prepare_logheight_matrix.py"
spec = importlib.util.spec_from_file_location("fa471base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa471 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa471
spec.loader.exec_module(fa471)

fa466 = fa471.fa466
b = fa471.b

EVENTUALLY_ZERO = """by
  rcases fixedPhaseCore_eventually_selectedCuspSection_eq_zero n u with
    ⟨Y₀, hY₀, hZero⟩
  have hExpEventually : ∀ᶠ r : ℝ in Filter.atTop, Y₀ < Real.exp r :=
    Real.tendsto_exp_atTop.eventually (eventually_gt_atTop Y₀)
  filter_upwards [hExpEventually] with r hr
  have hExpOne : 1 ≤ Real.exp r :=
    le_of_lt (hY₀.trans hr)
  have hlevel : gammaTwoCuspLevel (Real.exp r) = Real.exp r :=
    gammaTwoCuspLevel_of_one_le hExpOne
  have hpoint :
      gammaTwoSelectedHorocycleParam q (Real.exp r) t =
        selectedCosetAction q (logHeightBasePoint t r) := by
    unfold gammaTwoSelectedHorocycleParam selectedCosetAction
    apply congrArg (fun z : ℍ => gammaTwoCosetRep q • z)
    apply UpperHalfPlane.ext
    simp only [logHeightBasePoint, hlevel]
  have hu0 :
      ((u : SmoothQuotientCompactFunction)
        (selectedCosetAction q (logHeightBasePoint t r))) = 0 := by
    rw [← hpoint]
    exact hZero (Real.exp r) hr q t ht
  simp only [selectedLogHeightNaturalGauge, selectedCosetUnitaryPullback,
    fixedPhaseEuclideanGauge_apply, hu0, mul_zero, Pi.zero_apply]"""

HEIGHT_BASE_POS = """by
  apply UpperHalfPlane.ext
  simp [selectedHeightBasePoint,
    UpperHalfPlane.ofComplex_apply_of_im_pos, hy]"""

HEIGHT_BASE_EXP = """by
  apply UpperHalfPlane.ext
  simp [selectedHeightBasePoint, logHeightBasePoint,
    UpperHalfPlane.ofComplex_apply_of_im_pos, Real.exp_pos]"""

ENERGY_CONTINUOUS = """by
  let h : ℍ → ℂ :=
    selectedCosetUnitaryPullback q (fixedPhaseEuclideanGauge n u)
  have hh : RealSmooth h :=
    selectedCosetUnitaryPullback_realSmooth q
      (fixedPhaseEuclideanGauge_realSmooth n u)
  have hpoint : Continuous
      (fun p : ℝ × ℝ => logHeightBasePoint p.1 p.2) := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        (p.1 : ℂ) + (Real.exp p.2 : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_snd)).mul continuous_const)
    have hcU := hc.upperHalfPlaneMk
      (fun p => by simpa using Real.exp_pos p.2)
    exact hcU.congr (fun p => by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp [logHeightBasePoint])
  have hcomp : Continuous
      (fun p : ℝ × ℝ => h (logHeightBasePoint p.1 p.2)) :=
    hh.continuous.comp hpoint
  have hdycomp : Continuous
      (fun p : ℝ × ℝ =>
        dy h (logHeightBasePoint p.1 p.2)) :=
    (RealSmooth.dy hh).continuous.comp hpoint
  have hnatural : Continuous
      (fun p : ℝ × ℝ =>
        selectedLogHeightNaturalGauge n q u p.1 p.2) := by
    unfold selectedLogHeightNaturalGauge
    exact (Complex.continuous_ofReal.comp (by fun_prop)).mul hcomp
  have hderiv : Continuous
      (fun p : ℝ × ℝ =>
        deriv (selectedLogHeightNaturalGauge n q u p.1) p.2) := by
    have hExplicit : (fun p : ℝ × ℝ =>
        deriv (selectedLogHeightNaturalGauge n q u p.1) p.2) =
        fun p => ((Real.exp (p.2 / 2) : ℝ) : ℂ) *
          ((1 / 2 : ℂ) * h (logHeightBasePoint p.1 p.2) +
            heightC (logHeightBasePoint p.1 p.2) *
              dy h (logHeightBasePoint p.1 p.2)) := by
      funext p
      exact deriv_selectedLogHeightNaturalGauge n q u p.1 p.2
    have hfactor : Continuous (fun p : ℝ × ℝ =>
        ((Real.exp (p.2 / 2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (by fun_prop)
    have hheight : Continuous (fun p : ℝ × ℝ =>
        heightC (logHeightBasePoint p.1 p.2)) := by
      unfold heightC
      exact Complex.continuous_ofReal.comp
        (UpperHalfPlane.continuous_im.comp hpoint)
    rw [hExplicit]
    exact hfactor.mul
      ((continuous_const.mul hcomp).add (hheight.mul hdycomp))
  unfold selectedLogHeightEnergyDensity
  exact (hnatural.norm.pow 2).add (hderiv.norm.pow 2)"""

UNIFORM_ZERO = """by
  rcases fixedPhaseCore_eventually_selectedCuspSection_eq_zero n u with
    ⟨Y₀, hY₀, hZero⟩
  have hY₀pos : 0 < Y₀ := zero_lt_one.trans hY₀
  refine ⟨Real.log Y₀, ?_⟩
  intro t ht r hr
  have hExp : Y₀ < Real.exp r := by
    rw [← Real.exp_log hY₀pos]
    exact Real.exp_lt_exp.mpr hr
  have hExpOne : 1 ≤ Real.exp r :=
    le_of_lt (hY₀.trans hExp)
  have hlevel : gammaTwoCuspLevel (Real.exp r) = Real.exp r :=
    gammaTwoCuspLevel_of_one_le hExpOne
  have hpoint :
      gammaTwoSelectedHorocycleParam q (Real.exp r) t =
        selectedCosetAction q (logHeightBasePoint t r) := by
    unfold gammaTwoSelectedHorocycleParam selectedCosetAction
    apply congrArg (fun z : ℍ => gammaTwoCosetRep q • z)
    apply UpperHalfPlane.ext
    simp only [logHeightBasePoint, hlevel]
  have hu0 :
      ((u : SmoothQuotientCompactFunction)
        (selectedCosetAction q (logHeightBasePoint t r))) = 0 := by
    rw [← hpoint]
    exact hZero (Real.exp r) hExp q t ht
  simp only [selectedLogHeightNaturalGauge, selectedCosetUnitaryPullback,
    fixedPhaseEuclideanGauge_apply, hu0, mul_zero]"""

orig_norm_repairs = fa471.orig_norm_repairs


def norm_repairs(text: str):
    text, repairs = orig_norm_repairs(text)
    text = b.replace_body(
        text, "RealSmooth.comp_logHeightBasePoint", fa471.COMP_DIRECT)
    text = b.replace_body(text, "deriv_comp_logHeightBasePoint", fa471.DERIV_LOG)
    text = b.replace_body(
        text, "selectedLogHeightNaturalGauge_contDiff", fa471.GAUGE_CONTDIFF)
    text = b.replace_body(
        text, "deriv_selectedLogHeightNaturalGauge", fa471.GAUGE_DERIV)
    text = b.replace_in(
        text, "norm_deriv_selectedLogHeightNaturalGauge_le_graph",
        "rw [norm_mul, Complex.norm_real,\n    abs_of_pos",
        "rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,\n    abs_of_pos")
    text = b.replace_in(
        text, "selectedCosetUnitaryPullback_log_cuspLevel",
        "apply Subtype.ext", "apply UpperHalfPlane.ext")
    text = b.replace_in(
        text, "selectedCosetUnitaryPullback_log_cuspLevel",
        "simp only [heightC, logHeightBasePoint_im, Real.exp_log hH,",
        "simp only [heightC, logHeightBasePoint_im, H, Real.exp_log hH,")
    text = b.replace_in(
        text, "normSq_selectedLogHeightNaturalGauge_at_log_cuspLevel",
        "rw [norm_mul, Complex.norm_real,\n    abs_of_pos",
        "rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,\n    abs_of_pos")
    text = b.replace_body(
        text, "selectedLogHeightNaturalGauge_eventuallyEq_zero", EVENTUALLY_ZERO)
    text = b.replace_body(
        text, "selectedHeightBasePoint_of_pos", HEIGHT_BASE_POS)
    text = b.replace_body(
        text, "selectedHeightBasePoint_exp", HEIGHT_BASE_EXP)
    text = b.replace_in(
        text, "selectedLogHeightEnergyDensity_le_exp_mul_heightGraphDensity",
        "rw [norm_mul, Complex.norm_real, abs_of_pos (Real.exp_pos _),\n"
        "      hPullNorm, mul_pow, mul_pow, hExp]\n"
        "    ring",
        "rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,\n"
        "      abs_of_pos (Real.exp_pos _), hPullNorm, mul_pow, mul_pow, hExp]\n"
        "      <;> ring")
    text = b.replace_in(
        text, "selectedLogHeightEnergyDensity_le_exp_mul_heightGraphDensity",
        "rw [mul_pow, mul_pow, hExp]\n        ring",
        "rw [mul_pow, mul_pow, hExp] <;> ring")
    variant = os.environ.get("PREFIX_VARIANT", "prefix11")
    if variant == "continuous14":
        text = b.replace_body(
            text, "selectedLogHeightEnergyDensity_continuous", ENERGY_CONTINUOUS)
    if variant in {"prefix14", "continuous14"}:
        text = b.replace_body(
            text, "selectedLogHeightNaturalGauge_uniform_eventually_zero",
            UNIFORM_ZERO)
        text = b.replace_in(
            text, "integral_selectedLogHeightEnergyDensity_stripTail_eq_iterated",
            "change (∫ p, selectedLogHeightEnergyDensity n q u p ∂μ.prod ν) =\n"
            "    ∫ t, ∫ r, selectedLogHeightEnergyDensity n q u (t, r) ∂ν ∂μ\n"
            "  exact integral_prod _ hProd",
            "simpa only [μ, ν, Measure.prod_restrict] using\n"
            "    (integral_prod (selectedLogHeightEnergyDensity n q u) hProd)")
    return text, repairs + [{
        "declaration": "log-height prefix through joint continuity/Fubini",
        "strategy": variant,
    }]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
