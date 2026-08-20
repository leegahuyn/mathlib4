#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa470_prepare_first_three.py"
spec = importlib.util.spec_from_file_location("fa470base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa470 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa470
spec.loader.exec_module(fa470)

fa466 = fa470.fa466
b = fa470.b

COMP_DIRECT = """by
  let p : ℝ → ℂ := fun r => Complex.mk t (Real.exp r)
  have hExpC : ContDiff ℝ ∞
      (fun r : ℝ => ((Real.exp r : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp Real.contDiff_exp
  have hp : ContDiff ℝ ∞ p := by
    have hprod : ContDiff ℝ ∞
        (fun r : ℝ => ((Real.exp r : ℝ) : ℂ) * Complex.I) :=
      hExpC.mul contDiff_const
    simpa only [p, Complex.mk_eq_add_mul_I] using
      (contDiff_const.add hprod)
  have hpMaps : Set.MapsTo p Set.univ
      UpperHalfPlane.upperHalfPlaneSet := by
    intro r _hr
    change 0 < Real.exp r
    exact Real.exp_pos r
  unfold RealSmooth at hf
  have hcomp := hf.comp hp.contDiffOn hpMaps
  rw [contDiffOn_univ] at hcomp
  simpa only [p, upperLift, Function.comp_def, logHeightBasePoint,
    UpperHalfPlane.ofComplex_apply_of_im_pos, Real.exp_pos] using hcomp"""

COMP_SURROGATE = """by
  let p : ℝ → ℂ := fun r => Complex.mk t (Real.exp r)
  let p' : ℝ → ℂ := fun r => (t : ℂ) + (Real.exp r : ℂ) * Complex.I
  have hExpC : ContDiff ℝ ∞ (fun r : ℝ => (Real.exp r : ℂ)) := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp
        (by fun_prop : ContDiff ℝ ∞ fun r : ℝ => Real.exp r)
  have hp' : ContDiff ℝ ∞ p' :=
    contDiff_const.add (hExpC.mul contDiff_const)
  have hpEq : p = p' := by
    funext r
    apply Complex.ext <;> simp [p, p']
  have hp : ContDiff ℝ ∞ p := by
    rw [hpEq]
    exact hp'
  have hpMaps : Set.MapsTo p Set.univ
      UpperHalfPlane.upperHalfPlaneSet := by
    intro r _hr
    change 0 < Real.exp r
    exact Real.exp_pos r
  unfold RealSmooth at hf
  have hcomp := hf.comp hp.contDiffOn hpMaps
  rw [contDiffOn_univ] at hcomp
  simpa only [p, upperLift, Function.comp_def, logHeightBasePoint,
    UpperHalfPlane.ofComplex_apply_of_im_pos, Real.exp_pos] using hcomp"""

DERIV_LOG = """by
  let p : ℝ → ℂ := fun s => Complex.mk t (Real.exp s)
  let z : ℍ := logHeightBasePoint t r
  have hpDeriv : HasDerivAt p
      (Complex.I * (Real.exp r : ℂ)) r := by
    have hExp := (Real.hasDerivAt_exp r).ofReal_comp
    have hIm := hExp.const_mul Complex.I
    have hRe := hasDerivAt_const r (t : ℂ)
    simpa only [p, Complex.mk_eq_add_mul_I, Pi.add_apply, zero_add,
      add_comm, mul_comm] using hRe.add hIm
  have hOuter : DifferentiableAt ℝ (upperLift f) (z : ℂ) :=
    (RealSmooth.contDiffAt_upperLift hf z).differentiableAt (by simp)
  have hComp := hOuter.hasFDerivAt.comp r hpDeriv.hasFDerivAt
  have hEq : (fun s => f (logHeightBasePoint t s)) =
      upperLift f ∘ p := by
    funext s
    simp only [p, logHeightBasePoint, upperLift, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos, Real.exp_pos]
  rw [hEq, hComp.hasDerivAt.deriv]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one]
  change d1 f z (Complex.I * (Real.exp r : ℂ)) =
    heightC z * dy f z
  rw [d1_complex_decomposition]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero,
    z, heightC, logHeightBasePoint_im]
  ring"""

GAUGE_CONTDIFF = """by
  have hPull : RealSmooth
      (selectedCosetUnitaryPullback q (fixedPhaseEuclideanGauge n u)) :=
    selectedCosetUnitaryPullback_realSmooth q
      (fixedPhaseEuclideanGauge_realSmooth n u)
  have hSlice := RealSmooth.comp_logHeightBasePoint hPull t
  unfold selectedLogHeightNaturalGauge
  have hFactor : ContDiff ℝ 1
      (fun r : ℝ => ((Real.exp (r / 2) : ℝ) : ℂ)) := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp
        (by fun_prop : ContDiff ℝ 1 fun r : ℝ => Real.exp (r / 2))
  exact hFactor.mul (hSlice.of_le (by norm_num))"""

GAUGE_DERIV = """by
  let h : ℍ → ℂ :=
    selectedCosetUnitaryPullback q (fixedPhaseEuclideanGauge n u)
  have hh : RealSmooth h :=
    selectedCosetUnitaryPullback_realSmooth q
      (fixedPhaseEuclideanGauge_realSmooth n u)
  have hExp : HasDerivAt
      (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ))
      (((1 / 2 : ℝ) * Real.exp (r / 2) : ℝ) : ℂ) r := by
    convert (((Real.hasDerivAt_exp (r / 2)).comp r
      ((hasDerivAt_id r).div_const 2)).ofReal_comp) using 1
      <;> simp only [Function.comp_apply, id_eq, div_eq_mul_inv]
      <;> ring
  have hSlice : HasDerivAt
      (fun s => h (logHeightBasePoint t s))
      (heightC (logHeightBasePoint t r) *
        dy h (logHeightBasePoint t r)) r := by
    rw [← deriv_comp_logHeightBasePoint hh t r]
    exact ((RealSmooth.comp_logHeightBasePoint hh t).differentiable
      (by norm_num) r).hasDerivAt
  have hProduct := hExp.mul hSlice
  change deriv
      ((fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ)) *
        (fun s => h (logHeightBasePoint t s))) r = _
  rw [hProduct.deriv]
  ring"""

orig_norm_repairs = fa470.norm_repairs


def norm_repairs(text: str):
    text, repairs = orig_norm_repairs(text)
    variant = os.environ.get("LOG_VARIANT", "direct_one")
    if variant == "surrogate_one":
        text = b.replace_body(
            text, "RealSmooth.comp_logHeightBasePoint", COMP_SURROGATE)
        strategy = "additive_surrogate_then_transfer"
    else:
        text = b.replace_body(
            text, "RealSmooth.comp_logHeightBasePoint", COMP_DIRECT)
        strategy = "explicit_ofReal_contDiff_and_complex_product"
    if variant == "prefix4":
        text = b.replace_body(text, "deriv_comp_logHeightBasePoint", DERIV_LOG)
        text = b.replace_body(
            text, "selectedLogHeightNaturalGauge_contDiff", GAUGE_CONTDIFF)
        text = b.replace_body(
            text, "deriv_selectedLogHeightNaturalGauge", GAUGE_DERIV)
    return text, repairs + [{
        "declaration": "log-height prefix",
        "strategy": f"{variant}:{strategy}",
    }]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
