#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
import re
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
orig_norm_repairs = fa471.norm_repairs

DERIV_EXP_MUL_I = """by
  let p : ℝ → ℂ := fun s => Complex.mk t (Real.exp s)
  let z : ℍ := logHeightBasePoint t r
  have hpDeriv : HasDerivAt p
      ((Real.exp r : ℂ) * Complex.I) r := by
    have hExp := (Real.hasDerivAt_exp r).ofReal_comp
    have hIm := hExp.mul_const Complex.I
    have hRe := hasDerivAt_const r (t : ℂ)
    simpa only [p, Complex.mk_eq_add_mul_I, Pi.add_apply, zero_add] using
      hRe.add hIm
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
  change d1 f z ((Real.exp r : ℂ) * Complex.I) =
    heightC z * dy f z
  rw [d1_complex_decomposition]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    mul_one, add_zero, zero_add, sub_zero, z, heightC,
    logHeightBasePoint_im]
  ring"""

DERIV_CONVERT_RING_NF = """by
  let p : ℝ → ℂ := fun s => Complex.mk t (Real.exp s)
  let z : ℍ := logHeightBasePoint t r
  have hpDeriv : HasDerivAt p
      (Complex.I * (Real.exp r : ℂ)) r := by
    have hExp := (Real.hasDerivAt_exp r).ofReal_comp
    have hIm := hExp.mul_const Complex.I
    have hRe := hasDerivAt_const r (t : ℂ)
    convert hRe.add hIm using 1 <;>
      simp only [p, Complex.mk_eq_add_mul_I, Pi.add_apply, zero_add] <;>
      ring_nf
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
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    mul_one, add_zero, zero_add, sub_zero, z, heightC,
    logHeightBasePoint_im]
  ring"""

DERIV_CONST_ADD = """by
  let p : ℝ → ℂ := fun s => Complex.mk t (Real.exp s)
  let z : ℍ := logHeightBasePoint t r
  have hpDeriv : HasDerivAt p
      ((Real.exp r : ℂ) * Complex.I) r := by
    have hExp := (Real.hasDerivAt_exp r).ofReal_comp
    have hIm := hExp.mul_const Complex.I
    simpa only [p, Complex.mk_eq_add_mul_I] using
      hIm.const_add (t : ℂ)
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
  change d1 f z ((Real.exp r : ℂ) * Complex.I) =
    heightC z * dy f z
  rw [d1_complex_decomposition]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    mul_one, add_zero, zero_add, sub_zero, z, heightC,
    logHeightBasePoint_im]
  ring"""

DERIV_CONST_ADD_SIMP = DERIV_CONST_ADD.replace(
    """  rw [d1_complex_decomposition]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    mul_one, add_zero, zero_add, sub_zero, z, heightC,
    logHeightBasePoint_im]
  ring""",
    """  rw [d1_complex_decomposition]
  simp [Complex.mul_re, Complex.mul_im, z, heightC,
    logHeightBasePoint_im]""",
)

DERIV_CONST_ADD_NORM = DERIV_CONST_ADD.replace(
    """  ring""",
    """  norm_num <;> ring""",
)

DERIV_CONST_ADD_MAP_ZERO = DERIV_CONST_ADD.replace(
    """    logHeightBasePoint_im]
  ring""",
    """    logHeightBasePoint_im, map_zero]
  ring""",
)

if DERIV_CONST_ADD_SIMP == DERIV_CONST_ADD:
    raise RuntimeError("const_add simp candidate did not change")
if DERIV_CONST_ADD_NORM == DERIV_CONST_ADD:
    raise RuntimeError("const_add norm candidate did not change")
if DERIV_CONST_ADD_MAP_ZERO == DERIV_CONST_ADD:
    raise RuntimeError("const_add map_zero candidate did not change")

VARIANTS = {
    "const_add_simp": (
        DERIV_CONST_ADD_SIMP,
        "const_add followed by unrestricted simplification of the zero real coercion",
    ),
    "const_add_norm": (
        DERIV_CONST_ADD_NORM,
        "const_add followed by norm_num normalization of the zero real coercion",
    ),
    "const_add_map_zero": (
        DERIV_CONST_ADD_MAP_ZERO,
        "const_add with map_zero included in the final restricted simplifier",
    ),
}


def replace_body_once(text: str, name: str, body: str) -> str:
    pattern = re.compile(
        rf"^(?:(?:protected|private|noncomputable)\s+)*"
        rf"(?:theorem|lemma|def|abbrev)\s+{re.escape(name)}(?=[\s(:])",
        re.MULTILINE,
    )
    count = len(pattern.findall(text))
    if count != 1:
        raise RuntimeError(
            f"expected exactly one declaration header for {name}, found {count}"
        )
    return b.replace_body(text, name, body)


def norm_repairs(text: str):
    prior_log_variant = os.environ.get("LOG_VARIANT")
    os.environ["LOG_VARIANT"] = "direct_one"
    try:
        text, repairs = orig_norm_repairs(text)
    finally:
        if prior_log_variant is None:
            os.environ.pop("LOG_VARIANT", None)
        else:
            os.environ["LOG_VARIANT"] = prior_log_variant

    variant = os.environ.get("TRACE_VARIANT", "const_add_simp")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported TRACE_VARIANT={variant!r}")
    body, strategy = VARIANTS[variant]
    text = replace_body_once(text, "deriv_comp_logHeightBasePoint", body)
    return text, repairs + [
        {
            "declaration": "deriv_comp_logHeightBasePoint",
            "strategy": strategy,
        },
        {
            "declaration": "FA473 strict-frontier matrix",
            "strategy": variant,
            "matrix_variant": variant,
            "fa471_log_variant": "direct_one",
        },
    ]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
