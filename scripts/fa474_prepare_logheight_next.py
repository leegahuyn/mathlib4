#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa473_prepare_trace_tail.py"
spec = importlib.util.spec_from_file_location("fa473base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa473 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa473
spec.loader.exec_module(fa473)

fa466 = fa473.fa466
b = fa473.b
orig_norm_repairs = fa473.norm_repairs

GAUGE_CONTDIFF_EXPLICIT = """by
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

GAUGE_CONTDIFF_DIRECT = """by
  have hPull : RealSmooth
      (selectedCosetUnitaryPullback q (fixedPhaseEuclideanGauge n u)) :=
    selectedCosetUnitaryPullback_realSmooth q
      (fixedPhaseEuclideanGauge_realSmooth n u)
  have hSlice := RealSmooth.comp_logHeightBasePoint hPull t
  have hHalf : ContDiff ℝ ∞ (fun r : ℝ => r / 2) :=
    contDiff_id.div_const 2
  have hExpR : ContDiff ℝ ∞ (fun r : ℝ => Real.exp (r / 2)) := by
    simpa only [Function.comp_def] using Real.contDiff_exp.comp hHalf
  have hFactorInf : ContDiff ℝ ∞
      (fun r : ℝ => ((Real.exp (r / 2) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hExpR
  unfold selectedLogHeightNaturalGauge
  exact (hFactorInf.of_le (by norm_num)).mul
    (hSlice.of_le (by norm_num))"""

GAUGE_DERIV_CUMULATIVE = """by
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

FRONTIER_VARIANTS = {
    "const_add_simp",
}

NEXT_VARIANTS = {
    "explicit2790": [
        (
            "selectedLogHeightNaturalGauge_contDiff",
            GAUGE_CONTDIFF_EXPLICIT,
            "explicit Complex.ofRealCLM composition at C1",
        ),
    ],
    "direct2790": [
        (
            "selectedLogHeightNaturalGauge_contDiff",
            GAUGE_CONTDIFF_DIRECT,
            "direct smooth composition of half, exp, and Complex.ofRealCLM",
        ),
    ],
    "explicit_through2791": [
        (
            "selectedLogHeightNaturalGauge_contDiff",
            GAUGE_CONTDIFF_EXPLICIT,
            "explicit Complex.ofRealCLM composition at C1",
        ),
        (
            "deriv_selectedLogHeightNaturalGauge",
            GAUGE_DERIV_CUMULATIVE,
            "typed exponential derivative followed by the log-height chain rule",
        ),
    ],
    "direct_through2791": [
        (
            "selectedLogHeightNaturalGauge_contDiff",
            GAUGE_CONTDIFF_DIRECT,
            "direct smooth composition of half, exp, and Complex.ofRealCLM",
        ),
        (
            "deriv_selectedLogHeightNaturalGauge",
            GAUGE_DERIV_CUMULATIVE,
            "typed exponential derivative followed by the log-height chain rule",
        ),
    ],
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
    replaced = b.replace_body(text, name, body)
    if replaced == text:
        raise RuntimeError(f"body replacement for {name} produced no change")
    return replaced


def norm_repairs(text: str):
    frontier_variant = os.environ.get("FRONTIER_VARIANT")
    if frontier_variant not in FRONTIER_VARIANTS:
        raise RuntimeError(
            f"unsupported or missing FRONTIER_VARIANT={frontier_variant!r}"
        )

    prior_trace_variant = os.environ.get("TRACE_VARIANT")
    os.environ["TRACE_VARIANT"] = frontier_variant
    try:
        text, repairs = orig_norm_repairs(text)
    finally:
        if prior_trace_variant is None:
            os.environ.pop("TRACE_VARIANT", None)
        else:
            os.environ["TRACE_VARIANT"] = prior_trace_variant

    next_variant = os.environ.get("NEXT_VARIANT", "explicit2790")
    if next_variant not in NEXT_VARIANTS:
        raise RuntimeError(f"unsupported NEXT_VARIANT={next_variant!r}")

    added = []
    for declaration, body, strategy in NEXT_VARIANTS[next_variant]:
        text = replace_body_once(text, declaration, body)
        added.append({
            "declaration": declaration,
            "strategy": strategy,
        })
    added.append({
        "declaration": "FA474 next-frontier matrix",
        "strategy": next_variant,
        "matrix_variant": next_variant,
        "fa473_frontier_variant": frontier_variant,
    })
    return text, repairs + added


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
