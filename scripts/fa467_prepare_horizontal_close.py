#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa466_prepare_selectedscale.py"
spec = importlib.util.spec_from_file_location("fa466base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa466 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa466
spec.loader.exec_module(fa466)

CALC_CLOSE = """by
  rw [euclideanRaiseGauge_sub_lowerPredGauge]
  have hcoef : (-Complex.I / 2) * (2 * Complex.I) = (1 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  calc
    heightC z * dx f z =
        ((-Complex.I / 2) * (2 * Complex.I)) *
          (heightC z * dx f z) := by rw [hcoef]; ring
    _ = (-Complex.I / 2) *
        (2 * Complex.I * heightC z * dx f z +
          ((2 * (euclideanGaugeExponent n + 1) : ℝ) : ℂ) * f z -
          ((2 * (euclideanGaugeExponent n + 1) : ℝ) : ℂ) * f z) := by
      ring"""

CALC_FOUR = """by
  rw [euclideanRaiseGauge_sub_lowerPredGauge]
  have hcoef : (-Complex.I / 2) * (2 * Complex.I) = (1 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  calc
    heightC z * dx f z = 1 * (heightC z * dx f z) := by ring
    _ = ((-Complex.I / 2) * (2 * Complex.I)) *
        (heightC z * dx f z) := by rw [hcoef]
    _ = (-Complex.I / 2) *
        (2 * Complex.I * heightC z * dx f z) := by ring
    _ = (-Complex.I / 2) *
        (2 * Complex.I * heightC z * dx f z +
          ((2 * (euclideanGaugeExponent n + 1) : ℝ) : ℂ) * f z -
          ((2 * (euclideanGaugeExponent n + 1) : ℝ) : ℂ) * f z) := by
      ring"""

RING_I = """by
  rw [euclideanRaiseGauge_sub_lowerPredGauge]
  have hcoef : (-Complex.I / 2) * (2 * Complex.I) = (1 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  conv_lhs => rw [← one_mul (heightC z * dx f z), ← hcoef]
  ring"""

styles = {
    "calc_close": CALC_CLOSE,
    "calc_four": CALC_FOUR,
    "ring_i": RING_I,
}
style = os.environ.get("HORIZONTAL_STYLE", "calc_close")
if style not in styles:
    raise RuntimeError(f"unknown HORIZONTAL_STYLE: {style}")
fa466.b.HORIZONTAL = styles[style]

if __name__ == "__main__":
    fa466.main()
