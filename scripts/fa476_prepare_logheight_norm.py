#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
import re
import sys
from pathlib import Path


ROOT = Path.cwd()
BASE = ROOT / "scripts/fa475_prepare_strict_frontier.py"
spec = importlib.util.spec_from_file_location("fa475base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa475 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa475
spec.loader.exec_module(fa475)

fa466 = fa475.fa466
b = fa475.b
orig_norm_repairs = fa475.norm_repairs


EXACT_FA473_WINNER = "const_add_simp"
EXACT_FA474_WINNER = "explicit_through2791"
EXACT_FA475_WINNER = "clean_semicolon"


NORM_DERIV_BODY = """by
  let z := logHeightBasePoint t r
  let f := fixedPhaseEuclideanGauge n u
  let S := ‖selectedCosetConformalScaleC q z‖
  let F := ‖f (selectedCosetAction q z)‖
  let R := ‖euclideanRaiseGauge n f (selectedCosetAction q z)‖
  let L := ‖euclideanLowerFromSuccGauge (n - 1) f
    (selectedCosetAction q z)‖
  have hPullNorm :
      ‖selectedCosetUnitaryPullback q f z‖ = S * F := by
    rw [selectedCosetUnitaryPullback, norm_mul]
  have hdy := norm_height_mul_dy_selectedCosetUnitaryPullback_le_graph
    n q (fixedPhaseEuclideanGauge_realSmooth n u) z
  rw [deriv_selectedLogHeightNaturalGauge]
  have hOuter :
      ‖((1 / 2 : ℂ) * selectedCosetUnitaryPullback q f z +
          heightC z * dy (selectedCosetUnitaryPullback q f) z)‖ ≤
        S * (logHeightTraceDrift n * F + R + L) := by
    calc
      _ ≤ ‖(1 / 2 : ℂ) * selectedCosetUnitaryPullback q f z‖ +
          ‖heightC z * dy (selectedCosetUnitaryPullback q f) z‖ :=
        norm_add_le _ _
      _ = (1 / 2 : ℝ) * (S * F) +
          ‖heightC z * dy (selectedCosetUnitaryPullback q f) z‖ := by
        rw [norm_mul, hPullNorm]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (S * F) +
          S * ((3 + euclideanHorizontalDrift n / 2) * F + R + L) := by
        gcongr
      _ = S * (logHeightTraceDrift n * F + R + L) := by
        unfold logHeightTraceDrift
        ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (r / 2))]
  exact mul_le_mul_of_nonneg_left hOuter (Real.exp_pos _).le"""


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


def _restore_env(name: str, prior: str | None) -> None:
    if prior is None:
        os.environ.pop(name, None)
    else:
        os.environ[name] = prior


def norm_repairs(text: str):
    fa475_winner = os.environ.get("FA475_WINNER")
    if fa475_winner != EXACT_FA475_WINNER:
        raise RuntimeError(
            "FA476 requires the direct-evidence FA475#2 winner, got "
            f"{fa475_winner!r}"
        )

    prior_fa475 = os.environ.get("FA475_VARIANT")
    os.environ["FA475_VARIANT"] = fa475_winner
    try:
        text, repairs = orig_norm_repairs(text)
    finally:
        _restore_env("FA475_VARIANT", prior_fa475)

    text = replace_body_once(
        text,
        "norm_deriv_selectedLogHeightNaturalGauge_le_graph",
        NORM_DERIV_BODY,
    )
    return text, repairs + [
        {
            "declaration": "norm_deriv_selectedLogHeightNaturalGauge_le_graph",
            "declaration_index": 2792,
            "strategy": (
                "bridge the real norm to abs with Real.norm_eq_abs before "
                "rewriting positivity"
            ),
            "fa475_winner": fa475_winner,
            "frontier_declaration_index": 2792,
            "later_repair_count": 0,
            "max_errors": 32,
        }
    ]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
