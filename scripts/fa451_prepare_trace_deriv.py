#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE_SCRIPT = ROOT / "scripts/fa449_prepare_first_cluster.py"


def load_base():
    spec = importlib.util.spec_from_file_location("fa449_base", BASE_SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load FA449 generator")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


TRACE_LP_ZERO = """by
  rcases fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero n u with
    ⟨Y₀, hY₀, hZero⟩
  refine ⟨Y₀, hY₀, ?_⟩
  intro Z hYZ q
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_selectedCuspCoreTrace n q Z u,
    hZero Z hYZ q,
    MeasureTheory.Lp.coeFn_zero ℂ 2 selectedHorocycleParameterMeasure]
    with t htrace hrep hzero
  exact htrace.trans (hrep.trans hzero.symm)"""

TRACE_LP_ZERO_RW = """by
  rcases fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero n u with
    ⟨Y₀, hY₀, hZero⟩
  refine ⟨Y₀, hY₀, ?_⟩
  intro Z hYZ q
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_selectedCuspCoreTrace n q Z u,
    hZero Z hYZ q,
    MeasureTheory.Lp.coeFn_zero ℂ 2 selectedHorocycleParameterMeasure]
    with t htrace hrep hzero
  rw [htrace, hrep, hzero]"""

DERIV_CHANGE = """by
  have hnorm := (hf y).hasDerivAt.norm_sq
  have hprod := (hasDerivAt_id y).mul hnorm
  change deriv (id * fun x : ℝ => ‖f x‖ ^ 2) y = _
  rw [hprod.deriv]
  simp only [id_eq, one_mul]
  ring"""

DERIV_SIMPA = """by
  have hnorm := (hf y).hasDerivAt.norm_sq
  have hprod : HasDerivAt (fun r : ℝ => r * ‖f r‖ ^ 2)
      (1 * ‖f y‖ ^ 2 + y * (2 * ⟪f y, deriv f y⟫_ℝ)) y := by
    simpa only [Pi.mul_apply, id_eq] using (hasDerivAt_id y).mul hnorm
  rw [hprod.deriv]
  ring"""

NORM_GCONGR = """by
  rw [deriv_height_mul_normSq hf y, Real.norm_eq_abs]
  have hinner : |⟪f y, deriv f y⟫_ℝ| ≤
      ‖f y‖ * ‖deriv f y‖ :=
    abs_real_inner_le_norm _ _
  calc
    |‖f y‖ ^ 2 + 2 * y * ⟪f y, deriv f y⟫_ℝ| ≤
        |‖f y‖ ^ 2| + |2 * y * ⟪f y, deriv f y⟫_ℝ| :=
      abs_add_le _ _
    _ = ‖f y‖ ^ 2 + (2 * y) * |⟪f y, deriv f y⟫_ℝ| := by
      rw [abs_of_nonneg (sq_nonneg _), abs_mul,
        abs_of_nonneg (mul_nonneg (by norm_num) hy)]
    _ ≤ ‖f y‖ ^ 2 + (2 * y) *
        (‖f y‖ * ‖deriv f y‖) := by
      gcongr
    _ ≤ 2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f y‖ - y * ‖deriv f y‖)]"""

BASE_PATCHES = None


def main() -> None:
    base = load_base()
    global BASE_PATCHES
    BASE_PATCHES = [
        ("selectedCuspRestrictionRepresentative_add", base.ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", base.MEMLP_EXACT),
        ("coeFn_selectedCuspCoreTrace", base.COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", base.REP_ZERO),
    ]
    variants = {
        "known_before_trace": BASE_PATCHES,
        "trace_lpz": BASE_PATCHES + [
            ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_LP_ZERO),
        ],
        "trace_lpz_rw": BASE_PATCHES + [
            ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_LP_ZERO_RW),
        ],
        "trace_deriv_change": BASE_PATCHES + [
            ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_LP_ZERO),
            ("deriv_height_mul_normSq", DERIV_CHANGE),
        ],
        "trace_deriv_simpa": BASE_PATCHES + [
            ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_LP_ZERO),
            ("deriv_height_mul_normSq", DERIV_SIMPA),
        ],
        "trace_deriv_change_norm": BASE_PATCHES + [
            ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_LP_ZERO),
            ("deriv_height_mul_normSq", DERIV_CHANGE),
            ("norm_deriv_height_mul_normSq_le", NORM_GCONGR),
        ],
        "trace_deriv_simpa_norm": BASE_PATCHES + [
            ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_LP_ZERO),
            ("deriv_height_mul_normSq", DERIV_SIMPA),
            ("norm_deriv_height_mul_normSq_le", NORM_GCONGR),
        ],
    }
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(variants))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)

    original = base.SOURCE.read_bytes()
    actual_sha = base.sha256(original)
    if actual_sha != base.EXPECTED_SHA:
        raise RuntimeError(f"source SHA mismatch: {actual_sha} != {base.EXPECTED_SHA}")
    text = original.decode("utf-8")
    original_header = base.declaration_header(text, base.TARGET_HEADER)
    original_sequence = [m.group(1) for m in base.DECL_RE.finditer(text)]
    candidate, records = base.apply_many(text, variants[args.variant])
    if base.declaration_header(candidate, base.TARGET_HEADER) != original_header:
        raise RuntimeError("authoritative theorem header changed")
    candidate_sequence = [m.group(1) for m in base.DECL_RE.finditer(candidate)]
    if candidate_sequence != original_sequence:
        raise RuntimeError("declaration sequence changed")
    base.SOURCE.write_text(candidate, encoding="utf-8")
    data = base.SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "baseline_sha256": base.EXPECTED_SHA,
        "candidate_sha256": base.sha256(data),
        "line_count": len(candidate.splitlines()),
        "baseline_line_count": len(text.splitlines()),
        "target_header_sha256": base.sha256(original_header.encode()),
        "declaration_sequence_sha256": base.sha256(
            json.dumps(candidate_sequence, separators=(",", ":")).encode()
        ),
        "declaration_count": len(candidate_sequence),
        "repairs": records,
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
