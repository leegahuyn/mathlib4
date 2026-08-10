#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path.cwd()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


base = load_module("fa449_base_for_fa452", ROOT / "scripts/fa449_prepare_first_cluster.py")
trace = load_module("fa451_base_for_fa452", ROOT / "scripts/fa451_prepare_trace_deriv.py")

BASE_PATCHES = [
    ("selectedCuspRestrictionRepresentative_add", base.ADD_EXPLICIT),
    ("selectedCuspRestrictionRepresentative_memLp", base.MEMLP_EXACT),
    ("coeFn_selectedCuspCoreTrace", base.COEFN_CHANGE),
    ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", base.REP_ZERO),
]

TRACE_ZERO = [
    ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", trace.TRACE_LP_ZERO),
]
TRACE_ZERO_RW = [
    ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", trace.TRACE_LP_ZERO_RW),
]
DERIV_SIMPA_NORM = [
    ("deriv_height_mul_normSq", trace.DERIV_SIMPA),
    ("norm_deriv_height_mul_normSq_le", trace.NORM_GCONGR),
]
DERIV_CHANGE_NORM = [
    ("deriv_height_mul_normSq", trace.DERIV_CHANGE),
    ("norm_deriv_height_mul_normSq_le", trace.NORM_GCONGR),
]

COMMON_TAIL = r'''
  have henergyCompact : HasCompactSupport energy := by
    exact hfirstCompact.add hsecondCompact
  have hweightedSmooth : ContDiff ℝ 1 weighted := by
    exact contDiff_id.mul (hf.norm_sq ℂ)
  have henergyContinuous : Continuous energy := by
    exact
      (continuous_const.mul (hf.continuous.norm.pow 2)).add
        ((continuous_id.pow 2).mul
          (hf.continuous_deriv_one.norm.pow 2))
  have hderivWeightedIntegrable :
      Integrable (fun y : ℝ => ‖deriv weighted y‖) :=
    (hweightedSmooth.continuous_deriv_one.norm).integrable_of_hasCompactSupport
      hweightedCompact.deriv.norm
  have henergyIntegrable : Integrable energy :=
    henergyContinuous.integrable_of_hasCompactSupport henergyCompact
  have hFTC : ‖weighted H‖ ≤
      ∫ y in Set.Ioi H, ‖deriv weighted y‖ := by
    calc
      ‖weighted H‖ = ‖-weighted H‖ := by rw [norm_neg]
      _ = ‖∫ y in Set.Ioi H, deriv weighted y‖ := by
        rw [hweightedCompact.integral_Ioi_deriv_eq hweightedSmooth H]
      _ ≤ ∫ y in Set.Ioi H, ‖deriv weighted y‖ :=
        norm_integral_le_integral_norm _
  have hmono :
      (∫ y in Set.Ioi H, ‖deriv weighted y‖) ≤
        ∫ y in Set.Ioi H, energy y := by
    apply setIntegral_mono_on
      hderivWeightedIntegrable.integrableOn
      henergyIntegrable.integrableOn measurableSet_Ioi
    intro y hy
    exact norm_deriv_height_mul_normSq_le
      (hf.differentiable (by norm_num))
      ((zero_le_one.trans hH).trans (le_of_lt hy))
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  calc
    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by
      rw [show weighted H = H * ‖f H‖ ^ 2 by rfl,
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hH0 (sq_nonneg _))]
    _ ≤ ∫ y in Set.Ioi H, ‖deriv weighted y‖ := hFTC
    _ ≤ ∫ y in Set.Ioi H, energy y := hmono
'''

COMPACT_POW = """by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    exact hcompact.norm.pow 2
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    exact hcompact.deriv.norm.pow 2
  have hweightedCompact : HasCompactSupport weighted := by
    dsimp [weighted]
    exact hnormSq.mul_left
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    exact hnormSq.mul_left
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    exact hderivNormSq.mul_left
""" + COMMON_TAIL

COMPACT_MULLEFT = """by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using
      hcompact.norm.mul_left (f := fun y : ℝ => ‖f y‖)
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using
      hcompact.deriv.norm.mul_left (f := fun y : ℝ => ‖deriv f y‖)
  have hweightedCompact : HasCompactSupport weighted := by
    simpa only [weighted, Pi.mul_apply] using
      hnormSq.mul_left (f := fun y : ℝ => y)
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    simpa only [Pi.mul_apply] using
      hnormSq.mul_left (f := fun _y : ℝ => (2 : ℝ))
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    simpa only [Pi.mul_apply] using
      hderivNormSq.mul_left (f := fun y : ℝ => y ^ 2)
""" + COMMON_TAIL

COMPACT_CONVERT = """by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    convert hcompact.norm.mul_left (f := fun y : ℝ => ‖f y‖) using 1 <;>
      simp [pow_two, Pi.mul_apply]
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    convert hcompact.deriv.norm.mul_left
      (f := fun y : ℝ => ‖deriv f y‖) using 1 <;>
      simp [pow_two, Pi.mul_apply]
  have hweightedCompact : HasCompactSupport weighted := by
    convert hnormSq.mul_left (f := fun y : ℝ => y) using 1 <;>
      simp [weighted, Pi.mul_apply]
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    convert hnormSq.mul_left (f := fun _y : ℝ => (2 : ℝ)) using 1 <;>
      simp [Pi.mul_apply]
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    convert hderivNormSq.mul_left (f := fun y : ℝ => y ^ 2) using 1 <;>
      simp [Pi.mul_apply]
""" + COMMON_TAIL

COMPACT_MONO = """by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    exact hcompact.norm.pow 2
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    exact hcompact.deriv.norm.pow 2
  have hweightedCompact : HasCompactSupport weighted := by
    exact hnormSq.mul_left
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    exact hnormSq.const_mul 2
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    exact hderivNormSq.mul_left
""" + COMMON_TAIL

VARIANTS = {
    "root_baseline": [],
    "simpa_norm": BASE_PATCHES + TRACE_ZERO + DERIV_SIMPA_NORM,
    "change_norm": BASE_PATCHES + TRACE_ZERO + DERIV_CHANGE_NORM,
    "rw_simpa_norm": BASE_PATCHES + TRACE_ZERO_RW + DERIV_SIMPA_NORM,
    "simpa_norm_compact_pow": BASE_PATCHES + TRACE_ZERO + DERIV_SIMPA_NORM + [
        ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_POW),
    ],
    "change_norm_compact_pow": BASE_PATCHES + TRACE_ZERO + DERIV_CHANGE_NORM + [
        ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_POW),
    ],
    "simpa_norm_compact_mulleft": BASE_PATCHES + TRACE_ZERO + DERIV_SIMPA_NORM + [
        ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_MULLEFT),
    ],
    "simpa_norm_compact_convert": BASE_PATCHES + TRACE_ZERO + DERIV_SIMPA_NORM + [
        ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_CONVERT),
    ],
    "rw_simpa_norm_compact_pow": BASE_PATCHES + TRACE_ZERO_RW + DERIV_SIMPA_NORM + [
        ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_POW),
    ],
    "simpa_norm_compact_mono": BASE_PATCHES + TRACE_ZERO + DERIV_SIMPA_NORM + [
        ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_MONO),
    ],
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
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
    candidate, records = base.apply_many(text, VARIANTS[args.variant])
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
        "baseline_forbidden_counts": base.forbidden_counts(text),
        "candidate_forbidden_counts": base.forbidden_counts(candidate),
        "repairs": records,
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
