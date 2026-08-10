#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE_SCRIPT = ROOT / "scripts/fa449_prepare_first_cluster.py"
FA451_SCRIPT = ROOT / "scripts/fa451_prepare_trace_deriv.py"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


COMPACT_COMP_LEFT = """by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      HasCompactSupport.comp_left hcompact.norm
        (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      HasCompactSupport.comp_left hcompact.deriv.norm
        (g := fun x : ℝ => x ^ 2) (by norm_num)
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
    (hweightedSmooth.continuous_deriv_one.norm).integrable_of_hasCompactSupport hweightedCompact.deriv.norm
  have henergyIntegrable : Integrable energy :=
    henergyContinuous.integrable_of_hasCompactSupport henergyCompact
  have hFTC : ‖weighted H‖ ≤
      ∫ y in Set.Ioi H, ‖deriv weighted y‖ := by
    calc
      ‖weighted H‖ = ‖-weighted H‖ := by rw [norm_neg]
      _ = ‖∫ y in Set.Ioi H, deriv weighted y‖ := by
        rw [hweightedCompact.integral_Ioi_deriv_eq
          hweightedSmooth H]
      _ ≤ ∫ y in Set.Ioi H, ‖deriv weighted y‖ :=
        norm_integral_le_integral_norm _
  have hmono :
      (∫ y in Set.Ioi H, ‖deriv weighted y‖) ≤
        ∫ y in Set.Ioi H, energy y := by
    apply setIntegral_mono_on
      hderivWeightedIntegrable.integrableOn
      henergyIntegrable.integrableOn measurableSet_Ioi
    intro y hy
    exact norm_deriv_height_mul_normSq_le (hf.differentiable (by norm_num))
      ((zero_le_one.trans hH).trans (le_of_lt hy))
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  calc
    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by
      simp only [weighted, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hH0, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ∫ y in Set.Ioi H, ‖deriv weighted y‖ := hFTC
    _ ≤ ∫ y in Set.Ioi H, energy y := hmono"""


COMPACT_MONO = """by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      HasCompactSupport.comp_left hcompact.norm
        (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      HasCompactSupport.comp_left hcompact.deriv.norm
        (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hweightedCompact : HasCompactSupport weighted := by
    refine HasCompactSupport.mono hnormSq ?_
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hzero
    apply hy
    simp only [weighted, hzero, mul_zero]
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    refine HasCompactSupport.mono hnormSq ?_
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hzero
    apply hy
    simp only [hzero, mul_zero]
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    refine HasCompactSupport.mono hderivNormSq ?_
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hzero
    apply hy
    simp only [hzero, mul_zero]
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
    (hweightedSmooth.continuous_deriv_one.norm).integrable_of_hasCompactSupport hweightedCompact.deriv.norm
  have henergyIntegrable : Integrable energy :=
    henergyContinuous.integrable_of_hasCompactSupport henergyCompact
  have hFTC : ‖weighted H‖ ≤
      ∫ y in Set.Ioi H, ‖deriv weighted y‖ := by
    calc
      ‖weighted H‖ = ‖-weighted H‖ := by rw [norm_neg]
      _ = ‖∫ y in Set.Ioi H, deriv weighted y‖ := by
        rw [hweightedCompact.integral_Ioi_deriv_eq
          hweightedSmooth H]
      _ ≤ ∫ y in Set.Ioi H, ‖deriv weighted y‖ :=
        norm_integral_le_integral_norm _
  have hmono :
      (∫ y in Set.Ioi H, ‖deriv weighted y‖) ≤
        ∫ y in Set.Ioi H, energy y := by
    apply setIntegral_mono_on
      hderivWeightedIntegrable.integrableOn
      henergyIntegrable.integrableOn measurableSet_Ioi
    intro y hy
    exact norm_deriv_height_mul_normSq_le (hf.differentiable (by norm_num))
      ((zero_le_one.trans hH).trans (le_of_lt hy))
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  calc
    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by
      simp only [weighted, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hH0, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ∫ y in Set.Ioi H, ‖deriv weighted y‖ := hFTC
    _ ≤ ∫ y in Set.Ioi H, energy y := hmono"""


COMPACT_MONO_ABS = COMPACT_MONO.replace(
    """    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by
      simp only [weighted, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hH0, abs_of_nonneg (sq_nonneg _)]""",
    """    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by
      simp only [weighted, Real.norm_eq_abs]
      exact (abs_of_nonneg
        (mul_nonneg hH0 (sq_nonneg (‖f H‖)))).symm""",
)


COMPACT_MONO_DEF_EQ = COMPACT_MONO.replace(
    """    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hzero
    apply hy
    simp only [weighted, hzero, mul_zero]""",
    """    intro y hy hzero
    exact hy (by simp only [weighted, hzero, mul_zero])""",
    1,
).replace(
    """    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hzero
    apply hy
    simp only [hzero, mul_zero]""",
    """    intro y hy hzero
    exact hy (by simp only [hzero, mul_zero])""",
    2,
)


TENDSTO_NORM = """by
  let g : ℝ → ℝ := fun r => ‖f r‖ ^ 2
  have hgSmooth : ContDiff ℝ 1 g := hf.norm_sq ℂ
  have hgDerivMeasurable : AEStronglyMeasurable
      (fun r => ‖deriv g r‖) ((volume : Measure ℝ).restrict (Set.Ioi r₀)) :=
    (hgSmooth.continuous_deriv_one.norm.aestronglyMeasurable).mono_measure Measure.restrict_le_self
  have hgDerivIntegrable : IntegrableOn (fun r => ‖deriv g r‖)
      (Set.Ioi r₀) := by
    apply Integrable.mono henergy hgDerivMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hpoint := norm_deriv_normSq_le_energy
      (hf.differentiable (by norm_num)) r
    change ‖‖deriv g r‖‖ ≤ ‖‖f r‖ ^ 2 + ‖deriv f r‖ ^ 2‖
    rw [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    simpa only [g] using hpoint
  have hgDerivIntegrable' : IntegrableOn (deriv g) (Set.Ioi r₀) := by
    apply (integrable_norm_iff
      ((hgSmooth.continuous_deriv_one.aestronglyMeasurable).mono_measure Measure.restrict_le_self)).mp
    exact hgDerivIntegrable
  have hgzero : Filter.Tendsto g Filter.atTop (nhds 0) := by
    simpa only [g, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hzero.norm.pow 2
  have hFTC : (∫ r in Set.Ioi r₀, deriv g r) = -g r₀ := by
    simpa only [zero_sub] using
      integral_Ioi_of_hasDerivAt_of_tendsto'
        (f := g) (f' := deriv g) (m := 0)
        (fun r _hr =>
          (hgSmooth.differentiable (by norm_num) r).hasDerivAt)
        hgDerivIntegrable' hgzero
  calc
    ‖f r₀‖ ^ 2 = ‖g r₀‖ := by
      rw [show g r₀ = ‖f r₀‖ ^ 2 by rfl, Real.norm_eq_abs]
      exact (abs_of_nonneg (sq_nonneg (‖f r₀‖))).symm
    _ = ‖∫ r in Set.Ioi r₀, deriv g r‖ := by
      rw [hFTC, norm_neg]
    _ ≤ ∫ r in Set.Ioi r₀, ‖deriv g r‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r in Set.Ioi r₀,
        (‖f r‖ ^ 2 + ‖deriv f r‖ ^ 2) := by
      apply setIntegral_mono_on hgDerivIntegrable henergy measurableSet_Ioi
      intro r _hr
      exact norm_deriv_normSq_le_energy
        (hf.differentiable (by norm_num)) r"""


def main() -> None:
    base = load("fa452_base", BASE_SCRIPT)
    fa451 = load("fa452_fa451", FA451_SCRIPT)
    frontier = [
        ("selectedCuspRestrictionRepresentative_add", base.ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", base.MEMLP_EXACT),
        ("coeFn_selectedCuspCoreTrace", base.COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", base.REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", fa451.TRACE_LP_ZERO),
        ("deriv_height_mul_normSq", fa451.DERIV_CHANGE),
        ("norm_deriv_height_mul_normSq_le", fa451.NORM_GCONGR),
    ]
    variants = {
        "baseline": frontier,
        "compact_comp_left": frontier + [
            ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_COMP_LEFT),
        ],
        "compact_comp_left_mono": frontier + [
            ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_MONO),
        ],
        "compact_comp_left_mono_abs": frontier + [
            ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_MONO_ABS),
        ],
        "compact_comp_left_mono_defeq": frontier + [
            ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_MONO_DEF_EQ),
        ],
        "compact_comp_left_mono_abs_tendsto": frontier + [
            ("compactSupport_height_mul_normSq_le_energy_Ioi", COMPACT_MONO_ABS),
            ("tendsto_zero_normSq_le_energy_Ioi", TENDSTO_NORM),
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
        "frontier_sha256": "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb",
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
