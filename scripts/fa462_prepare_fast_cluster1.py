#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BASE_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
BASE_LINES = 60450
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)", re.MULTILINE)

spec = importlib.util.spec_from_file_location(
    "fa461_base", ROOT / "scripts/fa461_prepare_gl_analytic_cluster1.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA461 base preparer")
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)

PROTECTED = base.PROTECTED + [
    "dx_selectedCosetConformalScaleC",
    "dy_selectedCosetConformalScaleC",
]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def span(text: str, name: str) -> tuple[int, int]:
    matches = list(DECL_RE.finditer(text))
    for i, m in enumerate(matches):
        if m.group(1) == name:
            return m.start(), matches[i + 1].start() if i + 1 < len(matches) else len(text)
    raise RuntimeError(f"declaration not found: {name}")


def header(text: str, name: str) -> str:
    a, b = span(text, name)
    block = text[a:b]
    p = block.find(":=")
    if p < 0:
        raise RuntimeError(f"assignment not found: {name}")
    return block[: p + 2]


def replace_body(text: str, name: str, proof: str) -> str:
    a, b = span(text, name)
    block = text[a:b]
    p = block.find(":=")
    if p < 0:
        raise RuntimeError(f"assignment not found: {name}")
    suffix = "\n" if block.endswith("\n") else ""
    return text[:a] + block[: p + 2] + " " + proof.rstrip() + "\n" + suffix + text[b:]


def replace_in(text: str, name: str, old: str, new: str) -> str:
    a, b = span(text, name)
    block = text[a:b]
    count = block.count(old)
    if count != 1:
        raise RuntimeError(f"{name}: expected one replacement, found {count}: {old!r}")
    return text[:a] + block.replace(old, new, 1) + text[b:]


SMOOTH_SCALE = """by
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
  exact RealSmooth.mul hnum hdenInv"""

SCALE_EQ_CHANGE = """by
  unfold selectedCosetConformalScaleC heightC
  change
    (((selectedCosetGL q • z).im : ℂ) / (z.im : ℂ)) =
      ((1 / Complex.normSq (UpperHalfPlane.denom (selectedCosetGL q) z) : ℝ) : ℂ)
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp only [selectedCosetGL_det, Int.reduceAbs, one_mul, Complex.ofReal_div,
    Complex.ofReal_one]
  field_simp [z.im_ne_zero]"""

SCALE_EQ_HAVE = """by
  have haction : selectedCosetAction q z = selectedCosetGL q • z := by
    simp [selectedCosetAction, selectedCosetGL]
  have him := UpperHalfPlane.im_smul_eq_div_normSq (selectedCosetGL q) z
  unfold selectedCosetConformalScaleC heightC
  rw [haction, him]
  simp only [selectedCosetGL_det, Int.reduceAbs, one_mul, Complex.ofReal_div,
    Complex.ofReal_one]
  field_simp [z.im_ne_zero]"""

DX_SCALE = """by
  let N : ℍ → ℂ := fun w => heightC (selectedCosetAction q w)
  let Dinv : ℍ → ℂ := fun w => (heightC w)⁻¹
  have hN : RealSmooth N :=
    RealSmooth.comp_selectedCosetAction realSmooth_heightC q
  have hDinv : RealSmooth Dinv :=
    RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)
  have hdxN : dx N z = selectedCosetB q z := by
    simpa only [N, dx_heightC, dy_heightC, mul_zero, mul_one, zero_add] using
      dx_comp_selectedCosetAction q realSmooth_heightC z
  have hdxDinv : dx Dinv z = 0 := by
    change d1 Dinv z 1 = 0
    rw [show d1 Dinv z 1 = -(d1 heightC z 1) / heightC z ^ 2 by
      simpa only [Dinv] using
        d1_inv realSmooth_heightC z 1 (heightC_ne_zero z), d1_heightC]
    simp
  have hfun : selectedCosetConformalScaleC q = N * Dinv := by
    funext w
    simp only [selectedCosetConformalScaleC, N, Dinv, Pi.mul_apply, div_eq_mul_inv]
  rw [hfun, dx_mul hN hDinv, hdxN, hdxDinv]
  simp only [mul_zero, add_zero, Dinv, div_eq_mul_inv]"""

DY_SCALE = """by
  let N : ℍ → ℂ := fun w => heightC (selectedCosetAction q w)
  let Dinv : ℍ → ℂ := fun w => (heightC w)⁻¹
  have hN : RealSmooth N :=
    RealSmooth.comp_selectedCosetAction realSmooth_heightC q
  have hDinv : RealSmooth Dinv :=
    RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)
  have hdyN : dy N z = selectedCosetA q z := by
    simpa only [N, dx_heightC, dy_heightC, mul_zero, mul_one, add_zero, zero_add] using
      dy_comp_selectedCosetAction q realSmooth_heightC z
  have hdyDinv : dy Dinv z = -(1 / heightC z ^ 2) := by
    change d1 Dinv z Complex.I = _
    rw [show d1 Dinv z Complex.I =
        -(d1 heightC z Complex.I) / heightC z ^ 2 by
      simpa only [Dinv] using
        d1_inv realSmooth_heightC z Complex.I (heightC_ne_zero z), d1_heightC]
    field_simp [heightC_ne_zero z]
    simp only [Complex.I_im]
  have hfun : selectedCosetConformalScaleC q = N * Dinv := by
    funext w
    simp only [selectedCosetConformalScaleC, N, Dinv, Pi.mul_apply, div_eq_mul_inv]
  rw [hfun, dy_mul hN hDinv, hdyN, hdyDinv]
  simp only [Dinv, N, div_eq_mul_inv]
  have hz : heightC z ≠ 0 := heightC_ne_zero z
  field_simp [hz]
  ring"""

NORM_DERIV = """by
  have hden := selectedCosetDenom_ne_zero q z
  rw [selectedCosetConformalScaleC_eq_inv_normSq_denom]
  unfold selectedCosetDerivative
  change
    ‖(1 / Complex.normSq (selectedCosetDenom q z) : ℝ)‖ =
      ‖1 / selectedCosetDenom q z ^ 2‖
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr
    (Complex.normSq_pos.mpr hden)), norm_div, norm_one, norm_pow,
    Complex.normSq_eq_norm_sq]"""

DX_PULL = """by
  unfold selectedCosetUnitaryPullback
  change dx
      (selectedCosetConformalScaleC q *
        (fun w => f (selectedCosetAction q w))) z = _
  rw [dx_mul (selectedCosetConformalScaleC_realSmooth q)
    (RealSmooth.comp_selectedCosetAction hf q),
    dx_comp_selectedCosetAction q hf]"""

DY_PULL = """by
  unfold selectedCosetUnitaryPullback
  change dy
      (selectedCosetConformalScaleC q *
        (fun w => f (selectedCosetAction q w))) z = _
  rw [dy_mul (selectedCosetConformalScaleC_realSmooth q)
    (RealSmooth.comp_selectedCosetAction hf q),
    dy_comp_selectedCosetAction q hf]"""

HEIGHT_DY_PULL = """by
  rw [dy_selectedCosetUnitaryPullback q hf]
  rw [mul_add]
  calc
    _ = (heightC z * dy (selectedCosetConformalScaleC q) z) *
          f (selectedCosetAction q z) +
        (heightC z * selectedCosetConformalScaleC q z) *
          (-selectedCosetB q z * dx f (selectedCosetAction q z) +
            selectedCosetA q z * dy f (selectedCosetAction q z)) := by ring
    _ = (selectedCosetA q z - selectedCosetConformalScaleC q z) *
          f (selectedCosetAction q z) +
        heightC (selectedCosetAction q z) *
          (-selectedCosetB q z * dx f (selectedCosetAction q z) +
            selectedCosetA q z * dy f (selectedCosetAction q z)) := by
      rw [height_mul_dy_selectedCosetConformalScaleC]
      unfold selectedCosetConformalScaleC
      rw [mul_div_cancel₀ _ (heightC_ne_zero z)]
    _ = _ := by ring"""

LOG_DRIFT = """by
  unfold logHeightTraceDrift
  have hDrift : 0 ≤ euclideanHorizontalDrift n := euclideanHorizontalDrift_nonneg n
  linarith"""

L2_NORM = """by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) F,
    MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner F F)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t =>
    inner_self_eq_norm_sq (𝕜 := ℂ) (F t)"""


def apply_cluster(text: str, scale_mode: str) -> tuple[str, list[dict[str, str]]]:
    repairs: list[dict[str, str]] = []
    text = replace_body(text, "selectedCosetConformalScaleC_realSmooth", SMOOTH_SCALE)
    text = replace_body(text, "selectedCosetConformalScaleC_eq_inv_normSq_denom",
                        SCALE_EQ_HAVE if scale_mode == "have" else SCALE_EQ_CHANGE)
    text = replace_body(text, "dx_selectedCosetConformalScaleC", DX_SCALE)
    text = replace_body(text, "dy_selectedCosetConformalScaleC", DY_SCALE)
    text = replace_body(text, "norm_selectedCosetConformalScaleC_eq_derivative", NORM_DERIV)
    repairs += [
        {"declaration": "selectedCosetConformalScaleC_realSmooth", "strategy": "explicit_RealSmooth_mul"},
        {"declaration": "selectedCosetConformalScaleC_eq_inv_normSq_denom", "strategy": f"GL_im_formula_{scale_mode}"},
        {"declaration": "dx/dy_selectedCosetConformalScaleC", "strategy": "qualified_RealSmooth_inv"},
        {"declaration": "norm_selectedCosetConformalScaleC_eq_derivative", "strategy": "real_norm_after_folded_denom"},
    ]
    text = replace_in(text, "norm_selectedCosetA_le_scale",
        "simp only [selectedCosetA, Complex.norm_real]",
        "simp only [selectedCosetA, Complex.norm_real, Real.norm_eq_abs]")
    text = replace_in(text, "norm_selectedCosetB_le_scale",
        "simp only [selectedCosetB, Complex.norm_real]",
        "simp only [selectedCosetB, Complex.norm_real, Real.norm_eq_abs]")
    text = replace_in(text, "norm_height_mul_dy_selectedCosetConformalScaleC_le",
        "exact add_le_add_right (norm_selectedCosetA_le_scale q z) _",
        "exact add_le_add (norm_selectedCosetA_le_scale q z) (le_refl _)")
    text = replace_body(text, "dx_selectedCosetUnitaryPullback", DX_PULL)
    text = replace_body(text, "dy_selectedCosetUnitaryPullback", DY_PULL)
    text = replace_body(text, "height_mul_dy_selectedCosetUnitaryPullback", HEIGHT_DY_PULL)
    text = replace_in(text, "norm_height_mul_dy_selectedCosetUnitaryPullback_le",
        "_ ≤ ‖S‖ + ‖S‖ := add_le_add_right hA _",
        "_ ≤ ‖S‖ + ‖S‖ := add_le_add hA (le_refl _)")
    text = replace_body(text, "logHeightTraceDrift_nonneg", LOG_DRIFT)
    text = replace_in(text, "height_mul_normSq_selectedCuspPulledEuclideanGauge",
        "Complex.norm_real, abs_of_pos (Real.rpow_pos_of_pos hz _)",
        "Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz _)")
    text = replace_in(text, "normSq_selectedCuspRestrictionRepresentative_eq_height_mul_pulled",
        "Complex.norm_real,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t)",
        "Complex.norm_real, Real.norm_eq_abs,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t)")
    text = replace_body(text, "selectedHorocycleL2_norm_sq_eq_integral", L2_NORM)
    repairs += [
        {"declaration": "selectedCoset norm/unitary cluster", "strategy": "typed_norm_and_pointwise_product_normalization"},
        {"declaration": "selected cusp norm/L2 cluster", "strategy": "complex_real_norm_and_explicit_inner_scalar"},
    ]
    return text, repairs


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--variant", required=True, choices=[
        "baseline", "gl_cumulative", "gl_algA", "gl_cluster_change", "gl_cluster_have"])
    p.add_argument("--output-dir", required=True)
    args = p.parse_args()
    out = Path(args.output_dir); out.mkdir(parents=True, exist_ok=True)
    raw = SOURCE.read_bytes()
    if sha(raw) != BASE_SHA:
        raise RuntimeError(f"baseline SHA mismatch: {sha(raw)} != {BASE_SHA}")
    text = raw.decode("utf-8")
    if len(text.splitlines()) != BASE_LINES:
        raise RuntimeError("baseline line count mismatch")
    seq = [m.group(1) for m in DECL_RE.finditer(text)]
    headers = {n: header(text, n) for n in dict.fromkeys(PROTECTED)}
    cand = text; repairs: list[dict[str, str]] = []
    if args.variant != "baseline":
        cand, rs = base.apply_gl_pair_cumulative(cand); repairs += rs
    if args.variant in {"gl_algA", "gl_cluster_change", "gl_cluster_have"}:
        cand, rs = base.apply_algebra(cand, "A"); repairs += rs
    if args.variant in {"gl_cluster_change", "gl_cluster_have"}:
        cand, rs = apply_cluster(cand, "have" if args.variant.endswith("have") else "change")
        repairs += rs
    cseq = [m.group(1) for m in DECL_RE.finditer(cand)]
    if cseq != seq:
        raise RuntimeError("declaration sequence changed")
    for n, h in headers.items():
        if header(cand, n) != h:
            raise RuntimeError(f"declaration proposition changed: {n}")
    SOURCE.write_text(cand, encoding="utf-8")
    data = SOURCE.read_bytes()
    meta = {
        "variant": args.variant,
        "strategy": "fast_firsterror_cluster1",
        "baseline_sha256": BASE_SHA,
        "candidate_sha256": sha(data),
        "line_count": len(cand.splitlines()),
        "baseline_line_count": BASE_LINES,
        "target_declaration": "actualEdgeAmbientParam_hasDerivAt",
        "target_header_sha256": sha(headers["actualEdgeAmbientParam_hasDerivAt"].encode()),
        "declaration_sequence_sha256": sha(json.dumps(cseq, separators=(",", ":")).encode()),
        "declaration_count": len(cseq),
        "repairs": repairs,
    }
    (out / "CANDIDATE.json").write_text(json.dumps(meta, indent=2, ensure_ascii=False) + "\n")
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(meta, indent=2, ensure_ascii=False))

if __name__ == "__main__":
    main()
