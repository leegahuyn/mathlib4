#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = "231efe9a0b8f9d05aae5e65ff3904b3636182ef6f1c93c11eac0c05313730998"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    n = text.count(old)
    if n != 1:
        raise SystemExit(f"{label}: expected one match, found {n}")
    return text.replace(old, new, 1)

PETERS_OLD = """theorem actualStagePeterssonInner_self_re_eq_zero_iff
    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :
    (actualStagePeterssonInner u u).re = 0 ↔ u = 0 := by
  unfold actualStagePeterssonInner
  rw [inner_self_eq_norm_sq_to_K]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [sq_eq_zero_iff, norm_eq_zero]
"""
PETERS_NEW = """theorem actualStagePeterssonInner_self_re_eq_zero_iff
    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :
    (actualStagePeterssonInner u u).re = 0 ↔ u = 0 := by
  unfold actualStagePeterssonInner
  rw [← norm_sq_eq_re_inner, sq_eq_zero_iff, norm_eq_zero]
"""

CHART_OLD = """  simp only [OpenPartialHomeomorph.extend_target,
    PartialEquiv.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ]
"""
CHART_NEW = """  simp only [OpenPartialHomeomorph.extend_target,
    OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ]
"""

ADD_OLD = """theorem globalStageProjection_add
    (n : ℕ) (u v : ActualGlobalQuotientL2) :
    globalStageProjection n (u + v) =
      globalStageProjection n u + globalStageProjection n v := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (u + v),
      globalStageProjection_coeFn_ae n u,
      globalStageProjection_coeFn_ae n v,
      MeasureTheory.Lp.coeFn_add u v,
      MeasureTheory.Lp.coeFn_add
        (globalStageProjection n u) (globalStageProjection n v)]
    with x hsum hu hv huv hout
  rw [hsum, hout, Pi.add_apply, hu, hv]
  by_cases hx : x ∈ naturalStageSet n
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    simp [globalStageProjectionRepresentative, hx]
    simpa only [Pi.add_apply] using huv
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    simp [globalStageProjectionRepresentative, hx]
"""

SMUL_OLD = """theorem globalStageProjection_smul
    (n : ℕ) (c : ℂ) (u : ActualGlobalQuotientL2) :
    globalStageProjection n (c • u) =
      c • globalStageProjection n u := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (c • u),
      globalStageProjection_coeFn_ae n u,
      MeasureTheory.Lp.coeFn_smul c u,
      MeasureTheory.Lp.coeFn_smul c (globalStageProjection n u)]
    with x hleft hu hcu hright
  rw [hleft, hright, Pi.smul_apply, hu]
  by_cases hx : x ∈ naturalStageSet n
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    simp [globalStageProjectionRepresentative, hx]
    simpa only [Pi.smul_apply, smul_eq_mul] using hcu
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    simp [globalStageProjectionRepresentative, hx]
"""

ADD_DIRECT = """theorem globalStageProjection_add
    (n : ℕ) (u v : ActualGlobalQuotientL2) :
    globalStageProjection n (u + v) =
      globalStageProjection n u + globalStageProjection n v := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (u + v),
      globalStageProjection_coeFn_ae n u,
      globalStageProjection_coeFn_ae n v,
      MeasureTheory.Lp.coeFn_add u v,
      MeasureTheory.Lp.coeFn_add
        (globalStageProjection n u) (globalStageProjection n v)]
    with x hsum hu hv huv hout
  by_cases hx : x ∈ naturalStageSet n
  · rw [hsum, hout, Pi.add_apply, hu, hv,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      huv, Pi.add_apply]
  · rw [hsum, hout, Pi.add_apply, hu, hv,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      zero_add]
"""
SMUL_DIRECT = """theorem globalStageProjection_smul
    (n : ℕ) (c : ℂ) (u : ActualGlobalQuotientL2) :
    globalStageProjection n (c • u) =
      c • globalStageProjection n u := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (c • u),
      globalStageProjection_coeFn_ae n u,
      MeasureTheory.Lp.coeFn_smul c u,
      MeasureTheory.Lp.coeFn_smul c (globalStageProjection n u)]
    with x hleft hu hcu hright
  by_cases hx : x ∈ naturalStageSet n
  · rw [hleft, hright,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      hcu, Pi.smul_apply, Pi.smul_apply, hu,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx]
    simp only [smul_eq_mul]
  · rw [hleft, hright,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      Pi.smul_apply, hu,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      smul_zero]
"""

ADD_SIMPA = """theorem globalStageProjection_add
    (n : ℕ) (u v : ActualGlobalQuotientL2) :
    globalStageProjection n (u + v) =
      globalStageProjection n u + globalStageProjection n v := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (u + v),
      globalStageProjection_coeFn_ae n u,
      globalStageProjection_coeFn_ae n v,
      MeasureTheory.Lp.coeFn_add u v,
      MeasureTheory.Lp.coeFn_add
        (globalStageProjection n u) (globalStageProjection n v)]
    with x hsum hu hv huv hout
  rw [hsum, hout, Pi.add_apply, hu, hv]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_mem hx]
    rw [huv, Pi.add_apply]
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      zero_add]
"""
SMUL_SIMPA = """theorem globalStageProjection_smul
    (n : ℕ) (c : ℂ) (u : ActualGlobalQuotientL2) :
    globalStageProjection n (c • u) =
      c • globalStageProjection n u := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (c • u),
      globalStageProjection_coeFn_ae n u,
      MeasureTheory.Lp.coeFn_smul c u,
      MeasureTheory.Lp.coeFn_smul c (globalStageProjection n u)]
    with x hleft hu hcu hright
  rw [hleft, hright, Pi.smul_apply, hu]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_mem hx]
    rw [hcu, Pi.smul_apply]
    simp only [smul_eq_mul]
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      smul_zero]
"""

ADD_TOLP = """theorem globalStageProjection_add
    (n : ℕ) (u v : ActualGlobalQuotientL2) :
    globalStageProjection n (u + v) =
      globalStageProjection n u + globalStageProjection n v := by
  unfold globalStageProjection
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [MeasureTheory.Lp.coeFn_add u v] with x hx
  by_cases hmem : x ∈ naturalStageSet n
  · simp [globalStageProjectionRepresentative, hmem, hx]
  · simp [globalStageProjectionRepresentative, hmem]
"""
SMUL_TOLP = """theorem globalStageProjection_smul
    (n : ℕ) (c : ℂ) (u : ActualGlobalQuotientL2) :
    globalStageProjection n (c • u) =
      c • globalStageProjection n u := by
  unfold globalStageProjection
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [MeasureTheory.Lp.coeFn_smul c u] with x hx
  by_cases hmem : x ∈ naturalStageSet n
  · simp [globalStageProjectionRepresentative, hmem, hx]
  · simp [globalStageProjectionRepresentative, hmem]
"""

ADD_CONVERT = """theorem globalStageProjection_add
    (n : ℕ) (u v : ActualGlobalQuotientL2) :
    globalStageProjection n (u + v) =
      globalStageProjection n u + globalStageProjection n v := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (u + v),
      globalStageProjection_coeFn_ae n u,
      globalStageProjection_coeFn_ae n v,
      MeasureTheory.Lp.coeFn_add u v,
      MeasureTheory.Lp.coeFn_add
        (globalStageProjection n u) (globalStageProjection n v)]
    with x hsum hu hv huv hout
  rw [hsum, hout, Pi.add_apply, hu, hv]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_mem hx]
    convert huv using 1 <;> simp only [Pi.add_apply]
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      zero_add]
"""
SMUL_CONVERT = """theorem globalStageProjection_smul
    (n : ℕ) (c : ℂ) (u : ActualGlobalQuotientL2) :
    globalStageProjection n (c • u) =
      c • globalStageProjection n u := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (c • u),
      globalStageProjection_coeFn_ae n u,
      MeasureTheory.Lp.coeFn_smul c u,
      MeasureTheory.Lp.coeFn_smul c (globalStageProjection n u)]
    with x hleft hu hcu hright
  rw [hleft, hright, Pi.smul_apply, hu]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_mem hx]
    convert hcu using 1 <;> simp only [Pi.smul_apply, smul_eq_mul]
  · simp only [globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      smul_zero]
"""

HAM_OLD = """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
"""
HAM_MANUAL = """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply, map_add, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, inner_self_im,
    mul_zero, zero_mul, sub_zero]
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner]
"""
HAM_SIMP = """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply]
  simp [Complex.mul_re, inner_self_im, ← norm_sq_eq_re_inner]
"""
HAM_CAST = """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  have hcomplex :
      coordinateHamiltonianForm u u =
        ((‖covariantDerivative u‖ ^ 2 +
          (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 : ℝ) : ℂ) := by
    rw [coordinateHamiltonianForm_apply,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hcomplex, Complex.ofReal_re]
"""
HAM_CHANGE = """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply, map_add, Complex.mul_re]
  change
    (inner ℂ (covariantDerivative u) (covariantDerivative u)).re +
      ((1 / 4 : ℝ) *
        (inner ℂ (groundProjection u) (groundProjection u)).re - 0) =
      ‖covariantDerivative u‖ ^ 2 +
        (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner]
  ring
"""

PROJECTIONS = {
    "direct": (ADD_DIRECT, SMUL_DIRECT),
    "simpa": (ADD_SIMPA, SMUL_SIMPA),
    "tolp": (ADD_TOLP, SMUL_TOLP),
    "convert": (ADD_CONVERT, SMUL_CONVERT),
}
HAMS = {
    "manual": HAM_MANUAL,
    "simp": HAM_SIMP,
    "cast": HAM_CAST,
    "change": HAM_CHANGE,
}
VARIANTS = {
    "direct-manual": ("direct", "manual"),
    "direct-cast": ("direct", "cast"),
    "simpa-manual": ("simpa", "manual"),
    "simpa-simp": ("simpa", "simp"),
    "tolp-manual": ("tolp", "manual"),
    "tolp-cast": ("tolp", "cast"),
    "convert-manual": ("convert", "manual"),
    "convert-change": ("convert", "change"),
}


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit("usage: generate.py VARIANT INPUT OUTPUT")
    variant, source_s, output_s = sys.argv[1:]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant}; choices={sorted(VARIANTS)}")
    source = Path(source_s)
    output = Path(output_s)
    raw = source.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != BASE_SHA256:
        raise SystemExit(f"wrong base SHA256: {digest}")
    text = raw.decode()
    text = replace_once(text, PETERS_OLD, PETERS_NEW, "Petersson")
    text = replace_once(text, CHART_OLD, CHART_NEW, "chart")
    proj, ham = VARIANTS[variant]
    add, smul = PROJECTIONS[proj]
    text = replace_once(text, ADD_OLD, add, f"add/{proj}")
    text = replace_once(text, SMUL_OLD, smul, f"smul/{proj}")
    text = replace_once(text, HAM_OLD, HAMS[ham], f"Hamiltonian/{ham}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f"variant={variant}")
    print(f"sha256={hashlib.sha256(output.read_bytes()).hexdigest()}")
    print(f"blob={hashlib.sha1((f'blob {output.stat().st_size}\\0').encode() + output.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
