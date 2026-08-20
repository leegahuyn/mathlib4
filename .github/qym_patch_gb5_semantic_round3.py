#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = "231efe9a0b8f9d05aae5e65ff3904b3636182ef6f1c93c11eac0c05313730998"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb5_semantic_round3.py INPUT OUTPUT")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong QYM 5-error base bytes: {actual}")
    text = raw.decode()

    text = replace_once(
        text,
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, Complex.ofReal_re]\n"
        "  rw [sq_eq_zero_iff, norm_eq_zero]\n",
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  rw [Complex.ofReal_pow, Complex.ofReal_re]\n"
        "  simp only [sq_eq_zero_iff, norm_eq_zero]\n",
        "Petersson real-part normalization in the forward direction",
    )

    text = replace_once(
        text,
        "  simp only [OpenPartialHomeomorph.extend_target,\n"
        "    PartialEquiv.trans_target,\n"
        "    Homeomorph.toOpenPartialHomeomorph_target,\n"
        "    preimage_univ, inter_univ]\n",
        "  simp only [OpenPartialHomeomorph.extend_target,\n"
        "    OpenPartialHomeomorph.trans_target,\n"
        "    Homeomorph.toOpenPartialHomeomorph_target,\n"
        "    preimage_univ, inter_univ]\n",
        "transported extChart target through open partial homeomorph composition",
    )

    old_add = """theorem globalStageProjection_add
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
    new_add = """theorem globalStageProjection_add
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
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [hsum, hout, Pi.add_apply, hu, hv,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      huv, Pi.add_apply]
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [hsum, hout, Pi.add_apply, hu, hv,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      zero_add]
"""
    text = replace_once(text, old_add, new_add, "projection add by direct representative rewrites")

    old_smul = """theorem globalStageProjection_smul
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
    new_smul = """theorem globalStageProjection_smul
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
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [hleft, hright,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      hcu, Pi.smul_apply, Pi.smul_apply, hu,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx]
    simp only [smul_eq_mul]
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [hleft, hright,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      Pi.smul_apply, hu,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      smul_zero]
"""
    text = replace_once(text, old_smul, new_smul, "projection smul by direct representative rewrites")

    text = replace_once(
        text,
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,\n"
        "    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp only [Complex.ofReal_pow, Complex.ofReal_mul,\n"
        "    Complex.ofReal_add, Complex.ofReal_re]\n",
        "Hamiltonian real-part normalization in the forward direction",
    )

    output.write_text(text)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    print(f"candidate_sha256={digest}")


if __name__ == "__main__":
    main()
