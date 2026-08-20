#!/usr/bin/env python3
from __future__ import annotations

# Explicit second-push trigger after the workflow file exists on this branch.

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
        raise SystemExit("usage: qym_patch_gb5_semantic_round4.py INPUT OUTPUT")

    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong QYM five-error base bytes: {actual}")
    text = raw.decode()

    text = replace_once(
        text,
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, Complex.ofReal_re]\n"
        "  rw [sq_eq_zero_iff, norm_eq_zero]\n",
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  simp\n",
        "Petersson real-part definiteness",
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
        "transported extChart target",
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
  have hsource :
      (naturalStageSet n).indicator
          ((u + v : ActualGlobalQuotientL2) :
            Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient → ℂ) =ᵐ[
            actualGlobalQuotientMeasure]
        (naturalStageSet n).indicator
          ((u : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient → ℂ) +
            (v : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient → ℂ)) := by
    filter_upwards [MeasureTheory.Lp.coeFn_add u v] with x hx
    by_cases hmem : x ∈ naturalStageSet n
    · simpa only [Set.indicator_of_mem hmem] using hx
    · simp only [Set.indicator_of_notMem hmem]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (u + v),
      globalStageProjection_coeFn_ae n u,
      globalStageProjection_coeFn_ae n v,
      MeasureTheory.Lp.coeFn_add
        (globalStageProjection n u) (globalStageProjection n v),
      hsource]
    with x hsum hu hv hout hsrc
  rw [hsum, hout, Pi.add_apply, hu, hv]
  simp only [globalStageProjectionRepresentative] at hsrc ⊢
  rw [hsrc]
  by_cases hmem : x ∈ naturalStageSet n
  · simp only [Set.indicator_of_mem hmem, Pi.add_apply]
  · simp only [Set.indicator_of_notMem hmem, add_zero]
"""
    text = replace_once(text, old_add, new_add, "projection add via indicator AE transport")

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
  have hsource :
      (naturalStageSet n).indicator
          ((c • u : ActualGlobalQuotientL2) :
            Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient → ℂ) =ᵐ[
            actualGlobalQuotientMeasure]
        (naturalStageSet n).indicator
          (c • (u : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient → ℂ)) := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul c u] with x hx
    by_cases hmem : x ∈ naturalStageSet n
    · simpa only [Set.indicator_of_mem hmem] using hx
    · simp only [Set.indicator_of_notMem hmem]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalStageProjection_coeFn_ae n (c • u),
      globalStageProjection_coeFn_ae n u,
      MeasureTheory.Lp.coeFn_smul c (globalStageProjection n u),
      hsource]
    with x hleft hu hright hsrc
  rw [hleft, hright, Pi.smul_apply, hu]
  simp only [globalStageProjectionRepresentative] at hsrc ⊢
  rw [hsrc]
  by_cases hmem : x ∈ naturalStageSet n
  · simp only [Set.indicator_of_mem hmem, Pi.smul_apply]
  · simp only [Set.indicator_of_notMem hmem, smul_zero]
"""
    text = replace_once(text, old_smul, new_smul, "projection smul via indicator AE transport")

    text = replace_once(
        text,
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,\n"
        "    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n",
        "Hamiltonian real-part normalization",
    )

    output.write_text(text)
    print(f"candidate_sha256={hashlib.sha256(output.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
