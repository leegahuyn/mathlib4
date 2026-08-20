#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = "61b88982fa79f67da2c01aae2f01a24fab5347be17d3e85e45902d50ef83ae4f"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb10_semantic_round2.py INPUT OUTPUT")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong GB10 R1 bytes: {actual}")
    text = raw.decode()

    text = replace_once(
        text,
        "  have hTotal : Continuous (fun c : ℂ => totalOfBaseScalar x c) := by\n"
        "    simpa only [Function.comp_apply, id_eq] using\n"
        "      totalOfBaseScalar_continuous.comp\n"
        "        (continuous_const.prodMk continuous_id)\n",
        "  have hTotal : Continuous (fun c : ℂ => totalOfBaseScalar x c) := by\n"
        "    convert totalOfBaseScalar_continuous.comp\n"
        "      (continuous_const.prodMk continuous_id) using 1 <;> rfl\n",
        "fibre reconstruction continuity by definitional conversion",
    )

    text = replace_once(
        text,
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  simp [sq_eq_zero_iff]\n",
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, Complex.ofReal_re]\n"
        "  rw [sq_eq_zero_iff, norm_eq_zero]\n",
        "Petersson real-part normalization through ofReal_pow",
    )

    text = replace_once(
        text,
        "/-! ## 2. The explicitly transported atlas on the total space -/\n"
        "/-! ## 2. The explicitly transported atlas on the total space -/\n",
        "/-! ## 2. The explicitly transported atlas on the total space -/\n",
        "deduplicate transported-atlas section marker",
    )

    text = replace_once(
        text,
        "  letI : ChartedSpace (ModelProd ℂ ℂ) InverseEtaTotal :=\n"
        "    ChartedSpace.comp\n"
        "      (ModelProd ℂ ℂ) (InverseEtaBase × ℂ) InverseEtaTotal\n"
        "  rw [extChartAt_comp (I := (𝓘(ℂ).prod 𝓘(ℂ))) u]\n"
        "  simp only [PartialEquiv.trans_target,\n"
        "    Homeomorph.toOpenPartialHomeomorph_target,\n"
        "    preimage_univ, inter_univ]\n",
        "  letI : ChartedSpace (ModelProd ℂ ℂ) InverseEtaTotal :=\n"
        "    inverseEtaTotalTransportedChartedSpace\n"
        "  unfold extChartAt\n"
        "  rw [inverseEtaTotalTransported_chartAt u]\n"
        "  simp only [OpenPartialHomeomorph.extend_target,\n"
        "    PartialEquiv.trans_target,\n"
        "    Homeomorph.toOpenPartialHomeomorph_target,\n"
        "    preimage_univ, inter_univ]\n",
        "transported extChart target via explicit chart formula",
    )

    text = replace_once(
        text,
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp only [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hx]\n"
        "    simpa only [Pi.add_apply] using huv\n"
        "  · simp [globalStageProjectionRepresentative, hx]\n",
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "      ((n : ℝ) + 2) at hx\n"
        "    simp [globalStageProjectionRepresentative, hx]\n"
        "    simpa only [Pi.add_apply] using huv\n"
        "  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "      ((n : ℝ) + 2) at hx\n"
        "    simp [globalStageProjectionRepresentative, hx]\n",
        "projection add membership normalization",
    )

    text = replace_once(
        text,
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp only [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hx]\n"
        "    simpa only [Pi.smul_apply, smul_eq_mul] using hcu\n"
        "  · simp [globalStageProjectionRepresentative, hx]\n",
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "      ((n : ℝ) + 2) at hx\n"
        "    simp [globalStageProjectionRepresentative, hx]\n"
        "    simpa only [Pi.smul_apply, smul_eq_mul] using hcu\n"
        "  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "      ((n : ℝ) + 2) at hx\n"
        "    simp [globalStageProjectionRepresentative, hx]\n",
        "projection smul membership normalization",
    )

    text = replace_once(
        text,
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n"
        "  · simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n",
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "      ((n : ℝ) + 2) at hx\n"
        "    simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n"
        "  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "      ((n : ℝ) + 2) at hx\n"
        "    simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n",
        "projection error density pointwise bound membership normalization",
    )

    text = replace_once(
        text,
        "  filter_upwards [eventually_mem_naturalStageSet x] with n hn\n"
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hn]\n",
        "  filter_upwards [eventually_mem_naturalStageSet x] with n hn\n"
        "  change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "    ((n : ℝ) + 2) at hn\n"
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hn]\n",
        "eventual-zero membership normalization",
    )

    text = replace_once(
        text,
        "  have hx : x ∈ naturalStageSet n :=\n"
        "    naturalStageSet_monotone hn hN\n"
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hx]\n",
        "  have hx : x ∈ naturalStageSet n :=\n"
        "    naturalStageSet_monotone hn hN\n"
        "  change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet\n"
        "    ((n : ℝ) + 2) at hx\n"
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hx]\n",
        "pointwise convergence membership normalization",
    )

    text = replace_once(
        text,
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  norm_num\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,\n"
        "    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]\n",
        "Hamiltonian real-part normalization through ofReal ring map",
    )

    output.write_text(text)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    print(f"candidate_sha256={digest}")


if __name__ == "__main__":
    main()
