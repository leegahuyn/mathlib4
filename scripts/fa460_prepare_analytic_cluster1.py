#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BASE_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
BASE_LINES = 60450

spec = importlib.util.spec_from_file_location(
    "fa459_prepare", ROOT / "scripts/fa459_prepare_true_first_cluster.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA459 preparer")
fa459 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa459
spec.loader.exec_module(fa459)

PROTECTED = [
    "actualEdgeAmbientParam_hasDerivAt",
    "nativeActualEdgeFluxIntegral_paired_circular",
    "nativeActualEdgeFluxIntegral_paired_left",
    "nativeActualEdgeFluxIntegral_paired_right",
    "selectedHalfOpenTile_ae_eq_openTile",
    "integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola",
    "compactSupport_height_mul_normSq_le_energy_Ioi",
    "tendsto_zero_normSq_le_energy_Ioi",
    "selectedCosetConformalScaleC_realSmooth",
    "selectedCosetConformalScaleC_eq_inv_normSq_denom",
    "norm_selectedCosetConformalScaleC_eq_derivative",
    "norm_selectedCosetA_le_scale",
    "norm_selectedCosetB_le_scale",
    "norm_height_mul_dy_selectedCosetConformalScaleC_le",
    "dx_selectedCosetUnitaryPullback",
    "dy_selectedCosetUnitaryPullback",
    "height_mul_dy_selectedCosetUnitaryPullback",
    "norm_height_mul_dy_selectedCosetUnitaryPullback_le",
    "logHeightTraceDrift_nonneg",
    "height_mul_normSq_selectedCuspPulledEuclideanGauge",
    "normSq_selectedCuspRestrictionRepresentative_eq_height_mul_pulled",
    "selectedHorocycleL2_norm_sq_eq_integral",
]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new, 1)


def replace_all_exact(text: str, old: str, new: str, expected: int, label: str) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrences, found {count}")
    return text.replace(old, new)


def body(text: str, name: str, new_body: str) -> str:
    return fa459.replace_body(text, name, new_body)


EQ_INV_CHANGE = """by
  have him := UpperHalfPlane.im_smul_eq_div_normSq
    (gammaTwoCosetRep q) z
  unfold selectedCosetConformalScaleC selectedCosetAction selectedCosetGL
    heightC
  change
    (((Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
        (gammaTwoCosetRep q))) • z).im : ℂ) / (z.im : ℂ) =
      ((1 / Complex.normSq
        (UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL
            ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
              (gammaTwoCosetRep q))) z) : ℝ) : ℂ)
  rw [him]
  simp only [Complex.ofReal_div, Complex.ofReal_one]"""

EQ_INV_LOCAL_EQ = """by
  have him := UpperHalfPlane.im_smul_eq_div_normSq
    (gammaTwoCosetRep q) z
  have haction :
      gammaTwoCosetRep q • z =
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
          (gammaTwoCosetRep q)) • z := by
    rfl
  unfold selectedCosetConformalScaleC selectedCosetAction selectedCosetGL
    heightC
  rw [haction, him]
  simp only [Complex.ofReal_div, Complex.ofReal_one]"""

NORM_DERIV = """by
  have hden := selectedCosetDenom_ne_zero q z
  have hnorm : 0 < ‖selectedCosetDenom q z‖ := norm_pos_iff.mpr hden
  rw [selectedCosetConformalScaleC_eq_inv_normSq_denom]
  change
    ‖((1 / Complex.normSq (selectedCosetDenom q z) : ℝ) : ℂ)‖ =
      ‖1 / selectedCosetDenom q z ^ 2‖
  rw [Complex.norm_real, abs_of_pos (one_div_pos.mpr
    (Complex.normSq_pos.mpr hden)), norm_div, norm_one, norm_pow,
    Complex.normSq_eq_norm_sq]"""

LOG_DRIFT = """by
  unfold logHeightTraceDrift
  have hDrift : 0 ≤ euclideanHorizontalDrift n := by
    unfold euclideanHorizontalDrift
    exact abs_nonneg _
  linarith"""

HOROCYCLE_L2 = """by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) F,
    MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner F F)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t =>
    inner_self_eq_norm_sq (𝕜 := ℂ) (F t)"""


def apply_cluster1(text: str, eq_mode: str) -> tuple[str, list[dict[str, str]]]:
    repairs: list[dict[str, str]] = []

    text = replace_once(
        text,
        "realSmooth_heightC.inv (fun z => heightC_ne_zero z)",
        "RealSmooth.inv realSmooth_heightC (fun z => heightC_ne_zero z)",
        "explicit RealSmooth.inv z",
    )
    text = replace_all_exact(
        text,
        "realSmooth_heightC.inv (fun w => heightC_ne_zero w)",
        "RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)",
        2,
        "explicit RealSmooth.inv w",
    )
    repairs.append({"declaration": "selectedCosetConformalScaleC_realSmooth/dx/dy",
                    "strategy": "fully_qualified_RealSmooth_inv"})

    text = body(
        text,
        "selectedCosetConformalScaleC_eq_inv_normSq_denom",
        EQ_INV_CHANGE if eq_mode == "change" else EQ_INV_LOCAL_EQ,
    )
    repairs.append({"declaration": "selectedCosetConformalScaleC_eq_inv_normSq_denom",
                    "strategy": f"explicit_real_SL_action_{eq_mode}"})

    text = body(text, "norm_selectedCosetConformalScaleC_eq_derivative", NORM_DERIV)
    repairs.append({"declaration": "norm_selectedCosetConformalScaleC_eq_derivative",
                    "strategy": "keep_selectedCosetDenom_folded_before_norm_rewrite"})

    text = replace_all_exact(
        text,
        "simp only [selectedCosetA, Complex.norm_real]",
        "simp only [selectedCosetA, Complex.norm_real, Real.norm_eq_abs]",
        1,
        "selectedCosetA real norm",
    )
    text = replace_all_exact(
        text,
        "simp only [selectedCosetB, Complex.norm_real]",
        "simp only [selectedCosetB, Complex.norm_real, Real.norm_eq_abs]",
        1,
        "selectedCosetB real norm",
    )
    repairs.append({"declaration": "norm_selectedCosetA/B_le_scale",
                    "strategy": "normalize_real_norm_to_abs"})

    text = replace_once(
        text,
        "      exact add_le_add_right (norm_selectedCosetA_le_scale q z) _\n",
        "      simpa [add_comm] using\n        add_le_add_right (norm_selectedCosetA_le_scale q z)\n          ‖selectedCosetConformalScaleC q z‖\n",
        "A scale add order",
    )
    repairs.append({"declaration": "norm_height_mul_dy_selectedCosetConformalScaleC_le",
                    "strategy": "normalize_add_order"})

    text = replace_once(
        text,
        "    dx f (selectedCosetAction q z) +\n            selectedCosetB q z * dy f (selectedCosetAction q z)) := by\n  rw [dx_mul",
        "    dx f (selectedCosetAction q z) +\n            selectedCosetB q z * dy f (selectedCosetAction q z)) := by\n  unfold selectedCosetUnitaryPullback\n  rw [dx_mul",
        "unfold unitary pullback before dx_mul",
    )
    text = replace_once(
        text,
        "    dx f (selectedCosetAction q z) +\n            selectedCosetA q z * dy f (selectedCosetAction q z)) := by\n  rw [dy_mul",
        "    dx f (selectedCosetAction q z) +\n            selectedCosetA q z * dy f (selectedCosetAction q z)) := by\n  unfold selectedCosetUnitaryPullback\n  rw [dy_mul",
        "unfold unitary pullback before dy_mul",
    )
    repairs.append({"declaration": "dx/dy_selectedCosetUnitaryPullback",
                    "strategy": "unfold_definition_before_product_rule"})

    text = replace_once(
        text,
        "  rw [dy_selectedCosetUnitaryPullback q hf,\n    height_mul_dy_selectedCosetConformalScaleC]\n",
        "  rw [dy_selectedCosetUnitaryPullback q hf]\n  rw [mul_add, ← mul_assoc,\n    height_mul_dy_selectedCosetConformalScaleC]\n",
        "associate height times dy scale",
    )
    repairs.append({"declaration": "height_mul_dy_selectedCosetUnitaryPullback",
                    "strategy": "distribute_and_associate_before_scale_rewrite"})

    text = replace_once(
        text,
        "      _ ≤ ‖S‖ + ‖S‖ := add_le_add_right hA _\n",
        "      _ ≤ ‖S‖ + ‖S‖ := by\n        simpa [add_comm] using add_le_add_right hA ‖S‖\n",
        "unitary hAS add order",
    )
    repairs.append({"declaration": "norm_height_mul_dy_selectedCosetUnitaryPullback_le",
                    "strategy": "normalize_add_order"})

    text = body(text, "logHeightTraceDrift_nonneg", LOG_DRIFT)
    repairs.append({"declaration": "logHeightTraceDrift_nonneg",
                    "strategy": "explicit_abs_nonneg_then_linarith"})

    text = replace_once(
        text,
        "        rw [fixedPhaseEuclideanGauge_apply, norm_mul,\n          Complex.norm_real, abs_of_pos (Real.rpow_pos_of_pos hz _)]\n",
        "        rw [fixedPhaseEuclideanGauge_apply, norm_mul,\n          Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz _)]\n",
        "height gauge real norm",
    )
    repairs.append({"declaration": "height_mul_normSq_selectedCuspPulledEuclideanGauge",
                    "strategy": "normalize_real_norm_before_positive_rpow"})

    text = replace_once(
        text,
        "    rw [Complex.norm_real,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t),\n      selectedCuspTraceWeight_sq]\n",
        "    rw [Real.norm_eq_abs,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t),\n      selectedCuspTraceWeight_sq]\n",
        "trace weight real norm",
    )
    repairs.append({"declaration": "normSq_selectedCuspRestrictionRepresentative_eq_height_mul_pulled",
                    "strategy": "normalize_real_norm_to_abs"})

    text = body(text, "selectedHorocycleL2_norm_sq_eq_integral", HOROCYCLE_L2)
    repairs.append({"declaration": "selectedHorocycleL2_norm_sq_eq_integral",
                    "strategy": "explicit_complex_scalar_for_inner_self"})
    return text, repairs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=[
        "baseline",
        "macro_cumulative",
        "macro_cluster1_change",
        "macro_cluster1_localEq",
        "postfix_cluster1_change",
        "postfix_cluster1_localEq",
    ])
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    original = SOURCE.read_bytes()
    if sha(original) != BASE_SHA:
        raise RuntimeError(f"baseline SHA mismatch: {sha(original)} != {BASE_SHA}")
    text = original.decode("utf-8")
    if len(text.splitlines()) != BASE_LINES:
        raise RuntimeError("baseline line count mismatch")

    original_sequence = [m.group(1) for m in fa459.DECL_RE.finditer(text)]
    original_headers = {n: fa459.declaration_header(text, n) for n in PROTECTED}
    candidate = text
    repairs: list[dict[str, str]] = []

    if args.variant != "baseline":
        mode = "postfix" if args.variant.startswith("postfix") else "macro"
        candidate, r = fa459.apply_pair_compat(candidate, mode)
        repairs.append(r)
        candidate, rs = fa459.apply_real_smul_repairs(candidate)
        repairs.extend(rs)
        candidate, rs = fa459.fa458.apply_cumulative(candidate, "direct_union")
        repairs.extend(rs)

    if "cluster1" in args.variant:
        eq_mode = "localEq" if args.variant.endswith("localEq") else "change"
        candidate, rs = apply_cluster1(candidate, eq_mode)
        repairs.extend(rs)

    seq = [m.group(1) for m in fa459.DECL_RE.finditer(candidate)]
    if seq != original_sequence:
        raise RuntimeError("declaration sequence changed")
    for name, old_header in original_headers.items():
        if fa459.declaration_header(candidate, name) != old_header:
            raise RuntimeError(f"theorem/declaration proposition changed: {name}")

    SOURCE.write_text(candidate, encoding="utf-8")
    data = SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "strategy": "analytic_normalization_cluster1",
        "baseline_sha256": BASE_SHA,
        "candidate_sha256": sha(data),
        "line_count": len(candidate.splitlines()),
        "baseline_line_count": BASE_LINES,
        "target_declaration": "actualEdgeAmbientParam_hasDerivAt",
        "target_header_sha256": sha(
            original_headers["actualEdgeAmbientParam_hasDerivAt"].encode()
        ),
        "declaration_sequence_sha256": sha(
            json.dumps(seq, separators=(",", ":")).encode()
        ),
        "declaration_count": len(seq),
        "repairs": repairs,
    }
    (out / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
