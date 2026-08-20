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
EXPECTED_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
EXPECTED_LINES = 60450
AUTHORITATIVE_HEADER = "actualEdgeAmbientParam_hasDerivAt"
TARGET = "compactSupport_height_mul_normSq_le_energy_Ioi"
DECL_RE = re.compile(r"^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)", re.MULTILINE)

spec = importlib.util.spec_from_file_location(
    "fa457_prepare", ROOT / "scripts/fa457_prepare_manual_support_original_ftc.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA457 preparer")
fa457 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa457
spec.loader.exec_module(fa457)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_span(text: str, name: str) -> tuple[int, int]:
    matches = list(DECL_RE.finditer(text))
    for index, match in enumerate(matches):
        if match.group(1) == name:
            end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
            return match.start(), end
    raise RuntimeError(f"declaration not found: {name}")


def declaration_header(text: str, name: str) -> str:
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":= by")
    marker_len = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_len = len(":=")
    if marker < 0:
        raise RuntimeError(f"proof marker not found: {name}")
    return block[:marker + marker_len]


def replace_proof(text: str, name: str, proof: str) -> str:
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":= by")
    if marker < 0:
        raise RuntimeError(f"`:= by` not found: {name}")
    prefix = block[:marker]
    suffix = "\n" if block.endswith("\n") else ""
    return text[:start] + prefix + ":= " + proof.rstrip() + "\n" + suffix + text[end:]


def replace_in_decl(text: str, name: str, old: str, new: str) -> str:
    start, end = declaration_span(text, name)
    block = text[start:end]
    if block.count(old) != 1:
        raise RuntimeError(f"expected one replacement in {name}, found {block.count(old)}")
    return text[:start] + block.replace(old, new, 1) + text[end:]


TARGET_PROOFS = {
    "direct_union": fa457.DIRECT_COMPONENTS,
    "direct_union_explicit": fa457.NORM_SQ_MONO,
    "direct_union_abs": fa457.DIRECT_COMPONENTS.replace(
        "exact mul_nonneg hH0 (sq_nonneg _)",
        "exact mul_nonneg hH0 (by positivity)",
    ),
}

TENDSTO_INTEGRABLE_OLD = """    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact norm_deriv_normSq_le_energy
      (hf.differentiable (by norm_num)) r"""
TENDSTO_INTEGRABLE_NEW = """    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hpoint := norm_deriv_normSq_le_energy
      (hf.differentiable (by norm_num)) r
    have henergyNonneg :
        0 ≤ ‖f r‖ ^ 2 + ‖deriv f r‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg henergyNonneg]
    simpa only [g] using hpoint"""

TENDSTO_CALC_OLD = """  calc
    ‖f r₀‖ ^ 2 = ‖g r₀‖ := by
      simp only [g, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]"""
TENDSTO_CALC_NEW = """  have hgNonneg : 0 ≤ g r₀ := by
    dsimp [g]
    positivity
  calc
    ‖f r₀‖ ^ 2 = g r₀ := rfl
    _ = ‖g r₀‖ := (Real.norm_of_nonneg hgNonneg).symm"""


def apply_cumulative(text: str, variant: str) -> tuple[str, list[dict[str, str]]]:
    repairs: list[dict[str, str]] = []
    text = replace_proof(text, TARGET, TARGET_PROOFS[variant])
    repairs.append({"declaration": TARGET, "strategy": f"manual_support_original_analytic:{variant}"})

    text = replace_in_decl(text, "tendsto_zero_normSq_le_energy_Ioi",
        TENDSTO_INTEGRABLE_OLD, TENDSTO_INTEGRABLE_NEW)
    text = replace_in_decl(text, "tendsto_zero_normSq_le_energy_Ioi",
        TENDSTO_CALC_OLD, TENDSTO_CALC_NEW)
    repairs.append({"declaration": "tendsto_zero_normSq_le_energy_Ioi", "strategy": "normalize_outer_real_norms_and_endpoint_norm"})

    text = replace_in_decl(text, "norm_dy_le_half_raise_lower_base",
        "add_le_add_right (norm_add_le _ _) _",
        "add_le_add (norm_add_le _ _) (le_refl _)")
    repairs.append({"declaration": "norm_dy_le_half_raise_lower_base", "strategy": "explicit_add_le_add"})

    text = replace_in_decl(text, "fixedPhaseEuclideanGauge_lower_pred",
        "  field_simp [hz]\n  ring",
        "  field_simp [hz]\n  ring_nf")
    repairs.append({"declaration": "fixedPhaseEuclideanGauge_lower_pred", "strategy": "ring_nf_after_field_simp"})

    text = replace_in_decl(text, "height_mul_dx_eq_negI_half_raise_sub_lower_sub",
        "  rw [euclideanRaiseGauge_sub_lowerPredGauge]\n  ring",
        "  rw [euclideanRaiseGauge_sub_lowerPredGauge]\n  simp [Complex.I_sq]")
    repairs.append({"declaration": "height_mul_dx_eq_negI_half_raise_sub_lower_sub", "strategy": "normalize_I_sq"})

    text = replace_in_decl(text, "norm_height_mul_dx_le_euclideanGraph",
        "    simp only [c, Complex.norm_real, euclideanHorizontalDrift]",
        "    simp only [c, Complex.norm_real, euclideanHorizontalDrift, Real.norm_eq_abs]")
    text = replace_in_decl(text, "norm_height_mul_dx_le_euclideanGraph",
        "  rw [norm_mul, norm_div, norm_neg, Complex.norm_I, norm_ofNat, one_div]",
        "  rw [norm_mul, norm_div, norm_neg, Complex.norm_I]\n  have hnormTwo : ‖(2 : ℂ)‖ = 2 := by norm_num\n  rw [hnormTwo]")
    repairs.append({"declaration": "norm_height_mul_dx_le_euclideanGraph", "strategy": "canonical_real_norm_and_explicit_complex_norm_two"})
    return text, repairs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=["baseline", "direct_union", "direct_union_explicit", "direct_union_abs"])
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    original = SOURCE.read_bytes()
    if sha256(original) != EXPECTED_SHA:
        raise RuntimeError("baseline source SHA mismatch")
    text = original.decode("utf-8")
    if len(text.splitlines()) != EXPECTED_LINES:
        raise RuntimeError("baseline line count mismatch")

    authoritative_header = declaration_header(text, AUTHORITATIVE_HEADER)
    target_header = declaration_header(text, TARGET)
    original_sequence = [m.group(1) for m in DECL_RE.finditer(text)]
    candidate = text
    repairs: list[dict[str, str]] = []
    if args.variant != "baseline":
        candidate, repairs = apply_cumulative(candidate, args.variant)

    if declaration_header(candidate, AUTHORITATIVE_HEADER) != authoritative_header:
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt statement/header changed")
    if declaration_header(candidate, TARGET) != target_header:
        raise RuntimeError("target statement/header changed")
    candidate_sequence = [m.group(1) for m in DECL_RE.finditer(candidate)]
    if candidate_sequence != original_sequence:
        raise RuntimeError("declaration sequence changed")

    SOURCE.write_text(candidate, encoding="utf-8")
    data = SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "strategy": "baseline" if args.variant == "baseline" else "cumulative_early_analytic",
        "baseline_sha256": EXPECTED_SHA,
        "candidate_sha256": sha256(data),
        "line_count": len(candidate.splitlines()),
        "baseline_line_count": EXPECTED_LINES,
        "target_declaration": AUTHORITATIVE_HEADER,
        "target_header_sha256": sha256(authoritative_header.encode()),
        "compact_header_sha256": sha256(target_header.encode()),
        "declaration_sequence_sha256": sha256(json.dumps(candidate_sequence, separators=(",", ":")).encode()),
        "declaration_count": len(candidate_sequence),
        "repairs": repairs,
    }
    (output / "CANDIDATE.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
