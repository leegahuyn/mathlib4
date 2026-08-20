#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
EXPECTED_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
EXPECTED_LINES = 60450
AUTHORITATIVE_HEADER = "actualEdgeAmbientParam_hasDerivAt"
TARGET = "compactSupport_height_mul_normSq_le_energy_Ioi"
DECL_RE = re.compile(r"^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)", re.MULTILINE)

COMMON_ANALYTIC = r"""  have henergyCompact : HasCompactSupport energy := by
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
  have hweightedNonneg : 0 ≤ weighted H := by
    dsimp [weighted]
    exact mul_nonneg hH0 (sq_nonneg _)
  calc
    H * ‖f H‖ ^ 2 = weighted H := rfl
    _ = ‖weighted H‖ := (Real.norm_of_nonneg hweightedNonneg).symm
    _ ≤ ∫ y in Set.Ioi H, ‖deriv weighted y‖ := hFTC
    _ ≤ ∫ y in Set.Ioi H, energy y := hmono"""

DIRECT_COMPONENTS = r"""by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hweightedCompact : HasCompactSupport weighted := by
    change HasCompactSupport (fun y : ℝ => y * ‖f y‖ ^ 2)
    exact hcompact.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hfy
      apply hy
      simp [hfy])
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    exact hcompact.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hfy
      apply hy
      simp [hfy])
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    exact hcompact.deriv.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hdfy
      apply hy
      simp [hdfy])
""" + COMMON_ANALYTIC

NORM_SQ_MONO = r"""by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    exact hcompact.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hfy
      apply hy
      simp [hfy])
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    exact hcompact.deriv.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hdfy
      apply hy
      simp [hdfy])
  have hweightedCompact : HasCompactSupport weighted := by
    exact hnormSq.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hsq
      apply hy
      simp [weighted, hsq])
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    exact hnormSq.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hsq
      apply hy
      simp [hsq])
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    exact hderivNormSq.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hsq
      apply hy
      simp [hsq])
""" + COMMON_ANALYTIC

UNION_ENERGY = r"""by
  let weighted : ℝ → ℝ := fun y => y * ‖f y‖ ^ 2
  let energy : ℝ → ℝ := fun y =>
    2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2
  have hweightedCompact : HasCompactSupport weighted := by
    change HasCompactSupport (fun y : ℝ => y * ‖f y‖ ^ 2)
    exact hcompact.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hfy
      apply hy
      simp [hfy])
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    exact hcompact.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hfy
      apply hy
      simp [hfy])
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    exact hcompact.deriv.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hdfy
      apply hy
      simp [hdfy])
""" + COMMON_ANALYTIC

VARIANTS = {
    "baseline": (None, "baseline"),
    "direct_union": (DIRECT_COMPONENTS, "direct_support_components_original_analytic"),
    "direct_union_explicit": (NORM_SQ_MONO, "normSq_then_mono_original_analytic"),
    "direct_union_abs": (UNION_ENERGY, "direct_support_components_original_analytic_alt"),
}


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
        raise RuntimeError(f"proof marker not found in {name}")
    return block[:marker + marker_len]


def replace_proof(text: str, name: str, proof: str) -> tuple[str, dict[str, str]]:
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":= by")
    if marker < 0:
        raise RuntimeError(f"`:= by` not found in {name}")
    prefix = block[:marker]
    suffix = "\n" if block.endswith("\n") else ""
    replacement = prefix + ":= " + proof.rstrip() + "\n" + suffix
    return text[:start] + replacement + text[end:], {
        "declaration": name,
        "old_block_sha256": sha256(block.encode()),
        "new_block_sha256": sha256(replacement.encode()),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
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
    sequence = [m.group(1) for m in DECL_RE.finditer(text)]
    proof, strategy = VARIANTS[args.variant]
    candidate = text
    repairs = []
    if proof is not None:
        candidate, repair = replace_proof(candidate, TARGET, proof)
        repair["strategy"] = strategy
        repairs.append(repair)
    if declaration_header(candidate, AUTHORITATIVE_HEADER) != authoritative_header:
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt statement/header changed")
    if declaration_header(candidate, TARGET) != target_header:
        raise RuntimeError("target statement/header changed")
    candidate_sequence = [m.group(1) for m in DECL_RE.finditer(candidate)]
    if candidate_sequence != sequence:
        raise RuntimeError("declaration sequence changed")
    SOURCE.write_text(candidate, encoding="utf-8")
    data = SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "strategy": strategy,
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
