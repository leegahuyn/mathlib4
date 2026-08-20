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
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)",
    re.MULTILINE,
)


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
    return block[: marker + marker_len]


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


DIRECT_UNION_PROOF = r"""by
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
  have henergyCompact : HasCompactSupport energy := by
    change HasCompactSupport (fun y : ℝ =>
      2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2)
    have hUnion : IsCompact (tsupport f ∪ tsupport (deriv f)) :=
      hcompact.union hcompact.deriv
    apply hUnion.of_isClosed_subset (isClosed_tsupport energy)
    apply closure_minimal
    · intro y hy
      simp only [Function.mem_support] at hy
      by_cases hfy : f y = 0
      · right
        apply subset_closure
        simp only [Function.mem_support]
        intro hdfy
        apply hy
        simp [energy, hfy, hdfy]
      · left
        exact subset_closure hfy
    · exact hUnion.isClosed
  have hweightedSmooth : ContDiff ℝ 1 weighted := by
    simpa [weighted] using (contDiff_id.mul (hf.norm.pow 2))
  have henergyContinuous : Continuous energy := by
    simpa [energy] using
      (hf.continuous.norm.pow 2).const_mul 2 |>.add
        ((continuous_id.pow 2).mul
          (hcompact.deriv.continuous.norm.pow 2))
  have hweightedIntegrable : Integrable weighted :=
    hweightedCompact.integrable hweightedSmooth.continuous
  have henergyIntegrable : Integrable energy :=
    henergyCompact.integrable henergyContinuous
  have hFTC : ‖weighted H‖ =
      ‖∫ y in Set.Ioi H, deriv weighted y‖ :=
    congrArg norm
      (integral_Ioi_deriv_eq hweightedSmooth.continuous
        hweightedIntegrable hweightedCompact)
  have hpointwise : ∀ y ∈ Set.Ioi H,
      ‖deriv weighted y‖ ≤ energy y := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans (by linarith) (le_of_lt hy)
    simpa [weighted, energy] using
      norm_deriv_height_mul_normSq_le hf hy0
  have hmono : ‖∫ y in Set.Ioi H, deriv weighted y‖ ≤
      ∫ y in Set.Ioi H, energy y := by
    calc
      ‖∫ y in Set.Ioi H, deriv weighted y‖ ≤
          ∫ y in Set.Ioi H, ‖deriv weighted y‖ :=
        norm_integral_le_of_norm hweightedSmooth.continuous.deriv.continuousOn
      _ ≤ ∫ y in Set.Ioi H, energy y :=
        MeasureTheory.setIntegral_mono_on henergyIntegrable.integrableOn
          hweightedSmooth.continuous.deriv.norm.aestronglyMeasurable
          (ae_restrict_of_forall_mem measurableSet_Ioi hpointwise)
  have hweightedNonneg : 0 ≤ weighted H := by
    dsimp [weighted]
    exact mul_nonneg (le_trans (by norm_num) hH) (sq_nonneg _)
  calc
    H * ‖f H‖ ^ 2 = weighted H := rfl
    _ = ‖weighted H‖ := (Real.norm_of_nonneg hweightedNonneg).symm
    _ ≤ ∫ y in Set.Ioi H, energy y := hFTC.trans hmono"""


DIRECT_UNION_EXPLICIT_PROOF = DIRECT_UNION_PROOF.replace(
    "simp [energy, hfy, hdfy]",
    "simp only [energy, hfy, hdfy, norm_zero, zero_pow, mul_zero, add_zero]",
)

DIRECT_UNION_SUPPORT_ONLY_PROOF = DIRECT_UNION_PROOF.replace(
    "  have hweightedNonneg : 0 ≤ weighted H := by\n"
    "    dsimp [weighted]\n"
    "    exact mul_nonneg (le_trans (by norm_num) hH) (sq_nonneg _)\n"
    "  calc\n"
    "    H * ‖f H‖ ^ 2 = weighted H := rfl\n"
    "    _ = ‖weighted H‖ := (Real.norm_of_nonneg hweightedNonneg).symm\n"
    "    _ ≤ ∫ y in Set.Ioi H, energy y := hFTC.trans hmono",
    "  calc\n"
    "    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by\n"
    "      rw [Real.norm_eq_abs]\n"
    "      exact (abs_of_nonneg\n"
    "        (mul_nonneg (le_trans (by norm_num) hH) (sq_nonneg _))).symm\n"
    "    _ ≤ ∫ y in Set.Ioi H, energy y := hFTC.trans hmono",
)

VARIANTS = {
    "baseline": None,
    "direct_union": DIRECT_UNION_PROOF,
    "direct_union_explicit": DIRECT_UNION_EXPLICIT_PROOF,
    "direct_union_abs": DIRECT_UNION_SUPPORT_ONLY_PROOF,
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    original = SOURCE.read_bytes()
    original_sha = sha256(original)
    if original_sha != EXPECTED_SHA:
        raise RuntimeError(f"FA451 champion SHA mismatch: {original_sha} != {EXPECTED_SHA}")
    text = original.decode("utf-8")
    if len(text.splitlines()) != EXPECTED_LINES:
        raise RuntimeError("FA451 champion line count mismatch")

    authoritative_header = declaration_header(text, AUTHORITATIVE_HEADER)
    target_header = declaration_header(text, TARGET)
    sequence = [m.group(1) for m in DECL_RE.finditer(text)]
    candidate = text
    repairs: list[dict[str, str]] = []
    proof = VARIANTS[args.variant]
    if proof is not None:
        candidate, repair = replace_proof(candidate, TARGET, proof)
        repairs.append(repair)

    if declaration_header(candidate, AUTHORITATIVE_HEADER) != authoritative_header:
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt statement/header changed")
    if declaration_header(candidate, TARGET) != target_header:
        raise RuntimeError("compact theorem statement/header changed")
    candidate_sequence = [m.group(1) for m in DECL_RE.finditer(candidate)]
    if candidate_sequence != sequence:
        raise RuntimeError("declaration sequence changed")

    SOURCE.write_text(candidate, encoding="utf-8")
    data = SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "baseline_sha256": EXPECTED_SHA,
        "candidate_sha256": sha256(data),
        "line_count": len(candidate.splitlines()),
        "baseline_line_count": EXPECTED_LINES,
        "target_declaration": AUTHORITATIVE_HEADER,
        "target_header_sha256": sha256(authoritative_header.encode()),
        "compact_header_sha256": sha256(target_header.encode()),
        "declaration_sequence_sha256": sha256(
            json.dumps(candidate_sequence, separators=(",", ":")).encode()
        ),
        "declaration_count": len(candidate_sequence),
        "repairs": repairs,
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
