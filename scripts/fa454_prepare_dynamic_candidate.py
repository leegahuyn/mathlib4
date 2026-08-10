#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BASELINE_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
BASELINE_LINES = 60450
AUTHORITATIVE_DECL = "actualEdgeAmbientParam_hasDerivAt"
COMPACT_DECL = "compactSupport_height_mul_normSq_le_energy_Ioi"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)",
    re.MULTILINE,
)
FORBIDDEN_RE = re.compile(
    r"\b(?:sorry|admit|unsafe|native_decide|Lean\.ofReduceBool)\b|"
    r"(?m)^\s*(?:protected\s+|private\s+)?axiom\b"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_matches(text: str) -> list[re.Match[str]]:
    return list(DECL_RE.finditer(text))


def declaration_span(text: str, name: str) -> tuple[int, int]:
    matches = declaration_matches(text)
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
    return block[: marker + marker_len]


def declaration_at(text: str, line: int) -> dict[str, int | str]:
    current_name = "<unknown>"
    current_index = -1
    current_line = 0
    for index, match in enumerate(declaration_matches(text)):
        declaration_line = text.count("\n", 0, match.start()) + 1
        if declaration_line > line:
            break
        current_name = match.group(1)
        current_index = index
        current_line = declaration_line
    return {
        "name": current_name,
        "index": current_index,
        "line": current_line,
    }


def replace_proof(text: str, name: str, proof: str) -> tuple[str, dict[str, object]]:
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":= by")
    if marker < 0:
        raise RuntimeError(f"`:= by` not found in {name}")
    prefix = block[:marker]
    trailing_newline = "\n" if block.endswith("\n") else ""
    replacement = prefix + ":= " + proof.rstrip() + "\n" + trailing_newline
    return text[:start] + replacement + text[end:], {
        "kind": "replace_proof",
        "declaration": name,
        "old_block_sha256": sha256(block.encode()),
        "new_block_sha256": sha256(replacement.encode()),
    }


COMPACT_PROOF = r"""by
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


def apply_compact(text: str) -> tuple[str, dict[str, object]]:
    return replace_proof(text, COMPACT_DECL, COMPACT_PROOF)


def apply_line_strategy(
    text: str, line: int, strategy: str
) -> tuple[str, dict[str, object]]:
    lines = text.splitlines(keepends=True)
    if line < 1 or line > len(lines):
        raise RuntimeError(f"error line outside source: {line}")
    index = line - 1
    raw = lines[index]
    indent = re.match(r"\s*", raw).group(0)
    newline = "\n" if raw.endswith("\n") else ""
    stripped = raw.strip()
    replacement: list[str]
    if strategy in {
        "simp_q",
        "aesop_q",
        "exact_q",
        "apply_q",
        "simp_all",
        "aesop",
        "grind",
        "norm_num",
        "ring_nf",
        "linarith",
        "nlinarith",
        "positivity",
    }:
        tactic = {
            "simp_q": "simp?",
            "aesop_q": "aesop?",
            "exact_q": "exact?",
            "apply_q": "apply?",
        }.get(strategy, strategy)
        replacement = [indent + tactic + newline]
    elif strategy in {"then_simp_all", "then_aesop", "then_grind"}:
        suffix = {
            "then_simp_all": " <;> simp_all",
            "then_aesop": " <;> aesop",
            "then_grind": " <;> grind",
        }[strategy]
        replacement = [raw.rstrip("\n") + suffix + newline]
    elif strategy == "insert_classical":
        replacement = [indent + "classical\n", raw]
    elif strategy == "exact_simpa":
        if not stripped.startswith("exact "):
            raise RuntimeError("error line is not an exact tactic")
        replacement = [indent + "simpa using " + stripped[6:] + newline]
    elif strategy == "exact_convert":
        if not stripped.startswith("exact "):
            raise RuntimeError("error line is not an exact tactic")
        replacement = [
            indent + "convert " + stripped[6:] + " using 1 <;> simp_all" + newline
        ]
    else:
        raise RuntimeError(f"unknown line strategy: {strategy}")
    lines[index : index + 1] = replacement
    candidate = "".join(lines)
    return candidate, {
        "kind": "line_strategy",
        "strategy": strategy,
        "line": line,
        "old_line": raw.rstrip("\n"),
        "new_lines": [value.rstrip("\n") for value in replacement],
    }


def apply_theorem_strategy(
    text: str, declaration: str, strategy: str
) -> tuple[str, dict[str, object]]:
    body = {
        "theorem_aesop": "by\n  classical\n  aesop",
        "theorem_simp_all": "by\n  classical\n  simp_all",
        "theorem_grind": "by\n  classical\n  grind",
        "theorem_first": (
            "by\n  classical\n  first | aesop | grind | simp_all | ring_nf | "
            "nlinarith | linarith | positivity | norm_num"
        ),
    }.get(strategy)
    if body is None:
        raise RuntimeError(f"unknown theorem strategy: {strategy}")
    return replace_proof(text, declaration, body)


def invariants(text: str) -> dict[str, object]:
    return {
        "authoritative_header_sha256": sha256(
            declaration_header(text, AUTHORITATIVE_DECL).encode()
        ),
        "compact_header_sha256": sha256(
            declaration_header(text, COMPACT_DECL).encode()
        ),
        "declaration_sequence_sha256": sha256(
            json.dumps(
                [match.group(1) for match in declaration_matches(text)],
                separators=(",", ":"),
            ).encode()
        ),
        "declaration_count": len(declaration_matches(text)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True)
    parser.add_argument("--stage", choices=["initial", "second"], required=True)
    parser.add_argument("--error-line", type=int, default=0)
    parser.add_argument("--error-declaration", default="")
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    original = SOURCE.read_bytes()
    original_text = original.decode("utf-8")
    original_invariants = invariants(original_text)
    repairs: list[dict[str, object]] = []
    candidate = original_text

    if args.stage == "initial":
        if args.variant == "baseline":
            pass
        elif args.variant.startswith("compact"):
            candidate, repair = apply_compact(candidate)
            repairs.append(repair)
        else:
            raise RuntimeError(f"initial variant must be baseline/compact: {args.variant}")
    else:
        strategy = args.variant.removeprefix("compact_then_")
        if strategy.startswith("theorem_"):
            if not args.error_declaration:
                raise RuntimeError("second-stage declaration missing")
            candidate, repair = apply_theorem_strategy(
                candidate, args.error_declaration, strategy
            )
        else:
            candidate, repair = apply_line_strategy(
                candidate, args.error_line, strategy
            )
        repairs.append(repair)

    if FORBIDDEN_RE.search(candidate):
        raise RuntimeError("forbidden token introduced")
    candidate_invariants = invariants(candidate)
    if (
        candidate_invariants["authoritative_header_sha256"]
        != original_invariants["authoritative_header_sha256"]
    ):
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt header changed")
    if (
        candidate_invariants["compact_header_sha256"]
        != original_invariants["compact_header_sha256"]
    ):
        raise RuntimeError("compact theorem header changed")
    if (
        candidate_invariants["declaration_sequence_sha256"]
        != original_invariants["declaration_sequence_sha256"]
    ):
        raise RuntimeError("declaration sequence changed")

    SOURCE.write_text(candidate, encoding="utf-8")
    data = SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "stage": args.stage,
        "source_sha256_before": sha256(original),
        "candidate_sha256": sha256(data),
        "line_count": len(candidate.splitlines()),
        "baseline_expected_sha256": BASELINE_SHA,
        "baseline_expected_line_count": BASELINE_LINES,
        "error_line_used": args.error_line,
        "error_declaration_used": args.error_declaration,
        "repairs": repairs,
        **candidate_invariants,
    }
    (output / f"PREPARE-{args.stage}.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(metadata, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
