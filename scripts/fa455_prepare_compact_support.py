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

OLD = """  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [pow_two] using hcompact.norm.mul hcompact.norm
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [pow_two] using
      hcompact.deriv.norm.mul hcompact.deriv.norm
"""

MUL_LEFT = """  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using hcompact.norm.mul_left (f := fun y : ℝ => ‖f y‖)
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using
      hcompact.deriv.norm.mul_left (f := fun y : ℝ => ‖deriv f y‖)
"""

MUL_RIGHT = """  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using hcompact.norm.mul_right (f' := fun y : ℝ => ‖f y‖)
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using
      hcompact.deriv.norm.mul_right (f' := fun y : ℝ => ‖deriv f y‖)
"""

COMP_LEFT = """  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using hcompact.norm.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      hcompact.deriv.norm.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
"""

# Keep the historical selector-compatible labels, but record the real strategy.
VARIANTS = {
    "baseline": (None, "baseline"),
    "direct_union": (MUL_LEFT, "HasCompactSupport.mul_left"),
    "direct_union_explicit": (MUL_RIGHT, "HasCompactSupport.mul_right"),
    "direct_union_abs": (COMP_LEFT, "HasCompactSupport.comp_left_pow_two"),
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
    return block[: marker + marker_len]


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
    replacement, strategy = VARIANTS[args.variant]
    candidate = text
    repairs = []
    if replacement is not None:
        if candidate.count(OLD) != 1:
            raise RuntimeError("expected unique compact-support block not found")
        candidate = candidate.replace(OLD, replacement, 1)
        repairs.append({"declaration": TARGET, "strategy": strategy})

    if len(candidate.splitlines()) != EXPECTED_LINES:
        raise RuntimeError("same-height invariant violated")
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
