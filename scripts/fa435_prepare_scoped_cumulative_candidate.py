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
SCOPED_HELPER = ROOT / "scripts/fa432_prepare_scoped_instance_candidate.py"
EXPECTED_LINES = 60453

VARIANTS = {
    "baseline",
    "scoped-only",
    "scoped-paired-dot",
    "scoped-paired-parenthesized",
    "scoped-paired-dot-ring",
    "scoped-paired-parenthesized-simp",
    "scoped-paired-dot-safe",
    "scoped-paired-parenthesized-safe",
    "scoped-paired-dot-safe-analytic",
    "scoped-paired-parenthesized-safe-analytic",
}


def load_helper():
    spec = importlib.util.spec_from_file_location("fa432_for_fa435", SCOPED_HELPER)
    if spec is None or spec.loader is None:
        raise RuntimeError("unable to load FA432 helper")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def replace_same_height(
    text: str, old: str, new: str, *, expected: int | tuple[int, ...] | None = None
) -> tuple[str, int]:
    count = text.count(old)
    allowed: tuple[int, ...]
    if expected is None:
        allowed = (count,)
    elif isinstance(expected, tuple):
        allowed = expected
    else:
        allowed = (0, expected)
    if expected is not None and count not in allowed:
        raise RuntimeError(
            f"replacement multiplicity {count} not in {allowed}: {old[:100]!r}"
        )
    if count == 0:
        return text, 0
    candidate = text.replace(old, new)
    if line_count(candidate) != line_count(text):
        raise RuntimeError("replacement changed file height")
    return candidate, count


def apply_paired(text: str, style: str) -> tuple[str, int]:
    total = 0
    for edge, expected in (
        ("circularArc", 5),
        ("leftVerticalSegment", 2),
        ("rightVerticalSegment", 2),
    ):
        old = (
            "GammaTwoActualPolygonEdge.paired "
            f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)"
        )
        if style == "dot":
            new = (
                f"((q, GammaTwoModularTileEdge.{edge}) : "
                "GammaTwoActualPolygonEdge).paired"
            )
        else:
            new = (
                "(GammaTwoActualPolygonEdge.paired "
                f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))"
            )
        text, count = replace_same_height(text, old, new, expected=expected)
        total += count
    return text, total


def apply_selected_piola(text: str, tactic: str) -> tuple[str, int]:
    old = "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n"
    new = (
        "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n"
        f"  {tactic}\n"
    )
    return replace_same_height(text, old, new, expected=1)


def insert_measurable_space(text: str) -> tuple[str, int]:
    marker = "theorem selectedCuspRestrictionRepresentative_memLp"
    char_index = text.find(marker)
    if char_index < 0:
        return text, 0
    lines = text.splitlines(keepends=True)
    offset = 0
    start = None
    for i, line in enumerate(lines):
        if offset <= char_index < offset + len(line):
            start = i
            break
        offset += len(line)
    if start is None:
        return text, 0
    decl_re = re.compile(
        r"^(?:protected\s+|private\s+|noncomputable\s+)?"
        r"(?:theorem|lemma|def|abbrev|instance|structure|class)\b"
    )
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if decl_re.match(lines[i]):
            end = i
            break
    proof_line = next((i for i in range(start, end) if ":= by" in lines[i]), None)
    if proof_line is None:
        return text, 0
    blank = next(
        (i for i in range(proof_line + 1, min(end, proof_line + 9)) if lines[i].strip() == ""),
        None,
    )
    if blank is None:
        return text, 0
    lines[blank] = "  letI : MeasurableSpace ℝ := Real.measureSpace.toMeasurableSpace\n"
    candidate = "".join(lines)
    if line_count(candidate) != line_count(text):
        raise RuntimeError("measurable-space insertion changed file height")
    return candidate, 1


def apply_safe(text: str) -> tuple[str, list[dict]]:
    records: list[dict] = []
    replacements = [
        (
            "height-membership",
            "        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n",
            "        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n",
            1,
        ),
        (
            "upper-half-plane-constructor",
            "    hcomplex.subtype_mk _\n",
            "    hcomplex.upperHalfPlaneMk _\n",
            1,
        ),
        (
            "upper-half-plane-ext",
            "      apply Subtype.ext\n      apply Complex.ext <;> simp)\n",
            "      apply UpperHalfPlane.ext\n      apply Complex.ext <;> simp)\n",
            1,
        ),
        (
            "absolute-triangle",
            "      abs_add _ _\n",
            "      abs_add_le _ _\n",
            1,
        ),
        (
            "tail-projection",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)\n"
            "      .eventually_zero_on_horocycleBoundary with\n",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)"
            ".eventually_zero_on_horocycleBoundary with\n\n",
            2,
        ),
        (
            "zero-function-coercion",
            "  simpa using htrace.trans hrep\n",
            "  simpa only [Pi.zero_apply] using htrace.trans hrep\n",
            1,
        ),
        (
            "product-derivative-normalization",
            "  simpa only [one_mul] using hprod.deriv\n",
            "  convert hprod.deriv using 1 <;> ring\n",
            1,
        ),
    ]
    for label, old, new, expected in replacements:
        text, count = replace_same_height(text, old, new, expected=expected)
        records.append({"label": label, "applied": count})
    return text, records


def apply_analytic(text: str) -> tuple[str, list[dict]]:
    records: list[dict] = []
    text, count = insert_measurable_space(text)
    records.append({"label": "measurable-space-alignment", "applied": count})
    replacements = [
        (
            "positive-tail-height",
            "    exact norm_deriv_height_mul_normSq_le\n"
            "      (hf.differentiable (by norm_num)) (le_of_lt hy)\n",
            "    exact norm_deriv_height_mul_normSq_le (hf.differentiable (by norm_num))\n"
            "      ((zero_le_one.trans hH).trans (le_of_lt hy))\n",
            1,
        ),
        (
            "nonnegative-multiplier",
            "        (mul_le_mul_of_nonneg_left hinner\n"
            "          (mul_nonneg (by norm_num) hy)) _\n",
            "        (mul_le_mul_of_nonneg_left hinner (by positivity))\n"
            "          _\n",
            1,
        ),
    ]
    for label, old, new, expected in replacements:
        text, count = replace_same_height(text, old, new, expected=expected)
        records.append({"label": label, "applied": count})
    return text, records


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    helper = load_helper()
    artifact_dir = output / "artifact-downloads"
    artifact_dir.mkdir(parents=True, exist_ok=True)
    baseline_data, provenance = helper.load_helper().recover_exact_source(artifact_dir)
    baseline = baseline_data.decode("utf-8")
    if args.variant == "baseline":
        candidate, scoped_metadata = helper.prepare(baseline, "baseline")
    else:
        candidate, scoped_metadata = helper.prepare(baseline, "scoped-normed-remove")
    records: list[dict] = [
        {
            "label": "scoped-normed-remove",
            "applied": 0 if args.variant == "baseline" else 1,
        }
    ]

    if "paired-dot" in args.variant:
        candidate, count = apply_paired(candidate, "dot")
        records.append({"label": "paired-dot", "applied": count})
    elif "paired-parenthesized" in args.variant:
        candidate, count = apply_paired(candidate, "parenthesized")
        records.append({"label": "paired-parenthesized", "applied": count})

    if args.variant.endswith("-ring"):
        candidate, count = apply_selected_piola(candidate, "ring")
        records.append({"label": "selected-Piola-ring", "applied": count})
    elif args.variant.endswith("-simp"):
        candidate, count = apply_selected_piola(candidate, "simp")
        records.append({"label": "selected-Piola-simp", "applied": count})

    if "safe" in args.variant:
        candidate, extra = apply_safe(candidate)
        records.extend(extra)
    if args.variant.endswith("safe-analytic"):
        candidate, extra = apply_analytic(candidate)
        records.extend(extra)

    if line_count(candidate) != EXPECTED_LINES:
        raise RuntimeError(
            f"candidate line count {line_count(candidate)} != {EXPECTED_LINES}"
        )
    _, _, _, baseline_header = helper.declaration_span(baseline)
    _, _, _, candidate_header = helper.declaration_span(candidate)
    if baseline_header != candidate_header:
        raise RuntimeError("target theorem statement/header changed")

    SOURCE.write_text(candidate, encoding="utf-8")
    (output / "Mock2_FunctionalAnalysis-baseline.lean").write_bytes(baseline_data)
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_text(
        candidate, encoding="utf-8"
    )
    metadata = {
        "variant": args.variant,
        "baseline_sha256": sha(baseline),
        "candidate_sha256": sha(candidate),
        "line_count": line_count(candidate),
        "target_header_sha256": sha(baseline_header),
        "scoped_metadata": scoped_metadata,
        "hunks": records,
        "provenance": provenance,
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
