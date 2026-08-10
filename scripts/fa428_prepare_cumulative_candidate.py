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
BASE_HELPER = ROOT / "scripts/fa427_prepare_actualedge_candidate.py"
EXPECTED_LINES = 60453

VARIANTS = {
    "pre-only",
    "paired-dot",
    "paired-parenthesized",
    "paired-dot-ring",
    "paired-parenthesized-simp",
    "paired-dot-safe",
    "paired-parenthesized-safe",
    "paired-dot-safe-analytic",
}


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def load_base_module():
    spec = importlib.util.spec_from_file_location("fa427_helper", BASE_HELPER)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load FA427 helper")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def replace_if_exact(text: str, old: str, new: str, *, expected: int | None = None) -> tuple[str, int]:
    count = text.count(old)
    if expected is not None and count not in {0, expected}:
        raise RuntimeError(f"unexpected replacement multiplicity {count}, expected 0 or {expected}: {old[:80]!r}")
    if count == 0:
        return text, 0
    candidate = text.replace(old, new)
    if line_count(candidate) != line_count(text):
        raise RuntimeError("replacement changed file height")
    return candidate, count


def paired(text: str, mode: str) -> tuple[str, int]:
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
        if mode == "dot":
            new = f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired"
        else:
            new = (
                "(GammaTwoActualPolygonEdge.paired "
                f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))"
            )
        text, count = replace_if_exact(text, old, new, expected=expected)
        total += count
    return text, total


def normalization(text: str, tactic: str) -> tuple[str, int]:
    old = "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n"
    new = f"  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  {tactic}\n"
    return replace_if_exact(text, old, new, expected=1)


def apply_safe_hunks(text: str) -> tuple[str, list[dict]]:
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
            "upper-half-plane-extensionality",
            "      apply Subtype.ext\n      apply Complex.ext <;> simp)\n",
            "      apply UpperHalfPlane.ext\n      apply Complex.ext <;> simp)\n",
            1,
        ),
        (
            "absolute-triangle-rename",
            "      abs_add _ _\n",
            "      abs_add_le _ _\n",
            1,
        ),
        (
            "tail-projection-1",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)\n      .eventually_zero_on_horocycleBoundary with\n",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with\n\n",
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
        text, count = replace_if_exact(text, old, new, expected=expected)
        records.append({"label": label, "applied": count})
    return text, records


def insert_measurable_instance_same_height(text: str) -> tuple[str, int]:
    marker = (
        "theorem selectedCuspRestrictionRepresentative_memLp"
    )
    start = text.find(marker)
    if start < 0:
        return text, 0
    lines = text.splitlines(keepends=True)
    char_count = 0
    start_line = 0
    for i, line in enumerate(lines):
        if char_count <= start < char_count + len(line):
            start_line = i
            break
        char_count += len(line)
    end_line = len(lines)
    decl_re = re.compile(r"^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\b")
    for i in range(start_line + 1, len(lines)):
        if decl_re.match(lines[i]):
            end_line = i
            break
    proof_line = next((i for i in range(start_line, end_line) if ":= by" in lines[i]), None)
    if proof_line is None:
        return text, 0
    blank = next((i for i in range(proof_line + 1, min(end_line, proof_line + 8)) if lines[i].strip() == ""), None)
    if blank is None:
        return text, 0
    lines[blank] = "  letI : MeasurableSpace ℝ := Real.measureSpace.toMeasurableSpace\n"
    candidate = "".join(lines)
    if line_count(candidate) != line_count(text):
        raise RuntimeError("measurable-space insertion changed height")
    return candidate, 1


def apply_analytic_hunks(text: str) -> tuple[str, list[dict]]:
    records: list[dict] = []
    text, count = insert_measurable_instance_same_height(text)
    records.append({"label": "measurable-space-alignment", "applied": count})
    replacements = [
        (
            "positive-tail-height",
            "    exact norm_deriv_height_mul_normSq_le\n      (hf.differentiable (by norm_num)) (le_of_lt hy)\n",
            "    exact norm_deriv_height_mul_normSq_le (hf.differentiable (by norm_num))\n      ((zero_le_one.trans hH).trans (le_of_lt hy))\n",
            1,
        ),
        (
            "nonnegative-multiplier",
            "        (mul_le_mul_of_nonneg_left hinner\n          (mul_nonneg (by norm_num) hy)) _\n",
            "        (mul_le_mul_of_nonneg_left hinner (by positivity))\n          _\n",
            1,
        ),
    ]
    for label, old, new, expected in replacements:
        text, count = replace_if_exact(text, old, new, expected=expected)
        records.append({"label": label, "applied": count})
    return text, records


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    base = load_base_module()
    tmp = out / "artifact-downloads"
    tmp.mkdir(parents=True, exist_ok=True)
    baseline_data, provenance = base.recover_exact_source(tmp)
    baseline = baseline_data.decode("utf-8")
    candidate, base_metadata = base.prepare_variant(baseline, "pre-normed-body-remove")
    records: list[dict] = [{"label": "pre-normed-body-remove", "applied": 1}]

    if "paired-dot" in args.variant:
        candidate, count = paired(candidate, "dot")
        records.append({"label": "paired-dot", "applied": count})
    elif "paired-parenthesized" in args.variant:
        candidate, count = paired(candidate, "parenthesized")
        records.append({"label": "paired-parenthesized", "applied": count})

    if args.variant.endswith("-ring"):
        candidate, count = normalization(candidate, "ring")
        records.append({"label": "selected-Piola-ring", "applied": count})
    elif args.variant.endswith("-simp"):
        candidate, count = normalization(candidate, "simp")
        records.append({"label": "selected-Piola-simp", "applied": count})

    if "safe" in args.variant:
        candidate, extra = apply_safe_hunks(candidate)
        records.extend(extra)
    if args.variant.endswith("safe-analytic"):
        candidate, extra = apply_analytic_hunks(candidate)
        records.extend(extra)

    if line_count(candidate) != EXPECTED_LINES:
        raise RuntimeError(f"candidate line count {line_count(candidate)} != {EXPECTED_LINES}")
    _, _, _, baseline_header = base.declaration_span(baseline)
    _, _, _, candidate_header = base.declaration_span(candidate)
    if baseline_header != candidate_header:
        raise RuntimeError("target theorem statement/header changed")

    SOURCE.write_text(candidate, encoding="utf-8")
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_text(candidate, encoding="utf-8")
    (out / "Mock2_FunctionalAnalysis-baseline.lean").write_bytes(baseline_data)
    metadata = {
        "variant": args.variant,
        "baseline_sha256": sha(baseline),
        "candidate_sha256": sha(candidate),
        "line_count": line_count(candidate),
        "target_header_sha256": sha(baseline_header),
        "base_candidate": base_metadata,
        "hunks": records,
        "provenance": provenance,
    }
    (out / "CANDIDATE.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
