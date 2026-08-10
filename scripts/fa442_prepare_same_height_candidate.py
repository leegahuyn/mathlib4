#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path.cwd()
SRC = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
OUT_LINES = 60453
BASELINE_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
TARGET = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)

VARIANTS = {
    "baseline",
    "slope_only",
    "slope_structures",
    "slope_change_convert",
    "slope_paired_parenthesized",
    "slope_paired_dot",
    "slope_paired_parenthesized_ring",
    "slope_paired_parenthesized_ring_height",
    "slope_paired_parenthesized_ring_height_upper",
    "slope_paired_parenthesized_ring_height_upper_tail",
    "slope_paired_parenthesized_ring_height_upper_tail_zero",
    "slope_paired_parenthesized_all_known",
    "slope_paired_dot_all_known",
    "slope_structures_paired_all_known",
    "slope_change_convert_paired_all_known",
    "slope_paired_parenthesized_deep_simp",
}


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def declaration_span(text: str, name: str) -> tuple[int, int, int, str]:
    lines = text.splitlines(keepends=True)
    start = None
    for i, line in enumerate(lines):
        m = DECL_RE.match(line)
        if m and m.group(1) == name:
            start = i
            break
    if start is None:
        raise RuntimeError(f"declaration not found: {name}")
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if DECL_RE.match(lines[i]):
            end = i
            break
    block = "".join(lines[start:end])
    marker = block.find(":= by")
    marker_len = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_len = len(":=")
    if marker < 0:
        raise RuntimeError(f"body marker not found: {name}")
    header = block[: marker + marker_len]
    body_start = start + header.count("\n")
    return start, body_start, end, header


def replace_exact(text: str, old: str, new: str, *, expected: int | None = 1) -> tuple[str, int]:
    count = text.count(old)
    if expected is not None and count != expected:
        raise RuntimeError(
            f"unexpected match count {count}, expected {expected}: {old[:120]!r}"
        )
    if count == 0:
        return text, 0
    result = text.replace(old, new)
    if line_count(result) != line_count(text):
        raise RuntimeError("exact replacement changed file height")
    return result, count


def replace_decl_body_same_height(text: str, name: str, replacement: list[str]) -> str:
    lines = text.splitlines(keepends=True)
    _start, body_start, end, _header = declaration_span(text, name)
    height = end - body_start
    normalized = [line if line.endswith("\n") else line + "\n" for line in replacement]
    if len(normalized) > height:
        raise RuntimeError(
            f"replacement body for {name} has {len(normalized)} lines, source has {height}"
        )
    normalized.extend(["\n"] * (height - len(normalized)))
    lines[body_start:end] = normalized
    result = "".join(lines)
    if line_count(result) != line_count(text):
        raise RuntimeError(f"body replacement changed height for {name}")
    return result


def apply_slope(text: str, mode: str) -> tuple[str, dict]:
    old = (
        "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n"
        "    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp\n"
    )
    if mode == "plain":
        new = (
            "  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢\n"
            "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity, Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp\n"
        )
    elif mode == "structures":
        new = (
            "  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢\n"
            "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity, Function.comp_def, modularTileEdgeAmbientVelocity_eq, Complex.addCommGroup, Complex.instNormedAddCommGroup] using hcomp\n"
        )
    elif mode == "change_convert":
        new = (
            "  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢\n"
            "  convert hcomp using 1 <;> simp [actualEdgeAmbientParam, actualEdgeNativeVelocity, Function.comp_def, modularTileEdgeAmbientVelocity_eq, Complex.addCommGroup, Complex.instNormedAddCommGroup]\n"
        )
    else:
        raise RuntimeError(f"unknown slope mode: {mode}")
    text, count = replace_exact(text, old, new)
    return text, {"repair": f"slope_{mode}", "applied": count}


def apply_paired(text: str, style: str) -> tuple[str, dict]:
    total = 0
    per_edge: dict[str, int] = {}
    for edge, expected in (
        ("circularArc", 5),
        ("leftVerticalSegment", 2),
        ("rightVerticalSegment", 2),
    ):
        old = (
            "GammaTwoActualPolygonEdge.paired "
            f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)"
        )
        count = text.count(old)
        if count != expected:
            raise RuntimeError(
                f"paired {edge} occurrence count {count}, expected {expected}"
            )
        if style == "parenthesized":
            new = (
                "(GammaTwoActualPolygonEdge.paired "
                f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))"
            )
        elif style == "dot":
            new = (
                f"((q, GammaTwoModularTileEdge.{edge}) : "
                "GammaTwoActualPolygonEdge).paired"
            )
        else:
            raise RuntimeError(f"unknown paired style: {style}")
        text = text.replace(old, new)
        total += count
        per_edge[edge] = count
    if line_count(text) != OUT_LINES:
        raise RuntimeError("paired rewrite changed height")
    return text, {"repair": f"paired_{style}", "applied": total, "per_edge": per_edge}


def apply_ring_left(text: str) -> tuple[str, dict]:
    old = "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n"
    new = "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  ring\n"
    text, count = replace_exact(text, old, new)
    return text, {"repair": "left_selected_piola_ring", "applied": count}


def apply_height_membership(text: str) -> tuple[str, dict]:
    old = "        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n"
    new = "        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n"
    text, count = replace_exact(text, old, new)
    return text, {"repair": "height_membership", "applied": count}


def apply_upper_half_plane(text: str) -> tuple[str, dict]:
    records: list[dict] = []
    text, count = replace_exact(
        text,
        "    hcomplex.subtype_mk _\n",
        "    hcomplex.upperHalfPlaneMk _\n",
    )
    records.append({"repair": "upperHalfPlaneMk", "applied": count})
    text, count = replace_exact(
        text,
        "      apply Subtype.ext\n",
        "      apply UpperHalfPlane.ext\n",
    )
    records.append({"repair": "UpperHalfPlane.ext", "applied": count})
    return text, {"repair": "upper_half_plane_cluster", "details": records}


def apply_tail_projection(text: str) -> tuple[str, dict]:
    old = (
        "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)\n"
        "      .eventually_zero_on_horocycleBoundary with\n"
    )
    new = (
        "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with\n"
        "\n"
    )
    text, count = replace_exact(text, old, new, expected=2)
    return text, {"repair": "tail_projection", "applied": count}


def apply_zero_coercion(text: str) -> tuple[str, dict]:
    text, count = replace_exact(
        text,
        "  simpa using htrace.trans hrep\n",
        "  simpa only [Pi.zero_apply] using htrace.trans hrep\n",
    )
    return text, {"repair": "Pi.zero_apply", "applied": count}


def apply_misc_known(text: str) -> tuple[str, dict]:
    records: list[dict] = []
    replacements = [
        (
            "absolute_triangle_rename",
            "      abs_add _ _\n",
            "      abs_add_le _ _\n",
            1,
        ),
        (
            "product_derivative_normalization",
            "  simpa only [one_mul] using hprod.deriv\n",
            "  convert hprod.deriv using 1 <;> ring\n",
            1,
        ),
        (
            "positive_tail_height",
            "    exact norm_deriv_height_mul_normSq_le\n"
            "      (hf.differentiable (by norm_num)) (le_of_lt hy)\n",
            "    exact norm_deriv_height_mul_normSq_le (hf.differentiable (by norm_num))\n"
            "      ((zero_le_one.trans hH).trans (le_of_lt hy))\n",
            1,
        ),
        (
            "nonnegative_multiplier",
            "        (mul_le_mul_of_nonneg_left hinner\n"
            "          (mul_nonneg (by norm_num) hy)) _\n",
            "        (mul_le_mul_of_nonneg_left hinner (by positivity))\n"
            "          _\n",
            1,
        ),
    ]
    for label, old, new, expected in replacements:
        count = text.count(old)
        if count == 0:
            records.append({"repair": label, "applied": 0})
            continue
        text, applied = replace_exact(text, old, new, expected=expected)
        records.append({"repair": label, "applied": applied})
    return text, {"repair": "misc_known", "details": records}


def apply_representative_add_simp(text: str) -> tuple[str, dict]:
    text = replace_decl_body_same_height(
        text,
        "selectedCuspRestrictionRepresentative_add",
        [
            "  funext t\n",
            "  simp [selectedCuspRestrictionRepresentative, mul_add]\n",
        ],
    )
    return text, {"repair": "representative_add_simp", "applied": 1}


def apply_memlp_measure_alignment(text: str) -> tuple[str, dict]:
    text = replace_decl_body_same_height(
        text,
        "selectedCuspRestrictionRepresentative_memLp",
        [
            "  letI : MeasurableSpace ℝ := Real.measureSpace.toMeasurableSpace\n",
            "  let f := selectedCuspRestrictionRepresentative n q Y u\n",
            "  have hf : Continuous f := selectedCuspRestrictionRepresentative_continuous n q Y u\n",
            "  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2\n",
            "  change IntegrableOn (fun x => ‖f x‖ ^ 2)\n",
            "    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) volume\n",
            "  simpa only [Pi.pow_apply] using (hf.norm.pow 2).continuousOn.integrableOn_Icc\n",
        ],
    )
    return text, {"repair": "memLp_measure_alignment", "applied": 1}


def apply_coe_trace_change(text: str) -> tuple[str, dict]:
    text = replace_decl_body_same_height(
        text,
        "coeFn_selectedCuspCoreTrace",
        [
            "  change ⇑((selectedCuspRestrictionRepresentative_memLp n q Y u).toLp\n",
            "    (selectedCuspRestrictionRepresentative n q Y u)) =ᵐ[selectedHorocycleParameterMeasure]\n",
            "      selectedCuspRestrictionRepresentative n q Y u\n",
            "  exact MemLp.coeFn_toLp (selectedCuspRestrictionRepresentative_memLp n q Y u)\n",
        ],
    )
    return text, {"repair": "coe_trace_change", "applied": 1}


def build_variant(baseline: str, variant: str) -> tuple[str, list[dict]]:
    if variant not in VARIANTS:
        raise RuntimeError(f"unknown variant: {variant}")
    if variant == "baseline":
        return baseline, []

    slope_mode = "plain"
    if variant.startswith("slope_structures"):
        slope_mode = "structures"
    elif variant.startswith("slope_change_convert"):
        slope_mode = "change_convert"
    text, record = apply_slope(baseline, slope_mode)
    records = [record]

    if "paired_parenthesized" in variant:
        text, record = apply_paired(text, "parenthesized")
        records.append(record)
    elif "paired_dot" in variant:
        text, record = apply_paired(text, "dot")
        records.append(record)

    if variant.endswith("_ring") or "_ring_" in variant:
        text, record = apply_ring_left(text)
        records.append(record)
    if "_height" in variant:
        text, record = apply_height_membership(text)
        records.append(record)
    if "_upper" in variant:
        text, record = apply_upper_half_plane(text)
        records.append(record)
    if "_tail" in variant:
        text, record = apply_tail_projection(text)
        records.append(record)
    if "_zero" in variant:
        text, record = apply_zero_coercion(text)
        records.append(record)

    if "all_known" in variant or variant.endswith("deep_simp"):
        for repair in (
            apply_ring_left,
            apply_height_membership,
            apply_upper_half_plane,
            apply_tail_projection,
            apply_zero_coercion,
            apply_misc_known,
        ):
            # Avoid duplicate exact repairs already applied by incremental variants.
            try:
                text, record = repair(text)
                records.append(record)
            except RuntimeError as exc:
                if "unexpected match count 0" not in str(exc):
                    raise
        if variant.endswith("deep_simp"):
            for repair in (
                apply_representative_add_simp,
                apply_memlp_measure_alignment,
                apply_coe_trace_change,
            ):
                text, record = repair(text)
                records.append(record)

    if line_count(text) != OUT_LINES:
        raise RuntimeError(
            f"candidate line count {line_count(text)} != expected {OUT_LINES}"
        )
    return text, records


def code_without_comments_or_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    line_comment = False
    block_depth = 0
    string = False
    escaped = False
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""
        if line_comment:
            if c == "\n":
                line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if c == "/" and n == "-":
                block_depth += 1
                out.extend([" ", " "])
                i += 2
                continue
            if c == "-" and n == "/":
                block_depth -= 1
                out.extend([" ", " "])
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if string:
            out.append("\n" if c == "\n" else " ")
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                string = False
            i += 1
            continue
        if c == "-" and n == "-":
            line_comment = True
            out.extend([" ", " "])
            i += 2
            continue
        if c == "/" and n == "-":
            block_depth = 1
            out.extend([" ", " "])
            i += 2
            continue
        if c == '"':
            string = True
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def forbidden_counts(text: str) -> dict[str, int]:
    code = code_without_comments_or_strings(text)
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "new_global_axiom": r"(?m)^\s*(?:protected\s+|private\s+)?axiom\b",
        "unsafe": r"\bunsafe\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    }
    return {name: len(re.findall(pattern, code)) for name, pattern in patterns.items()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline = SRC.read_text(encoding="utf-8")
    baseline_sha = sha_text(baseline)
    if baseline_sha != BASELINE_SHA:
        raise RuntimeError(
            f"checked-in baseline sha {baseline_sha} != required {BASELINE_SHA}"
        )
    if line_count(baseline) != OUT_LINES:
        raise RuntimeError(
            f"checked-in baseline lines {line_count(baseline)} != {OUT_LINES}"
        )
    _, _, _, baseline_header = declaration_span(baseline, TARGET)
    candidate, repairs = build_variant(baseline, args.variant)
    _, _, _, candidate_header = declaration_span(candidate, TARGET)
    if candidate_header != baseline_header:
        raise RuntimeError("target theorem statement/header changed")

    candidate_sha = sha_text(candidate)
    SRC.write_text(candidate, encoding="utf-8")
    (output / "Mock2_FunctionalAnalysis-baseline.lean").write_text(
        baseline, encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_text(
        candidate, encoding="utf-8"
    )
    metadata = {
        "variant": args.variant,
        "baseline_sha256": baseline_sha,
        "candidate_sha256": candidate_sha,
        "line_count": line_count(candidate),
        "target_declaration": TARGET,
        "target_header_sha256": sha_text(baseline_header),
        "repairs": repairs,
        "baseline_forbidden_counts": forbidden_counts(baseline),
        "candidate_forbidden_counts": forbidden_counts(candidate),
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
