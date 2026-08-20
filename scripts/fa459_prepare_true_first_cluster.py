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
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)",
    re.MULTILINE,
)

spec = importlib.util.spec_from_file_location(
    "fa458_prepare", ROOT / "scripts/fa458_prepare_cumulative_early.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA458 cumulative preparer")
fa458 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa458
spec.loader.exec_module(fa458)

PAIR_DECLS = [
    "nativeActualEdgeFluxIntegral_paired_circular",
    "nativeActualEdgeFluxIntegral_paired_left",
    "nativeActualEdgeFluxIntegral_paired_right",
]
HEADER_DECLS = [
    "actualEdgeAmbientParam_hasDerivAt",
    *PAIR_DECLS,
    "selectedHalfOpenTile_ae_eq_openTile",
    "integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola",
    "compactSupport_height_mul_normSq_le_energy_Ioi",
    "tendsto_zero_normSq_le_energy_Ioi",
]


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
    """Return only the declaration proposition/type through `:=`.

    `:= term` and `:= by` are two proof presentation styles for the same
    theorem statement.  Treating the token `by` as part of the header caused
    the first FA459 generator to reject a statement-preserving repair.
    """
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":=")
    if marker < 0:
        raise RuntimeError(f"proof/body marker not found: {name}")
    return block[: marker + len(":=")]


def replace_body(text: str, name: str, body_after_assign: str) -> str:
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":=")
    if marker < 0:
        raise RuntimeError(f"assignment marker not found: {name}")
    prefix = block[: marker + 2]
    suffix = "\n" if block.endswith("\n") else ""
    return text[:start] + prefix + " " + body_after_assign.rstrip() + "\n" + suffix + text[end:]


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one replacement, found {count}")
    return text.replace(old, new, 1)


PAIR_DOC = """/-- Circular native integrals acquire the sign `-1` under pairing, including
the nontrivial change of variables `t |-> -t`. -/"""
UNIFORM_DOC = """/-- Uniform pairing law for every finite native edge integral. -/"""

MACRO_OPEN = """section ActualPolygonEdgeLiteralPairedCompat
local macro_rules
  | `(($e:term : GammaTwoActualPolygonEdge).paired) =>
      `(GammaTwoActualPolygonEdge.paired ($e : GammaTwoActualPolygonEdge))"""

POSTFIX_OPEN = """section ActualPolygonEdgeLiteralPairedCompat
local postfix:max \".paired\" => GammaTwoActualPolygonEdge.paired"""


def apply_pair_compat(text: str, mode: str) -> tuple[str, dict[str, str]]:
    opening = MACRO_OPEN if mode == "macro" else POSTFIX_OPEN
    text = replace_once(
        text, PAIR_DOC, opening + "\n" + PAIR_DOC,
        f"insert {mode} paired compatibility"
    )
    text = replace_once(
        text, UNIFORM_DOC,
        "end ActualPolygonEdgeLiteralPairedCompat\n\n" + UNIFORM_DOC,
        f"close {mode} paired compatibility"
    )
    return text, {
        "declaration": "PAIRING_SYNTAX_COMPATIBILITY",
        "strategy": f"scoped_{mode}_compat_no_theorem_header_change",
    }


SELECTED_AE_BODY = """by
  change
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (gammaTwoCosetRep q)) •
        modularHalfOpenTile =ᵐ[hyperbolicMeasure]
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (gammaTwoCosetRep q)) •
        ModularGroup.fdo
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (gammaTwoCosetRep q))
    (measurePreserving_smul
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (gammaTwoCosetRep q))⁻¹
      hyperbolicMeasure).quasiMeasurePreserving
    modularHalfOpenTile_ae_eq_fdo"""

HSELECTED_OLD = """  have hSelectedTile : MeasurableSet
      (gammaTwoCosetRep q • modularHalfOpenTile) :=
    MeasurableSet.const_smul modularHalfOpenTile_measurable
      (gammaTwoCosetRep q)"""

HSELECTED_NEW = """  have hSelectedTile : MeasurableSet
      (gammaTwoCosetRep q • modularHalfOpenTile) := by
    change MeasurableSet
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (gammaTwoCosetRep q)) •
        modularHalfOpenTile)
    exact MeasurableSet.const_smul modularHalfOpenTile_measurable
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (gammaTwoCosetRep q))"""


def apply_real_smul_repairs(text: str) -> tuple[str, list[dict[str, str]]]:
    text = replace_body(text, "selectedHalfOpenTile_ae_eq_openTile", SELECTED_AE_BODY)
    text = replace_once(
        text, HSELECTED_OLD, HSELECTED_NEW,
        "selected tile measurable real-SL cast"
    )
    return text, [
        {
            "declaration": "selectedHalfOpenTile_ae_eq_openTile",
            "strategy": "change_integer_SL_action_to_explicit_real_SL_action",
        },
        {
            "declaration": "integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola",
            "strategy": "explicit_real_SL_const_smul_measurability",
        },
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--variant",
        required=True,
        choices=[
            "baseline",
            "macro_pair_only",
            "macro_pair_smul",
            "macro_pair_smul_cumulative",
            "postfix_pair_smul_cumulative",
        ],
    )
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    original = SOURCE.read_bytes()
    if sha256(original) != EXPECTED_SHA:
        raise RuntimeError(
            f"baseline source SHA mismatch: {sha256(original)} != {EXPECTED_SHA}"
        )
    text = original.decode("utf-8")
    if len(text.splitlines()) != EXPECTED_LINES:
        raise RuntimeError(
            f"baseline line count mismatch: {len(text.splitlines())} != {EXPECTED_LINES}"
        )

    original_sequence = [m.group(1) for m in DECL_RE.finditer(text)]
    original_headers = {name: declaration_header(text, name) for name in HEADER_DECLS}
    candidate = text
    repairs: list[dict[str, str]] = []

    if args.variant != "baseline":
        mode = "postfix" if args.variant.startswith("postfix") else "macro"
        candidate, repair = apply_pair_compat(candidate, mode)
        repairs.append(repair)

    if args.variant in {
        "macro_pair_smul",
        "macro_pair_smul_cumulative",
        "postfix_pair_smul_cumulative",
    }:
        candidate, rs = apply_real_smul_repairs(candidate)
        repairs.extend(rs)

    if args.variant in {
        "macro_pair_smul_cumulative",
        "postfix_pair_smul_cumulative",
    }:
        candidate, rs = fa458.apply_cumulative(candidate, "direct_union")
        repairs.extend(rs)

    candidate_sequence = [m.group(1) for m in DECL_RE.finditer(candidate)]
    if candidate_sequence != original_sequence:
        raise RuntimeError("declaration sequence changed")
    for name, header in original_headers.items():
        actual = declaration_header(candidate, name)
        if actual != header:
            raise RuntimeError(f"declaration header changed: {name}")

    SOURCE.write_text(candidate, encoding="utf-8")
    data = SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "strategy": "strict_true_first_cluster",
        "baseline_sha256": EXPECTED_SHA,
        "candidate_sha256": sha256(data),
        "line_count": len(candidate.splitlines()),
        "baseline_line_count": EXPECTED_LINES,
        "authoritative_original_baseline_sha256":
            "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0",
        "target_declaration": "actualEdgeAmbientParam_hasDerivAt",
        "target_header_sha256": sha256(
            original_headers["actualEdgeAmbientParam_hasDerivAt"].encode()
        ),
        "protected_header_sha256": {
            name: sha256(header.encode()) for name, header in original_headers.items()
        },
        "declaration_sequence_sha256": sha256(
            json.dumps(candidate_sequence, separators=(",", ":")).encode()
        ),
        "declaration_count": len(candidate_sequence),
        "repairs": repairs,
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
