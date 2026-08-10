#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE_PATH = ROOT / "scripts/fa456_prepare_direct_union_final_two.py"
F457_PATH = ROOT / "scripts/fa457_prepare_true_first.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def replace_proof(base, text: str, name: str, proof: str):
    start, end = base.declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":= by")
    if marker < 0:
        raise RuntimeError(f"proof marker missing: {name}")
    replacement = block[:marker] + ":= " + proof.rstrip() + "\n\n"
    return text[:start] + replacement + text[end:], {
        "repair": "replace_proof",
        "declaration": name,
        "strategy": proof.splitlines()[0:2],
    }


def patch_deriv_norm(base, text: str):
    name = "integrable_selectedCuspTraceWeight_mul_normSq_deriv_gammaTwoSelectedHorocycleParam_Ioi"
    start, end = base.declaration_span(text, name)
    block = text[start:end]
    old = "  simpa only [one_mul] using hInt\n"
    new = "  simpa only [one_mul, gammaTwoSelectedHorocycleParam_deriv_norm] using hInt\n"
    if block.count(old) != 1:
        raise RuntimeError(f"{name}: expected one derivative simpa, found {block.count(old)}")
    block = block.replace(old, new)
    return text[:start] + block + text[end:], {
        "repair": "derivative_norm_simpa",
        "declaration": name,
    }


TENDSTO_METHOD = '''by
  exact
    (gammaTwoSelectedCuspTruncationMap_tendsto_atTop q Y).congr'
      (gammaTwoSelectedHorocycleParam_ae_eq_selectedCuspTruncationMap q Y).symm
'''

TENDSTO_EXPLICIT = '''by
  exact Filter.Tendsto.congr'
    (gammaTwoSelectedHorocycleParam_ae_eq_selectedCuspTruncationMap q Y).symm
    (gammaTwoSelectedCuspTruncationMap_tendsto_atTop q Y)
'''

TENDSTO_SIMPA = '''by
  simpa only using
    (gammaTwoSelectedCuspTruncationMap_tendsto_atTop q Y).congr'
      (gammaTwoSelectedHorocycleParam_ae_eq_selectedCuspTruncationMap q Y).symm
'''

CONT_FUNPROP = '''by
  fun_prop
'''

CONT_UNFOLD_FUNPROP = '''by
  unfold gammaTwoSelectedHorocycleParam
  fun_prop
'''


def main() -> None:
    base = load(BASE_PATH, "fa456_base")
    f457 = load(F457_PATH, "fa457_base")
    variants = {
        "true_baseline": (None, None),
        "cumulative_deriv": ("none", None),
        "tendsto_method": ("method", None),
        "tendsto_explicit": ("explicit", None),
        "tendsto_simpa": ("simpa", None),
        "tendsto_method_funprop": ("method", "funprop"),
        "tendsto_method_unfold_funprop": ("method", "unfold_funprop"),
        "tendsto_explicit_funprop": ("explicit", "funprop"),
    }
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(variants))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)

    data = base.SOURCE.read_bytes()
    if base.sha256(data) != base.EXPECTED_SHA:
        raise RuntimeError("FA451 baseline SHA mismatch")
    text = data.decode("utf-8")
    authoritative_header = base.declaration_header(text, base.AUTHORITATIVE_HEADER)
    compact_header = base.declaration_header(text, base.TARGET)
    sequence = [match.group(1) for match in base.DECL_RE.finditer(text)]
    candidate = text
    repairs = []

    tendsto_mode, continuity_mode = variants[args.variant]
    if args.variant != "true_baseline":
        candidate, rows = f457.apply_paired(candidate)
        repairs.extend(rows)
        candidate, row = f457.insert_instance(
            base, candidate, "selectedHalfOpenTile_ae_eq_openTile"
        )
        repairs.append(row)
        candidate, row = f457.insert_instance(
            base,
            candidate,
            "integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola",
        )
        repairs.append(row)
        candidate, row = base.replace_proof(candidate, base.TARGET, base.HFTC_LE)
        row["strategy"] = "direct_union_abs"
        repairs.append(row)
        candidate, row = patch_deriv_norm(base, candidate)
        repairs.append(row)

    if tendsto_mode in {"method", "explicit", "simpa"}:
        proof = {
            "method": TENDSTO_METHOD,
            "explicit": TENDSTO_EXPLICIT,
            "simpa": TENDSTO_SIMPA,
        }[tendsto_mode]
        candidate, row = replace_proof(
            base, candidate, "gammaTwoSelectedHorocycleParam_tendsto_atTop", proof
        )
        row["strategy"] = f"tendsto_{tendsto_mode}"
        repairs.append(row)

    if continuity_mode in {"funprop", "unfold_funprop"}:
        proof = {
            "funprop": CONT_FUNPROP,
            "unfold_funprop": CONT_UNFOLD_FUNPROP,
        }[continuity_mode]
        candidate, row = replace_proof(
            base, candidate, "gammaTwoSelectedHorocycleParam_continuous", proof
        )
        row["strategy"] = f"continuity_{continuity_mode}"
        repairs.append(row)

    if base.declaration_header(candidate, base.AUTHORITATIVE_HEADER) != authoritative_header:
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt header changed")
    if base.declaration_header(candidate, base.TARGET) != compact_header:
        raise RuntimeError("compact theorem header changed")
    candidate_sequence = [match.group(1) for match in base.DECL_RE.finditer(candidate)]
    if candidate_sequence != sequence:
        raise RuntimeError("declaration sequence changed")

    base.SOURCE.write_text(candidate, encoding="utf-8")
    result = base.SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "baseline_sha256": base.EXPECTED_SHA,
        "candidate_sha256": base.sha256(result),
        "line_count": len(candidate.splitlines()),
        "baseline_line_count": base.EXPECTED_LINES,
        "target_declaration": base.AUTHORITATIVE_HEADER,
        "target_header_sha256": base.sha256(authoritative_header.encode()),
        "compact_header_sha256": base.sha256(compact_header.encode()),
        "declaration_sequence_sha256": base.sha256(
            json.dumps(candidate_sequence, separators=(",", ":")).encode()
        ),
        "declaration_count": len(candidate_sequence),
        "repairs": repairs,
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(result)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
