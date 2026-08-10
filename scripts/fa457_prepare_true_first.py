#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE_SCRIPT = ROOT / "scripts/fa456_prepare_direct_union_final_two.py"


def load_base():
    spec = importlib.util.spec_from_file_location("fa456_base", BASE_SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load FA456 generator")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


INSTANCE = '''  letI : MeasurableConstSMul (SL(2, ℤ)) ℍ := {
    measurable_const_smul := fun g => by
      change Measurable (fun z : ℍ => ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • z)
      exact (continuous_const_smul _).measurable
  }
'''

PAIRED_EDGES = {
    "circularArc": 5,
    "leftVerticalSegment": 2,
    "rightVerticalSegment": 2,
}


def replace_exact(text: str, old: str, new: str, expected: int, label: str):
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected}, found {count}")
    return text.replace(old, new), {
        "repair": label,
        "occurrences": count,
    }


def insert_instance(base, text: str, theorem: str):
    start, end = base.declaration_span(text, theorem)
    block = text[start:end]
    marker = ":= by\n"
    count = block.count(marker)
    if count != 1:
        raise RuntimeError(f"{theorem}: expected one proof marker, found {count}")
    new_block = block.replace(marker, marker + INSTANCE, 1)
    return text[:start] + new_block + text[end:], {
        "repair": "local_measurable_const_smul",
        "declaration": theorem,
    }


def apply_paired(text: str):
    records = []
    for edge, expected in PAIRED_EDGES.items():
        old = f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired"
        new = (
            "(GammaTwoActualPolygonEdge.paired "
            f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))"
        )
        text, record = replace_exact(text, old, new, expected, f"paired_explicit_{edge}")
        records.append(record)
    return text, records


def main() -> None:
    base = load_base()
    variants = {
        "true_baseline": (False, False, False, False),
        "paired_explicit": (True, False, False, False),
        "paired_selected_instance": (True, True, False, False),
        "paired_both_instances": (True, True, True, False),
        "paired_both_instances_union_abs": (True, True, True, True),
    }
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(variants))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)

    original = base.SOURCE.read_bytes()
    actual_sha = base.sha256(original)
    if actual_sha != base.EXPECTED_SHA:
        raise RuntimeError(f"baseline source SHA mismatch: {actual_sha} != {base.EXPECTED_SHA}")
    text = original.decode("utf-8")
    if len(text.splitlines()) != base.EXPECTED_LINES:
        raise RuntimeError("baseline line count mismatch")
    authoritative_header = base.declaration_header(text, base.AUTHORITATIVE_HEADER)
    compact_header = base.declaration_header(text, base.TARGET)
    sequence = [m.group(1) for m in base.DECL_RE.finditer(text)]

    paired, selected_instance, second_instance, union_abs = variants[args.variant]
    candidate = text
    repairs = []
    if paired:
        candidate, records = apply_paired(candidate)
        repairs.extend(records)
    if selected_instance:
        candidate, record = insert_instance(
            base, candidate, "selectedHalfOpenTile_ae_eq_openTile"
        )
        repairs.append(record)
    if second_instance:
        candidate, record = insert_instance(
            base,
            candidate,
            "integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola",
        )
        repairs.append(record)
    if union_abs:
        candidate, record = base.replace_proof(candidate, base.TARGET, base.HFTC_LE)
        record["strategy"] = "direct_union_abs"
        repairs.append(record)

    if base.declaration_header(candidate, base.AUTHORITATIVE_HEADER) != authoritative_header:
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt header changed")
    if base.declaration_header(candidate, base.TARGET) != compact_header:
        raise RuntimeError("compact-support theorem header changed")
    candidate_sequence = [m.group(1) for m in base.DECL_RE.finditer(candidate)]
    if candidate_sequence != sequence:
        raise RuntimeError("declaration sequence changed")

    base.SOURCE.write_text(candidate, encoding="utf-8")
    data = base.SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "baseline_sha256": base.EXPECTED_SHA,
        "candidate_sha256": base.sha256(data),
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
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
