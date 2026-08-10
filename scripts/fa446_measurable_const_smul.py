#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
INPUT_SHA256 = "4647a9463e4264a7f0e08405b7ccd1ce9be87e7227fa2b91dc52024e2e198152"
OUTPUT_SHA256 = "c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626"
EXPECTED_LINES = 60453

OLD = """      gammaTwoCosetRep q • ModularGroup.fdo :=
  Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹
      hyperbolicMeasure).quasiMeasurePreserving
    modularHalfOpenTile_ae_eq_fdo
"""

NEW = """      gammaTwoCosetRep q • ModularGroup.fdo := by
  letI : MeasurableConstSMul SL(2, ℤ) ℍ :=
    ⟨fun g ↦ (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹ hyperbolicMeasure).quasiMeasurePreserving modularHalfOpenTile_ae_eq_fdo
"""


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def line_count(data: bytes) -> int:
    return data.count(b"\n") + (0 if not data or data.endswith(b"\n") else 1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    out = ROOT / args.output_dir
    out.mkdir(parents=True, exist_ok=True)

    data = SOURCE.read_bytes()
    actual = sha(data)
    if actual != INPUT_SHA256:
        raise RuntimeError(f"unexpected FA445 selected-source input SHA: {actual}")
    if line_count(data) != EXPECTED_LINES:
        raise RuntimeError("input source is not the required 60453-line same-height source")

    text = data.decode("utf-8")
    count = text.count(OLD)
    if count != 1:
        raise RuntimeError(f"selectedHalfOpenTile proof block expected once, found {count}")
    repaired = text.replace(OLD, NEW)
    output = repaired.encode("utf-8")
    output_sha = sha(output)
    if output_sha != OUTPUT_SHA256:
        raise RuntimeError(f"unexpected repaired source SHA: {output_sha}")
    if line_count(output) != EXPECTED_LINES:
        raise RuntimeError("repair changed file height")

    SOURCE.write_bytes(output)
    candidate_copy = out / "Mock2_FunctionalAnalysis-candidate.lean"
    candidate_copy.write_bytes(output)

    candidate_path = out / "CANDIDATE.json"
    metadata = json.loads(candidate_path.read_text(encoding="utf-8"))
    if metadata.get("candidate_sha256") != INPUT_SHA256:
        raise RuntimeError("parent candidate metadata does not match selected FA445 source")
    metadata["variant"] = "measurable_const_smul_local"
    metadata["parent_direct_champion_sha256"] = INPUT_SHA256
    metadata["parent_direct_first_error"] = {
        "line": 32590,
        "column": 5,
        "declaration": "selectedHalfOpenTile_ae_eq_openTile",
        "declaration_index": 2671,
    }
    metadata["candidate_sha256"] = OUTPUT_SHA256
    metadata["line_count"] = EXPECTED_LINES
    repairs = list(metadata.get("repairs", []))
    repairs.append({
        "repair": "proof_local_MeasurableConstSMul",
        "declaration": "selectedHalfOpenTile_ae_eq_openTile",
        "applied": 1,
        "same_height": True,
    })
    metadata["repairs"] = repairs
    candidate_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")

    result = {
        "input_sha256": actual,
        "output_sha256": output_sha,
        "line_count": line_count(output),
        "same_height": True,
        "target_theorem_header_changed": False,
        "changed_declaration": "selectedHalfOpenTile_ae_eq_openTile",
        "repair": "proof-local MeasurableConstSMul SL(2, ℤ) ℍ",
    }
    (out / "FA446_REPAIR.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
