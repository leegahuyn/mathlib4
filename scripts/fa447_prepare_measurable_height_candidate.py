#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
PARENT_SHA256 = "4647a9463e4264a7f0e08405b7ccd1ce9be87e7227fa2b91dc52024e2e198152"
EXPECTED_LINES = 60453
TARGET = "actualEdgeAmbientParam_hasDerivAt"

EXPECTED_OUTPUTS = {
    "parent": PARENT_SHA256,
    "proof_local_height": "07afb89ecce1d0b6be4c15bb6752a6907a4594d6a37f6b516868b09cd61bc43d",
    "namespace_local": "f208d4d86fe225e2e18f69220b0660db683dbaa5b62835f2a8196f59325aa2ef",
    "namespace_local_height": "c278f9488601dd69535acf508ef10d49aecafd1e143a8e5a55f554478102174a",
}

PROOF_LOCAL_OLD = """      gammaTwoCosetRep q • ModularGroup.fdo :=
  Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹
      hyperbolicMeasure).quasiMeasurePreserving
    modularHalfOpenTile_ae_eq_fdo
"""
PROOF_LOCAL_NEW = """      gammaTwoCosetRep q • ModularGroup.fdo := by
  letI : MeasurableConstSMul SL(2, ℤ) ℍ :=
    ⟨fun g ↦ (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹ hyperbolicMeasure).quasiMeasurePreserving modularHalfOpenTile_ae_eq_fdo
"""
NAMESPACE_ANCHOR = """open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
"""
NAMESPACE_INSTANCE = """open HalfWeightDifferentialOperators SmoothCompactCoreGeometry
local instance gammaTwoGlobalStokesBridgeMeasurableConstSMul : MeasurableConstSMul SL(2, ℤ) ℍ := ⟨fun g ↦ (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩
/-! #### A. The selected open and half-open tiles agree almost everywhere -/
"""
HEIGHT_OLD = "        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩"
HEIGHT_NEW = "        (show z.im ≤ H from le_of_not_gt hHigh)⟩"


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def load_audit_module():
    path = ROOT / "scripts/fa442_prepare_same_height_candidate.py"
    spec = importlib.util.spec_from_file_location("fa447_audit", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load same-height audit module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, dict]:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one exact occurrence, found {count}")
    result = text.replace(old, new)
    if line_count(result) != line_count(text):
        raise RuntimeError(f"{label}: changed file height")
    return result, {"repair": label, "applied": 1, "same_height": True}


def build(parent: str, variant: str) -> tuple[str, list[dict]]:
    text = parent
    repairs: list[dict] = []
    if variant == "parent":
        return text, repairs
    if variant == "proof_local_height":
        text, r = replace_once(text, PROOF_LOCAL_OLD, PROOF_LOCAL_NEW,
                               "proof_local_MeasurableConstSMul")
        repairs.append(r)
        text, r = replace_once(text, HEIGHT_OLD, HEIGHT_NEW, "height_membership")
        repairs.append(r)
        return text, repairs
    if variant in {"namespace_local", "namespace_local_height"}:
        text, r = replace_once(text, NAMESPACE_ANCHOR, NAMESPACE_INSTANCE,
                               "namespace_local_MeasurableConstSMul")
        repairs.append(r)
        if variant.endswith("_height"):
            text, r = replace_once(text, HEIGHT_OLD, HEIGHT_NEW, "height_membership")
            repairs.append(r)
        return text, repairs
    raise RuntimeError(f"unknown variant: {variant}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(EXPECTED_OUTPUTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    out = ROOT / args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    parent = SOURCE.read_text(encoding="utf-8")
    parent_sha = sha_text(parent)
    if parent_sha != PARENT_SHA256:
        raise RuntimeError(f"checked-in parent SHA {parent_sha} != {PARENT_SHA256}")
    if line_count(parent) != EXPECTED_LINES:
        raise RuntimeError("parent is not the required 60453-line source")

    audit_module = load_audit_module()
    _, _, _, parent_header = audit_module.declaration_span(parent, TARGET)
    candidate, repairs = build(parent, args.variant)
    _, _, _, candidate_header = audit_module.declaration_span(candidate, TARGET)
    if candidate_header != parent_header:
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt header changed")
    if line_count(candidate) != EXPECTED_LINES:
        raise RuntimeError("candidate changed file height")

    candidate_sha = sha_text(candidate)
    expected = EXPECTED_OUTPUTS[args.variant]
    if candidate_sha != expected:
        raise RuntimeError(f"unexpected candidate SHA {candidate_sha}, expected {expected}")
    audit = dict(audit_module.forbidden_counts(candidate))
    if any(value != 0 for value in audit.values()):
        raise RuntimeError(f"forbidden-token audit failed: {audit}")

    SOURCE.write_text(candidate, encoding="utf-8")
    (out / "Mock2_FunctionalAnalysis-parent.lean").write_text(parent, encoding="utf-8")
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_text(candidate, encoding="utf-8")
    metadata = {
        "variant": args.variant,
        "baseline_sha256": parent_sha,
        "candidate_sha256": candidate_sha,
        "line_count": EXPECTED_LINES,
        "target_declaration": TARGET,
        "target_header_sha256": sha_text(parent_header),
        "parent_direct_first_error": {
            "line": 32590,
            "column": 5,
            "declaration": "selectedHalfOpenTile_ae_eq_openTile",
            "declaration_index": 2671,
        },
        "repairs": repairs,
        "baseline_forbidden_counts": dict(audit_module.forbidden_counts(parent)),
        "candidate_forbidden_counts": audit,
    }
    (out / "CANDIDATE.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
