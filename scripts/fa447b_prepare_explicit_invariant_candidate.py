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
CHAMPION_SHA = "c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626"
EXPECTED_LINES = 60453
TARGET = "actualEdgeAmbientParam_hasDerivAt"
INSTANCE_NAME = "UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume"
EXPECTED_OUTPUTS = {
    "champion": CHAMPION_SHA,
    "proof_explicit": "6613fd6cacd3aae8ea16561e42e3f67cb763219ddbf1885b426b42f6b0e89c9a",
    "proof_explicit_height": "2bf64d3eca2579915bcbb8db4fa766fe9b0ed2d69609eb5cf6522ece1a124893",
    "namespace_explicit": "9578814ffd1b3cbf28c33fcc32ca43e68d0db026a9be2b18c5ba50c1577e9c15",
    "namespace_explicit_height": "0475ba4ba5327b21350ad7991dbad54ba7d56684d5df02ae23f9192fd6ed69ac",
}

CHAMPION_BLOCK = """      gammaTwoCosetRep q • ModularGroup.fdo := by
  letI : MeasurableConstSMul SL(2, ℤ) ℍ :=
    ⟨fun g ↦ (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹ hyperbolicMeasure).quasiMeasurePreserving modularHalfOpenTile_ae_eq_fdo
"""
ORIGINAL_BLOCK = """      gammaTwoCosetRep q • ModularGroup.fdo :=
  Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹
      hyperbolicMeasure).quasiMeasurePreserving
    modularHalfOpenTile_ae_eq_fdo
"""
PROOF_EXPLICIT = f"""      gammaTwoCosetRep q • ModularGroup.fdo := by
  letI : MeasurableConstSMul SL(2, ℤ) ℍ := ⟨fun g ↦ (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩
  letI : MeasureTheory.SMulInvariantMeasure SL(2, ℤ) ℍ hyperbolicMeasure := ⟨fun g s hs ↦ by change hyperbolicMeasure ((fun z : ℍ => (g : GL (Fin 2) ℝ) • z) ⁻¹' s) = hyperbolicMeasure s; exact {INSTANCE_NAME}.1 (g : GL (Fin 2) ℝ) hs⟩
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹ hyperbolicMeasure).quasiMeasurePreserving modularHalfOpenTile_ae_eq_fdo
"""
NAMESPACE_ANCHOR = """namespace GammaTwoGlobalStokesBridge

open MeasureTheory Set Function Topology Filter
"""
NAMESPACE_EXPLICIT = f"""namespace GammaTwoGlobalStokesBridge
local instance gammaTwoGlobalStokesBridgeSMulInvariantMeasure : MeasureTheory.SMulInvariantMeasure SL(2, ℤ) ℍ hyperbolicMeasure := ⟨fun g s hs ↦ by change hyperbolicMeasure ((fun z : ℍ => (g : GL (Fin 2) ℝ) • z) ⁻¹' s) = hyperbolicMeasure s; exact {INSTANCE_NAME}.1 (g : GL (Fin 2) ℝ) hs⟩
open MeasureTheory Set Function Topology Filter
"""
MEASURABLE_ANCHOR = """open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
"""
MEASURABLE_INSTANCE = """open HalfWeightDifferentialOperators SmoothCompactCoreGeometry
local instance gammaTwoGlobalStokesBridgeMeasurableConstSMul : MeasurableConstSMul SL(2, ℤ) ℍ := ⟨fun g ↦ (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩
/-! #### A. The selected open and half-open tiles agree almost everywhere -/
"""
HEIGHT_OLD = "        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩"
HEIGHT_NEW = "        (show z.im ≤ H from le_of_not_gt hHigh)⟩"


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def load_helpers():
    p = ROOT / "scripts/fa442_prepare_same_height_candidate.py"
    spec = importlib.util.spec_from_file_location("fa447b_helpers", p)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load same-height helpers")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def replace_once(text: str, old: str, new: str, name: str) -> tuple[str, dict]:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{name}: expected once, found {count}")
    result = text.replace(old, new)
    if line_count(result) != line_count(text):
        raise RuntimeError(f"{name}: changed file height")
    return result, {"repair": name, "applied": 1, "same_height": True}


def build(champion: str, variant: str) -> tuple[str, list[dict]]:
    text = champion
    repairs: list[dict] = []
    if variant == "champion":
        return text, repairs
    if variant in {"proof_explicit", "proof_explicit_height"}:
        text, r = replace_once(text, CHAMPION_BLOCK, PROOF_EXPLICIT,
                               "proof_local_explicit_GL_invariant")
        repairs.append(r)
        if variant.endswith("_height"):
            text, r = replace_once(text, HEIGHT_OLD, HEIGHT_NEW, "height_membership")
            repairs.append(r)
        return text, repairs
    if variant in {"namespace_explicit", "namespace_explicit_height"}:
        text, r = replace_once(text, CHAMPION_BLOCK, ORIGINAL_BLOCK,
                               "restore_theorem_body_for_namespace_instances")
        repairs.append(r)
        text, r = replace_once(text, NAMESPACE_ANCHOR, NAMESPACE_EXPLICIT,
                               "namespace_explicit_GL_invariant")
        repairs.append(r)
        text, r = replace_once(text, MEASURABLE_ANCHOR, MEASURABLE_INSTANCE,
                               "namespace_MeasurableConstSMul")
        repairs.append(r)
        if variant.endswith("_height"):
            text, r = replace_once(text, HEIGHT_OLD, HEIGHT_NEW, "height_membership")
            repairs.append(r)
        return text, repairs
    raise RuntimeError(f"unknown variant: {variant}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", required=True, choices=sorted(EXPECTED_OUTPUTS))
    ap.add_argument("--output-dir", required=True)
    args = ap.parse_args()
    out = ROOT / args.output_dir
    out.mkdir(parents=True, exist_ok=True)

    champion = SOURCE.read_text()
    actual_champion = sha_text(champion)
    if actual_champion != CHAMPION_SHA:
        raise RuntimeError(f"checked-in source SHA {actual_champion} != {CHAMPION_SHA}")
    if line_count(champion) != EXPECTED_LINES:
        raise RuntimeError("champion line count mismatch")
    helpers = load_helpers()
    _, _, _, old_header = helpers.declaration_span(champion, TARGET)
    candidate, repairs = build(champion, args.variant)
    _, _, _, new_header = helpers.declaration_span(candidate, TARGET)
    if old_header != new_header:
        raise RuntimeError("actualEdgeAmbientParam_hasDerivAt header changed")
    if line_count(candidate) != EXPECTED_LINES:
        raise RuntimeError("candidate line count mismatch")
    candidate_sha = sha_text(candidate)
    if candidate_sha != EXPECTED_OUTPUTS[args.variant]:
        raise RuntimeError(f"unexpected candidate SHA {candidate_sha}")
    audit = dict(helpers.forbidden_counts(candidate))
    if any(audit.values()):
        raise RuntimeError(f"forbidden audit failed: {audit}")

    SOURCE.write_text(candidate)
    (out / "Mock2_FunctionalAnalysis-champion.lean").write_text(champion)
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_text(candidate)
    meta = {
        "variant": args.variant,
        "baseline_sha256": CHAMPION_SHA,
        "candidate_sha256": candidate_sha,
        "line_count": EXPECTED_LINES,
        "target_declaration": TARGET,
        "target_header_sha256": sha_text(old_header),
        "parent_direct_first_error": {
            "line": 32592,
            "column": 5,
            "declaration": "selectedHalfOpenTile_ae_eq_openTile",
            "declaration_index": 2671,
        },
        "explicit_instance": INSTANCE_NAME,
        "repairs": repairs,
        "baseline_forbidden_counts": dict(helpers.forbidden_counts(champion)),
        "candidate_forbidden_counts": audit,
    }
    (out / "CANDIDATE.json").write_text(json.dumps(meta, indent=2) + "\n")
    print(json.dumps(meta, indent=2))


if __name__ == "__main__":
    main()
