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
CHAMPION_SHA256 = "c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626"
EXPECTED_LINES = 60453
TARGET = "actualEdgeAmbientParam_hasDerivAt"

EXPECTED_OUTPUTS = {
    "champion": CHAMPION_SHA256,
    "height_only": "07afb89ecce1d0b6be4c15bb6752a6907a4594d6a37f6b516868b09cd61bc43d",
    "proof_invariant": "e77d57a492f15ef79bb30ed2d5a73822a91329a29c24578234787cfd296dc25d",
    "proof_invariant_height": "d26926c92ae5be13464a43a4dbadcc4c52a0240e0312f75795c860418b57beef",
    "namespace_both": "5b5d3e956d5e3e8a93a0bf355edf59c10204676b5cf44c7b934dfb12a9552afa",
    "namespace_both_height": "7672a704456be636790b2984bb2de8564414fa9a701059d7c7ab9ed9922dabe1",
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
PROOF_INVARIANT_BLOCK = """      gammaTwoCosetRep q • ModularGroup.fdo := by
  letI : MeasurableConstSMul SL(2, ℤ) ℍ := ⟨fun g ↦ (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩
  letI : MeasureTheory.SMulInvariantMeasure SL(2, ℤ) ℍ hyperbolicMeasure := ⟨fun g s hs ↦ by change hyperbolicMeasure ((fun z : ℍ => (g : GL (Fin 2) ℝ) • z) ⁻¹' s) = hyperbolicMeasure s; exact (inferInstance : MeasureTheory.SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ hyperbolicMeasure).1 (g : GL (Fin 2) ℝ) hs⟩
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq (gammaTwoCosetRep q)
    (measurePreserving_smul (gammaTwoCosetRep q)⁻¹ hyperbolicMeasure).quasiMeasurePreserving modularHalfOpenTile_ae_eq_fdo
"""
NAMESPACE_ANCHOR = """namespace GammaTwoGlobalStokesBridge

open MeasureTheory Set Function Topology Filter
"""
NAMESPACE_SMUL = """namespace GammaTwoGlobalStokesBridge
local instance gammaTwoGlobalStokesBridgeSMulInvariantMeasure : MeasureTheory.SMulInvariantMeasure SL(2, ℤ) ℍ hyperbolicMeasure := ⟨fun g s hs ↦ by change hyperbolicMeasure ((fun z : ℍ => (g : GL (Fin 2) ℝ) • z) ⁻¹' s) = hyperbolicMeasure s; exact (inferInstance : MeasureTheory.SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ hyperbolicMeasure).1 (g : GL (Fin 2) ℝ) hs⟩
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
    spec = importlib.util.spec_from_file_location("fa447_helpers", p)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load helper module")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def replace_once(text: str, old: str, new: str, name: str) -> tuple[str, dict]:
    n = text.count(old)
    if n != 1:
        raise RuntimeError(f"{name}: expected once, found {n}")
    out = text.replace(old, new)
    if line_count(out) != line_count(text):
        raise RuntimeError(f"{name}: changed file height")
    return out, {"repair": name, "applied": 1, "same_height": True}


def build(champion: str, variant: str) -> tuple[str, list[dict]]:
    text = champion
    repairs: list[dict] = []
    if variant == "champion":
        return text, repairs
    if variant == "height_only":
        text, r = replace_once(text, HEIGHT_OLD, HEIGHT_NEW, "height_membership")
        return text, [r]
    if variant in {"proof_invariant", "proof_invariant_height"}:
        text, r = replace_once(text, CHAMPION_BLOCK, PROOF_INVARIANT_BLOCK,
                               "proof_local_SMulInvariantMeasure")
        repairs.append(r)
        if variant.endswith("_height"):
            text, r = replace_once(text, HEIGHT_OLD, HEIGHT_NEW, "height_membership")
            repairs.append(r)
        return text, repairs
    if variant in {"namespace_both", "namespace_both_height"}:
        text, r = replace_once(text, CHAMPION_BLOCK, ORIGINAL_BLOCK,
                               "restore_theorem_body_for_namespace_instances")
        repairs.append(r)
        text, r = replace_once(text, NAMESPACE_ANCHOR, NAMESPACE_SMUL,
                               "namespace_local_SMulInvariantMeasure")
        repairs.append(r)
        text, r = replace_once(text, MEASURABLE_ANCHOR, MEASURABLE_INSTANCE,
                               "namespace_local_MeasurableConstSMul")
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
    if sha_text(champion) != CHAMPION_SHA256:
        raise RuntimeError(f"unexpected checked-in champion SHA: {sha_text(champion)}")
    if line_count(champion) != EXPECTED_LINES:
        raise RuntimeError("champion line count mismatch")
    helpers = load_helpers()
    _, _, _, old_header = helpers.declaration_span(champion, TARGET)
    candidate, repairs = build(champion, args.variant)
    _, _, _, new_header = helpers.declaration_span(candidate, TARGET)
    if old_header != new_header:
        raise RuntimeError("target theorem header changed")
    actual = sha_text(candidate)
    if actual != EXPECTED_OUTPUTS[args.variant]:
        raise RuntimeError(f"unexpected output SHA {actual}")
    if line_count(candidate) != EXPECTED_LINES:
        raise RuntimeError("candidate line count mismatch")
    audit = dict(helpers.forbidden_counts(candidate))
    if any(audit.values()):
        raise RuntimeError(f"forbidden audit failed: {audit}")

    SOURCE.write_text(candidate)
    (out / "Mock2_FunctionalAnalysis-champion.lean").write_text(champion)
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_text(candidate)
    meta = {
        "variant": args.variant,
        "baseline_sha256": CHAMPION_SHA256,
        "candidate_sha256": actual,
        "line_count": EXPECTED_LINES,
        "target_declaration": TARGET,
        "target_header_sha256": sha_text(old_header),
        "parent_direct_first_error": {
            "line": 32592,
            "column": 5,
            "declaration": "selectedHalfOpenTile_ae_eq_openTile",
            "declaration_index": 2671,
        },
        "repairs": repairs,
        "baseline_forbidden_counts": dict(helpers.forbidden_counts(champion)),
        "candidate_forbidden_counts": audit,
    }
    (out / "CANDIDATE.json").write_text(json.dumps(meta, indent=2) + "\n")
    print(json.dumps(meta, indent=2))


if __name__ == "__main__":
    main()
