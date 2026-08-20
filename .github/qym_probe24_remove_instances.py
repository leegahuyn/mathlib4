#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED = {
    "remove-inner": {
        "sha256": "4652c2604dedb92080aceea4bdbd09e99ce83587c8b4f7953688a38cd2722c12",
        "blob": "1a94792fb1c6fff0c155bfd9e296a26ff146196f",
        "label": "inferred-opnorm-plus-groupoid",
    },
    "remove-both": {
        "sha256": "3678d6c5e0f65caeb03e762ed3f7a5fe97ef8fb049699b09d0e99fbcda4fcf94",
        "blob": "3391dbf58b639d003da21a83ab4de684f013a21f",
        "label": "inferred-opnorm-plus-groupoid-plus-gamma",
    },
}

OLD_OPNORM = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""
NEW_OPNORM = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""

OLD_HHALF = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance
"""
NEW_HHALF = """noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  (ActualFixedPhaseHhalfTraceCompletion n Y).innerProductSpace
"""

OLD_GROUP_H = """local instance conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth
"""
NEW_GROUP_H = """include hSmooth
private theorem conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth
omit hSmooth
"""

OLD_GROUP_COMPLEX = """local instance conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
"""
NEW_GROUP_COMPLEX = """include hSmooth
private theorem conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
"""

OLD_GROUP_COMPLEX_END = """  exact he

/-- Conditional construction of the genuine smooth quotient manifold."""
NEW_GROUP_COMPLEX_END = """  exact he
omit hSmooth

/-- Conditional construction of the genuine smooth quotient manifold."""

OLD_MANIFOLD = """theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

local instance conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual
"""
NEW_MANIFOLD = """include hSmooth
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
omit hSmooth

include hSmooth
private theorem conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth
omit hSmooth
"""

OLD_INCLUSION = """theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) :=
  contMDiff_inclusion (interiorStage_mono hYZ)
"""
NEW_INCLUSION = """include hSmooth
theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    conditionalIsManifold hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)
omit hSmooth
"""

OLD_GAMMA = """    all_goals
      norm_num [CongruenceSubgroup.Gamma_mem,
        ModularGroup.S, ModularGroup.T] at hGamma
"""
NEW_GAMMA = """    all_goals
      rw [CongruenceSubgroup.Gamma_mem] at hGamma
      norm_num [ModularGroup.S, ModularGroup.T] at hGamma
"""


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, (old[:120], text.count(old))
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_probe24_remove_instances.py VARIANT QYM.lean")
    variant, file_name = sys.argv[1], sys.argv[2]
    if variant not in EXPECTED:
        raise SystemExit(f"unknown variant: {variant}")

    path = Path(file_name)
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    text = raw.decode("utf-8")

    text = replace_once(text, OLD_OPNORM, NEW_OPNORM)
    text = replace_once(text, OLD_HHALF, NEW_HHALF)
    text = replace_once(text, OLD_GROUP_H, NEW_GROUP_H)
    text = replace_once(text, OLD_GROUP_COMPLEX, NEW_GROUP_COMPLEX)
    text = replace_once(text, OLD_GROUP_COMPLEX_END, NEW_GROUP_COMPLEX_END)
    text = replace_once(text, OLD_MANIFOLD, NEW_MANIFOLD)
    text = replace_once(text, OLD_INCLUSION, NEW_INCLUSION)
    if variant == "remove-both":
        text = replace_once(text, OLD_GAMMA, NEW_GAMMA)

    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    sha256 = hashlib.sha256(result).hexdigest()
    blob = git_blob(result)
    assert sha256 == EXPECTED[variant]["sha256"], (sha256, EXPECTED[variant]["sha256"])
    assert blob == EXPECTED[variant]["blob"], (blob, EXPECTED[variant]["blob"])

    decoded = result.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    assert not any(forbidden.values()), forbidden

    print(json.dumps({
        "schema": "qym-probe28-producer-matrix-v1",
        "variant": variant,
        "label": EXPECTED[variant]["label"],
        "input_sha256": INPUT_SHA256,
        "candidate_sha256": sha256,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
