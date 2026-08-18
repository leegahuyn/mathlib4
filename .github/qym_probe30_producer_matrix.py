#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED = {
    "groupoid": {
        "sha256": "39872ae016c9e1e42679508df70ed9e9e6998d71d522c447fa56b26160885c65",
        "blob": "4186c5226196164debfa95c281aa83805bf5d618",
    },
    "groupoid-gamma": {
        "sha256": "eddc4a1458a121a7ef310ac18ec87b4563b9f846a22cfc46b777d2369454178c",
        "blob": "1308138597e2e2ee6e275bf14a2c26ad9b04483c",
    },
}

OLD_OPNORM = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""
NEW_OPNORM = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) : _ :=
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


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, (old[:100], text.count(old))
    return text.replace(old, new, 1)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    variant, file_name = sys.argv[1], sys.argv[2]
    assert variant in EXPECTED
    path = Path(file_name)
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    text = raw.decode("utf-8")
    for old, new in [
        (OLD_OPNORM, NEW_OPNORM),
        (OLD_HHALF, NEW_HHALF),
        (OLD_GROUP_H, NEW_GROUP_H),
        (OLD_GROUP_COMPLEX, NEW_GROUP_COMPLEX),
        (OLD_GROUP_COMPLEX_END, NEW_GROUP_COMPLEX_END),
        (OLD_MANIFOLD, NEW_MANIFOLD),
        (OLD_INCLUSION, NEW_INCLUSION),
    ]:
        text = replace_once(text, old, new)
    if variant == "groupoid-gamma":
        text = replace_once(text, OLD_GAMMA, NEW_GAMMA)
    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    sha = hashlib.sha256(result).hexdigest()
    blob = git_blob(result)
    assert sha == EXPECTED[variant]["sha256"], (sha, EXPECTED[variant]["sha256"])
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
        "schema": "qym-probe30-producer-matrix-v1",
        "variant": variant,
        "candidate_sha256": sha,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
