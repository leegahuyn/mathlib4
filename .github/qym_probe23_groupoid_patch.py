#!/usr/bin/env python3
from pathlib import Path
import hashlib
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
OUTPUT_SHA256 = "5282a9223e30e2ea3f14b310a3902d10d662fd98c0968d12b1a8d984dabda5d0"
OUTPUT_BLOB = "0b84f1f5cdf88925f69134c50827e371353c79ca"

path = Path(sys.argv[1])
raw = path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
text = raw.decode("utf-8")

replacements = [
    (
        """local instance conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth
""",
        """include hSmooth in
private theorem conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth
""",
    ),
    (
        """local instance conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
""",
        """include hSmooth in
private theorem conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
""",
    ),
    (
        """theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

local instance conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual
""",
        """include hSmooth in
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

include hSmooth in
private theorem conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth
""",
    ),
    (
        """theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) :=
  contMDiff_inclusion (interiorStage_mono hYZ)
""",
        """include hSmooth in
theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    conditionalIsManifold hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)
""",
    ),
]

for old, new in replacements:
    assert text.count(old) == 1, (old[:100], text.count(old))
    text = text.replace(old, new, 1)

path.write_text(text, encoding="utf-8")
result = path.read_bytes()
assert hashlib.sha256(result).hexdigest() == OUTPUT_SHA256
blob = hashlib.sha1(b"blob " + str(len(result)).encode() + b"\0" + result).hexdigest()
assert blob == OUTPUT_BLOB, blob

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
print(OUTPUT_SHA256)
