#!/usr/bin/env python3
from pathlib import Path
import hashlib, re, sys

EXPECTED_INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED_OUTPUT_SHA256 = "4ef27f9448b87111daceef6216d53fc2b1daaaba912c7b9362065f3a2d4f9d77"
EXPECTED_OUTPUT_BLOB = "1e60515b7c0d6fcdc827a049c26235ff418817e0"

p = Path(sys.argv[1])
raw = p.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED_INPUT_SHA256
s = raw.decode()

replacements = [
    (
        """local instance conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth
""",
        """private theorem conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth
""",
    ),
    (
        """local instance conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
""",
        """private theorem conditionalHasGroupoidComplex :
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
        """theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

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
        """theorem interiorStageInclusion_contMDiff
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
    assert s.count(old) == 1, (old[:100], s.count(old))
    s = s.replace(old, new, 1)

p.write_text(s)
raw = p.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED_OUTPUT_SHA256
blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
assert blob == EXPECTED_OUTPUT_BLOB, blob
text = raw.decode()
forbidden = {
    "sorry": len(re.findall(r"\bsorry\b", text)),
    "admit": len(re.findall(r"\badmit\b", text)),
    "native_decide": len(re.findall(r"\bnative_decide\b", text)),
    "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
    "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
    "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
    "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
}
assert not any(forbidden.values()), forbidden
print(EXPECTED_OUTPUT_SHA256)
