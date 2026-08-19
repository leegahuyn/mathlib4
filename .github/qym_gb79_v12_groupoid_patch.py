#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

ATLAS_RE = re.compile(r"(?ms)^section ConditionalSmoothAtlas\b.*?^end ConditionalSmoothAtlas\s*")
ATLAS_BLOCK = r'''section ConditionalSmoothAtlas

variable (hSmooth : SmoothTransitionResidual)
include hSmooth

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

private theorem conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient

/-- Groupoid composition turns the single transition residual into the usual
complex smooth-atlas compatibility condition. -/
private theorem conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he

/-- Conditional construction of the genuine smooth quotient manifold.  The
only hypothesis is `SmoothTransitionResidual`; no additional topological or
atlas premise is hidden in this theorem. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

private theorem conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth

/-! ## 5. Open stage interiors -/

/-- The largest open submanifold canonically contained in the intrinsic closed
stage.  The closed subtype itself is not an `Opens`, so Mathlib's manifold
inclusion theorem does not apply directly to `IStage.X Y`. -/
def interiorStage (Y : ℝ) : TopologicalSpace.Opens GammaTwoQuotient :=
  ⟨interior (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y), isOpen_interior⟩

/-- Monotonicity of the closed stages induces monotonicity of their open
interiors. -/
theorem interiorStage_mono {Y Z : ℝ} (hYZ : Y ≤ Z) :
    interiorStage Y ≤ interiorStage Z :=
  interior_mono (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet_monotone hYZ)

/-- The canonical open-stage inclusion. -/
def interiorStageInclusion {Y Z : ℝ} (hYZ : Y ≤ Z) :
    interiorStage Y → interiorStage Z :=
  TopologicalSpace.Opens.inclusion (interiorStage_mono hYZ)

/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    conditionalIsManifold hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

def audit(text):
    return {
      "sorry": len(re.findall(r"\bsorry\b", text)),
      "admit": len(re.findall(r"\badmit\b", text)),
      "native_decide": len(re.findall(r"\bnative_decide\b", text)),
      "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
      "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
      "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
      "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }

def main():
    if len(sys.argv)!=2: raise SystemExit("usage: groupoid_patch QYM.lean")
    p=Path(sys.argv[1]); before=p.read_bytes(); text=before.decode("utf-8"); a0=audit(text)
    ms=list(ATLAS_RE.finditer(text))
    if len(ms)!=1: raise SystemExit(f"ConditionalSmoothAtlas matches={len(ms)}")
    m=ms[0]; text=text[:m.start()] + ATLAS_BLOCK.rstrip() + "\n\n" + text[m.end():]
    a1=audit(text)
    if a1!=a0: raise SystemExit(f"forbidden delta {a0}->{a1}")
    p.write_text(text,encoding="utf-8"); after=p.read_bytes()
    print(json.dumps({"input_sha256":hashlib.sha256(before).hexdigest(),"candidate_sha256":hashlib.sha256(after).hexdigest(),"forbidden":a1},indent=2,sort_keys=True))

if __name__=="__main__": main()
