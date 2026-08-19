#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,sys

BASELINE_SHA256='313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e'
BASELINE_BLOB='ff49510790dd7ca136bf34c3ec7150617ee1c241'
VARIANTS={'helper_letI','inline_letI'}

OLD='''section ConditionalSmoothAtlas

variable (hSmooth : SmoothTransitionResidual)

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

local instance conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient

/-- Groupoid composition turns the single transition residual into the usual
complex smooth-atlas compatibility condition. -/
local instance conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
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
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

local instance conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual
'''

HELPER='''section ConditionalSmoothAtlas

variable (hSmooth : SmoothTransitionResidual)

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

private theorem conditionalHasGroupoidH_proof :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient

/-- Groupoid composition turns the single transition residual into the usual
complex smooth-atlas compatibility condition. -/
private theorem conditionalHasGroupoidComplex_proof :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH_proof hSmooth
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
    conditionalHasGroupoidComplex_proof hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
'''

INLINE='''section ConditionalSmoothAtlas

variable (hSmooth : SmoothTransitionResidual)

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient

/-- Conditional construction of the genuine smooth quotient manifold.  The
only hypothesis is `SmoothTransitionResidual`; no additional topological or
atlas premise is hidden in this theorem. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
    apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
    intro e he
    rw [isLocalStructomorphOn_contDiffGroupoid_iff]
    change
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
    exact he
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
'''

OLD_INTERIOR='''theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) :=
  contMDiff_inclusion (interiorStage_mono hYZ)
'''

INTERIOR_HELPER='''theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex_proof hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)
'''

INTERIOR_INLINE='''theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
    apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
    intro e he
    rw [isLocalStructomorphOn_contDiffGroupoid_iff]
    change
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
    exact he
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)
'''

def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def audit(t): return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}

def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS: raise SystemExit('usage: qym_c06_variants.py VARIANT QYM.lean')
    v,p=sys.argv[1],Path(sys.argv[2]); before=p.read_bytes()
    if hashlib.sha256(before).hexdigest()!=BASELINE_SHA256 or blob(before)!=BASELINE_BLOB: raise SystemExit('baseline mismatch')
    text=before.decode(); a0=audit(text); head=HELPER if v=='helper_letI' else INLINE; tail=INTERIOR_HELPER if v=='helper_letI' else INTERIOR_INLINE
    for label,old,new in [('conditional block',OLD,head),('interior theorem',OLD_INTERIOR,tail)]:
        if text.count(old)!=1: raise SystemExit(f'{label} count={text.count(old)}')
        text=text.replace(old,new,1)
    a1=audit(text)
    if a1!=a0: raise SystemExit(f'forbidden delta {a0}->{a1}')
    p.write_text(text); after=p.read_bytes()
    print(json.dumps({'schema':'qym-c06-v1','variant':v,'input_sha256':BASELINE_SHA256,'input_blob':BASELINE_BLOB,'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':blob(after),'bytes':len(after),'lf':after.count(b'\n'),'fixed_producers_targeted':['conditionalHasGroupoidH','conditionalHasGroupoidComplex','gammaTwoQuotient_isManifold_of_smoothTransitionResidual','interiorStageInclusion_contMDiff'],'forbidden_before':a0,'forbidden_after':a1},indent=2,sort_keys=True))
if __name__=='__main__': main()
