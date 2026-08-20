#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,sys

BASE_SHA256='f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210'
BASE_BLOB='bd28d0436230a8f0bcb01806dac01787542256b8'

SIG='''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
'''

CURVE='''  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    have hx : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
      simpa [Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff
    have hconst : ContDiff ℝ ∞
        (fun _ : ℝ =>
          (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=
      contDiff_const
    simpa [actualFixedPhaseHorizontalHorocyclePoint] using hx.add hconst
'''

SL_SETUP='''  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
'''+CURVE+'''  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) :=
    ((contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 0) : ℂ))).mul hcurve).add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 1) : ℂ)))
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) :=
    ((contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 0) : ℂ))).mul hcurve).add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 1) : ℂ)))
  have hden : ∀ x : ℝ,
      ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
        (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) ≠ 0 := by
    intro x
    simpa [UpperHalfPlane.denom, sigma] using
      (UpperHalfPlane.denom_ne_zero
        ((gammaTwoCuspScaling kappa : SL(2, ℤ)) : GL (Fin 2) ℝ)
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
'''

GL_SETUP='''  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by simp [g]
'''+CURVE+'''  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa [UpperHalfPlane.num] using
      ((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 0 0 : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 0 1 : ℂ)))
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa [UpperHalfPlane.denom] using
      ((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 1 0 : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 1 1 : ℂ)))
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) ≠ 0 := by
    intro x
    simpa using
      (UpperHalfPlane.denom_ne_zero g
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
'''

SECOND_SIMPA='''

/-- Restriction of every actual real-smooth automorphic core section to a
named cusp horocycle is a real `C-infinity` function of the boundary
parameter. -/
theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ContDiff ℝ ∞
      (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) := by
  have hu : ContDiffOn ℝ ∞
      (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      UpperHalfPlane.upperHalfPlaneSet :=
    (u : SmoothQuotientCompactFunction).1.2
  have hcomp := hu.comp_contDiff
    (actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y)
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    upperLift, Function.comp_def] using hcomp
'''

SECOND_CHANGE='''

/-- Restriction of every actual real-smooth automorphic core section to a
named cusp horocycle is a real `C-infinity` function of the boundary
parameter. -/
theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ContDiff ℝ ∞
      (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) := by
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
        (actualFixedPhaseCuspHorocyclePoint kappa Y x : ℂ))
  exact (u : SmoothQuotientCompactFunction).1.2.comp_contDiff
    (actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y)
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
'''

FIRST={}
FIRST['sl_have_div']=SIG+SL_SETUP+'''  simpa [actualFixedPhaseCuspHorocyclePoint, sigma,
      UpperHalfPlane.coe_specialLinearGroup_apply] using
    hnum.div hdenDiff hden
'''
FIRST['sl_have_mul_inv']=SIG+SL_SETUP+'''  have hinv : ContDiff ℝ ∞
      (fun x : ℝ =>
        (((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ)))⁻¹) :=
    hdenDiff.inv hden
  have hmul := hnum.mul hinv
  simpa [actualFixedPhaseCuspHorocyclePoint, sigma,
      UpperHalfPlane.coe_specialLinearGroup_apply, div_eq_mul_inv] using hmul
'''
FIRST['sl_change_div']=SIG+SL_SETUP+'''  change ContDiff ℝ ∞
    (fun x : ℝ =>
      ((algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) /
        ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ)))
  exact hnum.div hdenDiff hden
'''
FIRST['gl_numden_div']=SIG+GL_SETUP+'''  have hfrac := hnum.div hdenDiff hden
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
'''
FIRST['gl_simpa_div']=SIG+GL_SETUP+'''  have hfrac := hnum.div hdenDiff hden
  simpa [actualFixedPhaseCuspHorocyclePoint, g,
      UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
'''
FIRST['cases_simp_funprop']=SIG+'''  cases kappa <;>
    simp [actualFixedPhaseCuspHorocyclePoint,
      gammaTwoCuspScaling,
      actualFixedPhaseHorizontalHorocyclePoint] <;>
    fun_prop
'''
FIRST['cases_simp_transparency']='''set_option backward.isDefEq.respectTransparency false in
'''+SIG+'''  cases kappa <;>
    simp [actualFixedPhaseCuspHorocyclePoint,
      gammaTwoCuspScaling,
      actualFixedPhaseHorizontalHorocyclePoint] <;>
    fun_prop
'''
FIRST['direct_apply_div']=SIG+'''  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
'''+CURVE+'''  have hden : ∀ x : ℝ,
      ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
        (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) ≠ 0 := by
    intro x
    simpa [UpperHalfPlane.denom, sigma] using
      (UpperHalfPlane.denom_ne_zero
        ((gammaTwoCuspScaling kappa : SL(2, ℤ)) : GL (Fin 2) ℝ)
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
  simp only [actualFixedPhaseCuspHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  apply ContDiff.div
  · exact ((contDiff_const : ContDiff ℝ ∞
      (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 0) : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 1) : ℂ)))
  · exact ((contDiff_const : ContDiff ℝ ∞
      (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 0) : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 1) : ℂ)))
  · exact hden
'''
FIRST['transparency_sl_div']='''set_option backward.isDefEq.respectTransparency false in
'''+FIRST['sl_have_div']

VARIANTS={}
for name,proof in FIRST.items():
    VARIANTS[name+'_simpa']=proof+SECOND_SIMPA
for name in ['sl_have_div','sl_change_div','cases_simp_funprop','direct_apply_div']:
    VARIANTS[name+'_change']=FIRST[name]+SECOND_CHANGE

REGION_RE=re.compile(r'(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?(?=^/-- Every actual smooth trace is Lipschitz)')

def blob(raw):return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
def audit(t):return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}
def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS:raise SystemExit('usage: script VARIANT QYM.lean; variants='+','.join(sorted(VARIANTS)))
    v,p=sys.argv[1],Path(sys.argv[2]);before=p.read_bytes()
    if hashlib.sha256(before).hexdigest()!=BASE_SHA256 or blob(before)!=BASE_BLOB:raise SystemExit('GB85 identity mismatch')
    t=before.decode();a0=audit(t);ms=list(REGION_RE.finditer(t))
    if len(ms)!=1:raise SystemExit(f'region count={len(ms)}')
    m=ms[0];u=t[:m.start()]+VARIANTS[v].rstrip()+'\n\n'+t[m.end():];a1=audit(u)
    if a1!=a0:raise SystemExit(f'forbidden delta {a0}->{a1}')
    p.write_text(u);after=p.read_bytes();marker='/-- Every actual smooth trace is Lipschitz';idx=u.find(marker)
    print(json.dumps({'schema':'qym-gb85-c2-matrix-v3','variant':v,'input_sha256':BASE_SHA256,'input_blob':BASE_BLOB,'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':blob(after),'bytes':len(after),'lf':after.count(b'\n'),'gate_line':u.count('\n',0,idx)+1,'forbidden':a1},indent=2,sort_keys=True))
if __name__=='__main__':main()
