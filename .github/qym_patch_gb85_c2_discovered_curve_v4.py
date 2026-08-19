#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,sys

BASE_SHA256='f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210'
BASE_BLOB='bd28d0436230a8f0bcb01806dac01787542256b8'
VARIANTS={
    f'i{i}_{call}_{frac}_{second}'
    for i in range(6)
    for call in ('pos','named','exact')
    for frac in ('div','mul_inv')
    for second in ('simpa','change')
}
REGION_RE=re.compile(r'(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?(?=^/-- Every actual smooth trace is Lipschitz)')
DECL_RE=re.compile(r'(?m)^\s*(?:theorem|lemma)\s+([^\s(:{]+)')

def blob(raw):return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
def audit(t):return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}

def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS:raise SystemExit('usage: script VARIANT QYM.lean')
    variant,path=sys.argv[1],Path(sys.argv[2]);before=path.read_bytes()
    if hashlib.sha256(before).hexdigest()!=BASE_SHA256 or blob(before)!=BASE_BLOB:raise SystemExit('GB85 identity mismatch')
    text=before.decode();target=text.find('theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff')
    if target<0:raise SystemExit('target theorem missing')
    prefix=text[:target]
    names=[]
    for m in DECL_RE.finditer(prefix):
        name=m.group(1);low=name.lower()
        if 'horizontalhorocyclepoint' in low and ('contdiff' in low or 'smooth' in low):names.append(name)
    # Prefer closest preceding and exact coe/ContDiff spellings.
    names=list(dict.fromkeys(reversed(names)))
    i_s,call,frac,second=variant.split('_',3);idx=int(i_s[1:])
    if idx>=len(names):raise SystemExit(f'curve lemma index {idx} unavailable; discovered={names}')
    curve_lemma=names[idx]
    if call=='pos':curve_term=f'{curve_lemma} Y'
    elif call=='named':curve_term=f'{curve_lemma} (Y := Y)'
    else:curve_term=f'{curve_lemma} Y'
    curve_proof=(f'  have hcurve : ContDiff ℝ ∞\n'
                 f'      (fun x : ℝ =>\n'
                 f'        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by\n')
    if call=='exact':curve_proof+=f'    exact {curve_term}\n'
    else:curve_proof+=f'    simpa using {curve_term}\n'
    first='''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
'''+curve_proof+'''  have hnum : ContDiff ℝ ∞
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
    if frac=='div':
        first+='''  have hfrac := hnum.div hdenDiff hden
  simpa [actualFixedPhaseCuspHorocyclePoint, sigma,
      UpperHalfPlane.coe_specialLinearGroup_apply] using hfrac
'''
    else:
        first+='''  have hinv := hdenDiff.inv hden
  have hfrac := hnum.mul hinv
  simpa [actualFixedPhaseCuspHorocyclePoint, sigma,
      UpperHalfPlane.coe_specialLinearGroup_apply, div_eq_mul_inv] using hfrac
'''
    if second=='simpa':
        second_proof='''

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
    else:
        second_proof='''

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
    ms=list(REGION_RE.finditer(text))
    if len(ms)!=1:raise SystemExit(f'region count={len(ms)}')
    m=ms[0];after_text=text[:m.start()]+(first+second_proof).rstrip()+'\n\n'+text[m.end():];a0,a1=audit(text),audit(after_text)
    if a1!=a0:raise SystemExit(f'forbidden delta {a0}->{a1}')
    path.write_text(after_text);after=path.read_bytes();marker='/-- Every actual smooth trace is Lipschitz';mi=after_text.find(marker)
    print(json.dumps({'schema':'qym-gb85-c2-discovered-v4','variant':variant,'curve_lemma':curve_lemma,'discovered_curve_lemmas':names,'input_sha256':BASE_SHA256,'input_blob':BASE_BLOB,'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':blob(after),'bytes':len(after),'lf':after.count(b'\n'),'gate_line':after_text.count('\n',0,mi)+1,'forbidden':a1},indent=2,sort_keys=True))
if __name__=='__main__':main()
