#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,sys

BASELINE_SHA256='313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e'
BASELINE_BLOB='ff49510790dd7ca136bf34c3ec7150617ee1c241'
VARIANTS={'direct_div','mul_inv_using_bang','direct_div_cases'}

OLD_INVERSE='''    rw [hfun]
    rw [div_eq_mul_inv]
    exact heta.mul (hetaShift.inv
      (fun x => ModularForm.eta_ne_zero
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2))
'''

DIRECT_DIV='''    rw [hfun]
    exact heta.div hetaShift
      (fun x => ModularForm.eta_ne_zero
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2)
'''

MUL_INV_BANG='''    rw [hfun]
    simpa only [div_eq_mul_inv] using!
      heta.mul (hetaShift.inv
        (fun x => ModularForm.eta_ne_zero
          (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2))
'''

OLD_POW='''    generalize hk : (2 : ℤ) * n = k
    cases k with
    | ofNat m =>
        convert hden.pow m using 1
        funext x
        rw [hk, zpow_natCast]
    | negSucc m =>
        convert (hden.pow (m + 1)).inv
          (fun x => pow_ne_zero _ (hdenNe x)) using 1
        funext x
        rw [hk, zpow_negSucc]
'''

POW_USING_BANG='''    generalize hk : (2 : ℤ) * n = k
    cases k with
    | ofNat m =>
        simpa only [hk, zpow_natCast] using! hden.pow m
    | negSucc m =>
        simpa only [hk, zpow_negSucc] using!
          (hden.pow (m + 1)).inv
            (fun x => pow_ne_zero _ (hdenNe x))
'''

POW_CASE_EQ='''    cases hk : (2 : ℤ) * n with
    | ofNat m =>
        simpa only [hk, zpow_natCast] using! hden.pow m
    | negSucc m =>
        simpa only [hk, zpow_negSucc] using!
          (hden.pow (m + 1)).inv
            (fun x => pow_ne_zero _ (hdenNe x))
'''

def blob(raw): return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
def audit(t): return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}

def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS: raise SystemExit('usage: qym_c04_variants.py VARIANT QYM.lean')
    variant,path=sys.argv[1],Path(sys.argv[2]); before=path.read_bytes()
    if hashlib.sha256(before).hexdigest()!=BASELINE_SHA256 or blob(before)!=BASELINE_BLOB: raise SystemExit('baseline mismatch')
    text=before.decode(); a0=audit(text)
    inverse = MUL_INV_BANG if variant=='mul_inv_using_bang' else DIRECT_DIV
    powproof = POW_CASE_EQ if variant=='direct_div_cases' else POW_USING_BANG
    for label,old,new in [('inverse',OLD_INVERSE,inverse),('pow',OLD_POW,powproof)]:
        if text.count(old)!=1: raise SystemExit(f'{label} count={text.count(old)}')
        text=text.replace(old,new,1)
    a1=audit(text)
    if a1!=a0: raise SystemExit(f'forbidden delta {a0}->{a1}')
    path.write_text(text); after=path.read_bytes()
    print(json.dumps({'schema':'qym-c04-v1','variant':variant,'input_sha256':BASELINE_SHA256,'input_blob':BASELINE_BLOB,'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':blob(after),'bytes':len(after),'lf':after.count(b'\n'),'fixed_producers_targeted':['actualFixedPhaseCuspBoundaryTransition_contDiff'],'forbidden_before':a0,'forbidden_after':a1},indent=2,sort_keys=True))
if __name__=='__main__': main()
