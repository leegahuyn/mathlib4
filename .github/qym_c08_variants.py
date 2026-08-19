#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,sys
BASELINE_SHA256='830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217'
BASELINE_BLOB='e796aa6ae9f01965116902a9345ed69f81bcfc42'
VARIANTS={'dense_induction','explicit_args','finite_heartbeats'}
OLD='''set_option maxHeartbeats 2000000 in
/-- A concrete smooth-core constant also controls the dense extension on the
whole old graph completion. -/
theorem actualFixedPhaseOldGraphToProductCollarExtension_norm_le
    (n : ℤ) (Y : ℝ) (C0 : ℝ)
    (hC0 : ∀ u : InverseEtaFixedPhaseCore n,
      ‖actualFixedPhaseSmoothCoreToProductCollarProfile n Y u‖ ≤
        C0 * ‖coreMap n u‖)
    (x : GraphSobolevCompletion n) :
    ‖actualFixedPhaseOldGraphToProductCollarExtension n Y x‖ ≤
      C0 * ‖x‖ := by
  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n
  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n
  exact LinearMap.norm_extendOfNorm_apply_le
    (denseRange_coreMap n) C0 hC0 x
'''
HEAD='''/-- A concrete smooth-core constant also controls the dense extension on the
whole old graph completion. -/
theorem actualFixedPhaseOldGraphToProductCollarExtension_norm_le
    (n : ℤ) (Y : ℝ) (C0 : ℝ)
    (hC0 : ∀ u : InverseEtaFixedPhaseCore n,
      ‖actualFixedPhaseSmoothCoreToProductCollarProfile n Y u‖ ≤
        C0 * ‖coreMap n u‖)
    (x : GraphSobolevCompletion n) :
    ‖actualFixedPhaseOldGraphToProductCollarExtension n Y x‖ ≤
      C0 * ‖x‖ := by
  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n
  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n
'''
DENSE=HEAD+'''  apply (denseRange_coreMap n).induction
  · intro y hy
    rcases hy with ⟨u, rfl⟩
    rw [actualFixedPhaseOldGraphToProductCollarExtension_core
      n Y ⟨C0, hC0⟩ u]
    exact hC0 u
  · exact isClosed_le (by fun_prop) (by fun_prop)
'''
EXPLICIT=HEAD+'''  exact LinearMap.norm_extendOfNorm_apply_le
    (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)
    (e := coreMap n)
    (denseRange_coreMap n) C0 hC0 x
'''
FINITE='''set_option maxHeartbeats 8000000 in
'''+HEAD+'''  exact LinearMap.norm_extendOfNorm_apply_le
    (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)
    (e := coreMap n)
    (denseRange_coreMap n) C0 hC0 x
'''
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def audit(t): return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}
def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS: raise SystemExit('usage: qym_c08_variants.py VARIANT QYM.lean')
    v,p=sys.argv[1],Path(sys.argv[2]); b=p.read_bytes()
    if hashlib.sha256(b).hexdigest()!=BASELINE_SHA256 or blob(b)!=BASELINE_BLOB: raise SystemExit('baseline mismatch')
    t=b.decode(); a0=audit(t); new={'dense_induction':DENSE,'explicit_args':EXPLICIT,'finite_heartbeats':FINITE}[v]
    if t.count(OLD)!=1: raise SystemExit(f'replacement count={t.count(OLD)}')
    t=t.replace(OLD,new,1); a1=audit(t)
    if a1!=a0: raise SystemExit(f'forbidden delta {a0}->{a1}')
    p.write_text(t); a=p.read_bytes()
    print(json.dumps({'schema':'qym-c08-v1','variant':v,'input_sha256':BASELINE_SHA256,'input_blob':BASELINE_BLOB,'candidate_sha256':hashlib.sha256(a).hexdigest(),'candidate_blob':blob(a),'bytes':len(a),'lf':a.count(b'\n'),'fixed_producers_targeted':['actualFixedPhaseOldGraphToProductCollarExtension_norm_le'],'forbidden_before':a0,'forbidden_after':a1},indent=2,sort_keys=True))
if __name__=='__main__': main()
