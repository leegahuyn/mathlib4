#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

BASE_SHA='c1498d669d3f43cda50edf7b61b33c865b00f6fe65ea95d9f1ab3c07794d1235'
BASE_BLOB='75c2eab05b4298d94246a6b0757f98a6ff5c02fe'
VARIANTS={'dense_induction','explicit_args'}
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
GATE='/-- Under the exact core estimate, the dense extension is the unique\ncontinuous map with the prescribed actual smooth constant-profile values. -/'

def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def audit(t):
    return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}

def main():
    if len(sys.argv)!=4 or sys.argv[1] not in VARIANTS: raise SystemExit('usage: patch.py VARIANT QYM.lean EXPECTED_SHA')
    v,p,expected=sys.argv[1],Path(sys.argv[2]),sys.argv[3]
    before=p.read_bytes()
    if sha(before)!=expected or expected!=BASE_SHA or blob(before)!=BASE_BLOB: raise SystemExit('authority mismatch')
    text=before.decode(); a0=audit(text)
    if text.count(OLD)!=1: raise SystemExit(f'block count={text.count(OLD)}')
    text=text.replace(OLD,DENSE if v=='dense_induction' else EXPLICIT,1); a1=audit(text)
    if a1!=a0: raise SystemExit(f'forbidden delta {a0}->{a1}')
    if GATE not in text: raise SystemExit('gate missing')
    p.write_text(text); after=p.read_bytes()
    print(json.dumps({'schema':'qym-gb78-v16-timeout-patch-v1','variant':v,'input_sha256':sha(before),'input_blob':blob(before),'candidate_sha256':sha(after),'candidate_blob':blob(after),'gate_line':text.count('\n',0,text.index(GATE))+1,'forbidden':a1,'bytes':len(after),'lf':after.count(b'\n')},indent=2,sort_keys=True))
if __name__=='__main__': main()
