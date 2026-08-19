#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
PAT=re.compile(r"(?ms)^set_option maxHeartbeats 2000000 in\n/-- A concrete smooth-core constant also controls.*?^theorem actualFixedPhaseOldGraphToProductCollarExtension_norm_le\b.*?(?=^/-- Under the exact core estimate)" )
EXPLICIT=r'''/-- A concrete smooth-core constant also controls the dense extension on the
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
    (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)
    (e := coreMap n)
    (denseRange_coreMap n) C0 hC0 x
'''
EXPLICIT_HAVE=r'''/-- A concrete smooth-core constant also controls the dense extension on the
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
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)
    (e := coreMap n)
    (denseRange_coreMap n) C0 hC0 x
  exact h
'''
HEARTBEAT=r'''set_option maxHeartbeats 8000000 in
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
    (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)
    (e := coreMap n)
    (denseRange_coreMap n) C0 hC0 x
'''
V={"explicit":EXPLICIT,"explicit_have":EXPLICIT_HAVE,"heartbeat":HEARTBEAT}
def audit(t): return {"sorry":len(re.findall(r"\bsorry\b",t)),"admit":len(re.findall(r"\badmit\b",t)),"native_decide":len(re.findall(r"\bnative_decide\b",t)),"Lean.ofReduceBool":t.count("Lean.ofReduceBool"),"global_axiom":len(re.findall(r"(?m)^\s*axiom\s+",t)),"unsafe":len(re.findall(r"(?m)^\s*unsafe\s+",t)),"maxHeartbeats_zero":len(re.findall(r"set_option\s+maxHeartbeats\s+0\b",t))}
def main():
  if len(sys.argv)!=3 or sys.argv[1] not in V: raise SystemExit('usage: collar_patch VARIANT QYM.lean')
  v,p=sys.argv[1],Path(sys.argv[2]); before=p.read_bytes(); t=before.decode(); a0=audit(t); ms=list(PAT.finditer(t))
  if len(ms)!=1: raise SystemExit(f'matches={len(ms)}')
  m=ms[0]; t=t[:m.start()]+V[v].rstrip()+"\n\n"+t[m.end():]; a1=audit(t)
  if a1!=a0: raise SystemExit(f'forbidden delta {a0}->{a1}')
  p.write_text(t); after=p.read_bytes(); print(json.dumps({'variant':v,'input_sha256':hashlib.sha256(before).hexdigest(),'candidate_sha256':hashlib.sha256(after).hexdigest(),'forbidden':a1},indent=2,sort_keys=True))
if __name__=='__main__': main()
