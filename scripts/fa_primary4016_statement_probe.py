#!/usr/bin/env python3
"""Probe statement-elaboration paths for FA blocker 4016.

The verified prefix proves the preceding hard-stage theorem.  All prior suffix
variants failed at the declaration line of the subtraction theorem, before a
candidate helper could be installed.  This suite therefore varies the public
statement's elaboration path (scoped heartbeat, explicit result type, let-bound
operators, explicit Sub.sub) while preserving its mathematical proposition.
"""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

SOURCE=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
EXPECTED='1c3d12594a3e8b14f9cf7b7294da7c29221758c72d00a596215198f7623fad8c'
PREFIX=Path('PrimalitySheafVerification/FA_Blocker_Prefix.lean')
DIR=Path('PrimalitySheafVerification/FA_Blocker_StatementCandidates')
START='/-- Pointwise splitting of full multiplication into hard and tail parts,\n'
END='theorem norm_discriminantHardStageOperator_sub_graphPotential_le'
PRE='''import PrimalitySheafVerification.FA_Blocker_Prefix

namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace P5DiscriminantHardTruncation

open Set Function Topology Filter MeasureTheory
open scoped ENNReal NNReal
open DefinitionOneSobolev
open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
open DefinitionOneSobolev.FixedPhaseGraphCompletion
open DefinitionOneSobolev.WeightCorePetersson
open GammaTwoQuotientGeometry
open FixedPhaseClosedOperators
open FixedPhaseClosedOperators.PhysicalLocalL2
open ExplicitDiscriminantPotential
open ExplicitDiscriminantPotential.FixedPhaseGraphPotential
open P5PhysicalHardStageRestriction

'''
POST='''

end P5DiscriminantHardTruncation
end Mock2FA.PaperCorrections.AutomorphicSobolev
'''
ORIGINAL_PROOF=r'''by
  ext u v
  rw [discriminantHardStageOperator_eq_weightedHard]
  simp only [ContinuousLinearMap.sub_apply, weightedGraphOperator,
    LinearMap.mkContinuous₂_apply,
    weightedGraphLinear, lpInfinityMultiplier_apply]
  rw [← inner_sub_right]
  congr 2
  apply Lp.ext
  filter_upwards [
    coeFn_discriminantFullCarrierWeightLp,
    coeFn_discriminantTailCarrierWeightLp N,
    coeFn_discriminantHardCarrierWeightLp N,
    MeasureTheory.Lp.coeFn_lpSMul discriminantFullCarrierWeightLp
      (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (discriminantTailCarrierWeightLp N)
      (graphEuclideanBase n u)] with z hfull htail hhard hfullmul htailmul
  rw [hfullmul, htailmul, hfull, htail, hhard,
    discriminantFull_eq_hard_add_tail]
  ring
'''
MUL_HELPER=r'''theorem discriminantFullCarrierMul_eq_hard_add_tail_statementProbe
    (N : ℕ) (n : ℤ) (u : GraphSobolevCompletion n) :
    (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
        OrbitEuclideanL2 n) =
      (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n) +
      (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n) := by
  apply Lp.ext
  filter_upwards [
    coeFn_discriminantFullCarrierWeightLp,
    coeFn_discriminantHardCarrierWeightLp N,
    coeFn_discriminantTailCarrierWeightLp N,
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      discriminantFullCarrierWeightLp (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantHardCarrierWeightLp N) (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantTailCarrierWeightLp N) (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_add
      (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n)
      (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n)] with
      z hfull hhard htail hfullmul hhardmul htailmul hadd
  rw [hfullmul, hadd, Pi.add_apply, hhardmul, htailmul,
    hfull, hhard, htail, discriminantFull_eq_hard_add_tail]
  ring
'''
ADDITIVE_PROOF=r'''by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hhard :
      discriminantHardStageOperator N n u v =
        weightedGraphOperator n (discriminantHardCarrierWeightLp N) u v :=
    congrArg (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
      (discriminantHardStageOperator_eq_weightedHard N n)
  simp only [ContinuousLinearMap.sub_apply]
  rw [hhard]
  simp only [weightedGraphOperator, LinearMap.mkContinuous₂_apply,
    weightedGraphLinear, lpInfinityMultiplier_apply]
  rw [← inner_sub_right]
  have hmul := discriminantFullCarrierMul_eq_hard_add_tail_statementProbe N n u
  have hsub :
      (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
          OrbitEuclideanL2 n) -
        (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
          OrbitEuclideanL2 n) =
        (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
          OrbitEuclideanL2 n) := by
    rw [hmul]
    abel
  exact congrArg
    (fun w : OrbitEuclideanL2 n ↦ inner ℂ (graphEuclideanBase n v) w) hsub
'''
EXACT_STMT=r'''theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := '''
TYPED_STMT=r'''theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    ((weightedGraphOperator n discriminantFullCarrierWeightLp :
        WeakAntiOperator (GraphSobolevCompletion n)) -
      (discriminantHardStageOperator N n :
        WeakAntiOperator (GraphSobolevCompletion n)) :
      WeakAntiOperator (GraphSobolevCompletion n)) =
    (weightedGraphOperator n (discriminantTailCarrierWeightLp N) :
      WeakAntiOperator (GraphSobolevCompletion n)) := '''
LET_STMT=r'''theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    let A : WeakAntiOperator (GraphSobolevCompletion n) :=
      weightedGraphOperator n discriminantFullCarrierWeightLp
    let H : WeakAntiOperator (GraphSobolevCompletion n) :=
      discriminantHardStageOperator N n
    let T : WeakAntiOperator (GraphSobolevCompletion n) :=
      weightedGraphOperator n (discriminantTailCarrierWeightLp N)
    A - H = T := '''
SUB_STMT=r'''theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    Sub.sub (α := WeakAntiOperator (GraphSobolevCompletion n))
      (weightedGraphOperator n discriminantFullCarrierWeightLp)
      (discriminantHardStageOperator N n) =
    (weightedGraphOperator n (discriminantTailCarrierWeightLp N) :
      WeakAntiOperator (GraphSobolevCompletion n)) := '''

C={
 '01': 'set_option maxHeartbeats 800000 in\n'+EXACT_STMT+ORIGINAL_PROOF,
 '02': 'set_option maxHeartbeats 2000000 in\n'+EXACT_STMT+ORIGINAL_PROOF,
 '03': TYPED_STMT+ORIGINAL_PROOF,
 '04': 'set_option maxHeartbeats 800000 in\n'+TYPED_STMT+ORIGINAL_PROOF,
 '05': LET_STMT+'by\n  dsimp only\n'+ORIGINAL_PROOF.removeprefix('by\n'),
 '06': MUL_HELPER+'\nset_option maxHeartbeats 800000 in\n'+EXACT_STMT+ADDITIVE_PROOF,
 '07': MUL_HELPER+'\n'+TYPED_STMT+ADDITIVE_PROOF,
 '08': MUL_HELPER+'\nset_option maxHeartbeats 800000 in\n'+SUB_STMT+ADDITIVE_PROOF,
}

def sha(b:bytes): return hashlib.sha256(b).hexdigest()
def load():
 b=SOURCE.read_bytes(); a=sha(b)
 if a!=EXPECTED: raise SystemExit(f'source mismatch {a}')
 s=b.decode()
 if s.count(START)!=1 or s.count(END)!=1: raise SystemExit('markers')
 return b,s
def gen():
 b,s=load(); st=s.index(START)
 PREFIX.write_text(s[:st].rstrip()+POST)
 DIR.mkdir(parents=True,exist_ok=True)
 rows=[]
 for k,v in sorted(C.items()):
  p=DIR/f'Candidate{k}.lean'; payload=PRE+v.rstrip()+POST; p.write_text(payload)
  rows.append({'candidate_id':k,'path':str(p),'sha256':sha(payload.encode()),'lines':len(payload.splitlines())})
 print(json.dumps({'schema':'fa-primary4016-statement-probe-v1','source_sha256':sha(b),'prefix_sha256':sha(PREFIX.read_bytes()),'candidates':rows},indent=2))
def mat(k,out):
 _,s=load(); st=s.index(START); en=s.index(END,st)
 out.parent.mkdir(parents=True,exist_ok=True); out.write_text(s[:st]+C[k].rstrip()+'\n\n'+s[en:])
 print(json.dumps({'candidate_id':k,'output':str(out),'sha256':sha(out.read_bytes())},indent=2))
def main():
 p=argparse.ArgumentParser(); p.add_argument('--materialize'); p.add_argument('--output',type=Path); a=p.parse_args()
 if a.materialize: mat(a.materialize,a.output)
 else: gen()
if __name__=='__main__': main()
