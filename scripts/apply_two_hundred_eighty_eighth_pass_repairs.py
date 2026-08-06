from pathlib import Path
import re, shutil

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / 'PrimalitySheafVerification' / 'Mock2.lean'
M2A = ROOT / 'PrimalitySheafVerification' / 'Mock2_Advanced.lean'
FA = ROOT / 'PrimalitySheafVerification' / 'Mock2_FunctionalAnalysis.lean'

def rep(t,o,n,label,e=1):
 c=t.count(o)
 if c!=e: raise RuntimeError(f'{label}: expected {e}, got {c}')
 print(label,c); return t.replace(o,n)

def main():
 m2=M2.read_text()
 m2=rep(m2,
'''  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom hm x
  simpa [sourceEqualizerFork] using h
''',
'''  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change (m x).1 = T.ι x
  simpa only [CategoryTheory.comp_apply] using
    ConcreteCategory.congr_hom hm x
''','m2 source unique')
 m2=rep(m2,
'''  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom hm x
  simpa [targetEqualizerFork] using h
''',
'''  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change (m x).1 = T.ι x
  simpa only [CategoryTheory.comp_apply] using
    ConcreteCategory.congr_hom hm x
''','m2 target unique')
 m2=rep(m2,'ShEq ActualBase','ShEq.{0, 0} ActualBase','m2 pin actual ShEq',10)
 m2=rep(m2,
'''      (constantSourceTorFunctor_model (X := ActualBase) M N ≅
        F ⋙ constantTargetTorFunctor_model (X := ActualBase) M N)
''',
'''      (constantSourceTorFunctor_model.{0, 0} (X := ActualBase) M N ≅
        F.{0, 0} ⋙
          constantTargetTorFunctor_model.{0, 0} (X := ActualBase) M N)
''','m2 pin constant functors')
 m2=rep(m2,
'''      (constantTorComparisonIso_model
        (X := ActualBase) M N hM).hom.app S =
''',
'''      (constantTorComparisonIso_model.{0, 0}
        (X := ActualBase) M N hM).hom.app S =
''','m2 pin comparison app')
 m2=rep(m2,
'''    ⟨constantTorComparisonIso_model (X := ActualBase) M N hM⟩
''',
'''    ⟨constantTorComparisonIso_model.{0, 0}
      (X := ActualBase) M N hM⟩
''','m2 pin comparison witness')
 m2=rep(m2,
'''    constantTorComparisonIso_model_hom_app (X := ActualBase) M N hM
''',
'''    constantTorComparisonIso_model_hom_app.{0, 0}
      (X := ActualBase) M N hM
''','m2 pin comparison theorem')
 q='Proposition20ActualQGaugeSpecialization.'
 m2=rep(m2,
'''  app := fun U _ => (0 : Proposition20ActualQGaugeSpecialization.Aq U)
''',
 f'''  app := fun U _ => {q}aqZero U
''','m2 zero comparison')
 m2=rep(m2,
'''    tensorToActualQGauge_zeroModel.app U s = 0 :=
''',
 f'''    tensorToActualQGauge_zeroModel.app U s = {q}aqZero U :=
''','m2 zero apply')
 m2=rep(m2,
'''    (hf : ∀ (U : Opens) (s : tensorGaugePresheafOverX_zeroModel.Field U),
      f.app U s = 0) :
''',
 f'''    (hf : ∀ (U : Opens) (s : tensorGaugePresheafOverX_zeroModel.Field U),
      f.app U s = {q}aqZero U) :
''','m2 zero uniqueness')
 m2=rep(m2,
'''  ∃ (U : Opens) (s : ActualTensorGlobal),
    B.comparison.app U (B.realizeGlobal U s) ≠ 0
''',
 f'''  ∃ (U : Opens) (s : ActualTensorGlobal),
    B.comparison.app U (B.realizeGlobal U s) ≠ {q}aqZero U
''','m2 nontrivial zero')
 M2.write_text(m2)

 a=M2A.read_text()
 a=rep(a,
'''  simpa [IsDenseEmbedding.subtypeEmb, Set.image_id] using
''',
'''  simpa [Set.inclusion, IsDenseEmbedding.subtypeEmb, Set.image_id] using
''','m2a dense inclusion unfold',2)
 a=rep(a,
'''  add_mem' := by
    intro A B hA hB
    simpa only [IsSmooth, Pi.add_apply, map_add] using hA.add hB
  smul_mem' := by
    intro c A hA
    simpa only [IsSmooth, Pi.smul_apply, map_smul] using hA.const_smul c
''',
'''  add_mem' := by
    intro A B hA hB
    change ContDiff ℂ ⊤ (fun z => coordinate (A z)) at hA
    change ContDiff ℂ ⊤ (fun z => coordinate (B z)) at hB
    change ContDiff ℂ ⊤ (fun z => coordinate ((A + B) z))
    simpa only [Pi.add_apply, map_add] using hA.add hB
  smul_mem' := by
    intro c A hA
    change ContDiff ℂ ⊤ (fun z => coordinate (A z)) at hA
    change ContDiff ℂ ⊤ (fun z => coordinate ((c • A) z))
    simpa only [Pi.smul_apply, map_smul] using hA.const_smul c
''','m2a algebraic smooth submodule')
 a=rep(a,
'''  zero_mem' := by
    simpa using
      (contDiff_const : ContDiff ℂ ⊤ (fun _ : ℂ => (0 : ContinuousValue)))
  add_mem' := by
    intro A B hA hB
    simpa only [Pi.add_apply] using hA.add hB
  smul_mem' := by
    intro c A hA
    simpa only [Pi.smul_apply] using hA.const_smul c
''',
'''  zero_mem' := by
    change ContDiff ℂ ⊤ (fun _ : ℂ => (0 : ContinuousValue))
    exact contDiff_const
  add_mem' := by
    intro A B hA hB
    change ContDiff ℂ ⊤ (fun z => A z + B z)
    exact hA.add hB
  smul_mem' := by
    intro c A hA
    change ContDiff ℂ ⊤ (fun z => c • A z)
    exact hA.const_smul c
''','m2a continuous smooth submodule')
 a=rep(a,
'''def forgetContinuousValue (A : ContinuousValue) : AlgebraicValue where
  toFun v := (A v).toLinearMap
  map_add' v w := by
    ext x
    simp
  map_smul' c v := by
    ext x
    change A (c * v) x = c * A v x
    simpa [smul_eq_mul] using
      congrArg (fun T : ℂ →L[ℂ] ℂ => T x) (A.map_smul c v)
''',
'''def forgetContinuousValue (A : ContinuousValue) : AlgebraicValue where
  toFun v := (A v).toLinearMap
  map_add' v w :=
    congrArg ContinuousLinearMap.toLinearMap (A.map_add v w)
  map_smul' c v :=
    congrArg ContinuousLinearMap.toLinearMap (A.map_smul c v)
''','m2a forget continuity')
 a=rep(a,
'''namespace UnnumberedFormulaLedger

inductive Disposition
  | proved
  | correctedAndProved
  | removedWithErratum
  deriving DecidableEq, Fintype, Repr
''',
'''namespace UnnumberedFormulaLedger

inductive Disposition
  | proved
  | correctedAndProved
  | removedWithErratum
  deriving DecidableEq, Repr

instance : Fintype Disposition where
  elems := {.proved, .correctedAndProved, .removedWithErratum}
  complete := by
    intro x
    cases x <;> simp
''','m2a disposition fintype')
 old='''instance : Fintype Disposition where
  elems := {.proved, .correctedAndProved, .removedWithErratum}
  complete := by
    intro x
    cases x <;> simp

inductive Claim
  | item1_pp3_4
  | equations1_1_to_1_16
  | quotedQ2A_to_Q2F
  | equations1_17_to_1_24
  | equations1_26_to_1_30
  | equations1_31_to_1_33
  | equations2_1_to_2_4
  | pages23_to_25
  | equations3_1_to_3_6
  | equations3_7_to_3_19
  | equations3_20_to_3_26
  | equations4_1_to_4_9
  | equations4_10_to_4_27
  | equations4_28_to_4_29
  | equations4_30_to_4_32
  | equation5_1
  | equations6_1_to_6_18
  deriving DecidableEq, Fintype, Repr
'''
 new='''instance : Fintype Disposition where
  elems := {.proved, .correctedAndProved, .removedWithErratum}
  complete := by
    intro x
    cases x <;> simp

inductive Claim
  | item1_pp3_4
  | equations1_1_to_1_16
  | quotedQ2A_to_Q2F
  | equations1_17_to_1_24
  | equations1_26_to_1_30
  | equations1_31_to_1_33
  | equations2_1_to_2_4
  | pages23_to_25
  | equations3_1_to_3_6
  | equations3_7_to_3_19
  | equations3_20_to_3_26
  | equations4_1_to_4_9
  | equations4_10_to_4_27
  | equations4_28_to_4_29
  | equations4_30_to_4_32
  | equation5_1
  | equations6_1_to_6_18
  deriving DecidableEq, Repr

instance : Fintype Claim where
  elems := {
    .item1_pp3_4,
    .equations1_1_to_1_16,
    .quotedQ2A_to_Q2F,
    .equations1_17_to_1_24,
    .equations1_26_to_1_30,
    .equations1_31_to_1_33,
    .equations2_1_to_2_4,
    .pages23_to_25,
    .equations3_1_to_3_6,
    .equations3_7_to_3_19,
    .equations3_20_to_3_26,
    .equations4_1_to_4_9,
    .equations4_10_to_4_27,
    .equations4_28_to_4_29,
    .equations4_30_to_4_32,
    .equation5_1,
    .equations6_1_to_6_18}
  complete := by
    intro x
    cases x <;> simp
'''
 a=rep(a,old,new,'m2a claim fintype')
 a=rep(a,
'''theorem dependencies_nonempty (c : Claim) :
    (dependencies c).Nonempty := by
  cases c <;> simp [dependencies]
''',
'''theorem dependencies_nonempty (c : Claim) :
    dependencies c ≠ [] := by
  cases c <;> simp [dependencies]
''','m2a dependencies nonempty')
 pat=r'^theorem ([A-Za-z0-9_]+) : _ :='
 a,n=re.subn(pat,r'noncomputable def \1 :=',a,flags=re.M)
 print('m2a ledger aliases',n)
 if n!=601: raise RuntimeError(n)
 M2A.write_text(a)

 f=FA.read_text()
 f=rep(f,
'''/-- Use one coherent inner-product completion instance in all subsequent
completed-graph declarations. -/
noncomputable local instance sobolevCompletionInnerProductSpace :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.innerProductSpace
''',
'''/-- Use one coherent normed-space and inner-product completion instance in
all subsequent completed-graph declarations. -/
noncomputable local instance sobolevCompletionNormedSpace :
    NormedSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange

noncomputable local instance sobolevCompletionInnerProductSpace :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.innerProductSpace
''','fa completion instances')
 FA.write_text(f)

if __name__=='__main__': main()
