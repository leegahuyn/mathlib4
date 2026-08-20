from pathlib import Path
import re, hashlib, json, sys
p=Path(sys.argv[1]); out=Path(sys.argv[2])
s=p.read_text(); before=s
repairs=[]
def rep(old,new,n=1,label=None):
    global s
    c=s.count(old)
    if c!=n:
        raise SystemExit(f'count mismatch {label or old[:80]!r}: got {c} expected {n}')
    s=s.replace(old,new)
    repairs.append(label or old[:60])
rep('    simpa only [mul_assoc] using hMeasV.mul hMeasBase\n',
    '    simpa only [Pi.mul_apply, mul_assoc] using hMeasV.mul hMeasBase\n', label='3669 Pi.mul_apply')
rep('''    simpa only [Pi.zero_apply, pow_two, zero_mul, mul_zero,
      zero_add, add_zero, neg_zero, sub_zero, sub_eq_add_neg] using hModel.congr'
''','''    simpa only [Pi.zero_apply, zero_pow, OfNat.ofNat, mul_zero,
      sub_zero, sub_eq_add_neg] using hModel.congr'
''',label='3689 preserve pow2')
rep('''noncomputable def literalStageFourierModes (N : ℕ) :
    Finset (Fin 2 → ℤ) := by
  classical
  exact Finset.univ.pi fun _ : Fin 2 ↦
    Finset.Icc (-(N : ℤ)) (N : ℤ)
''','''noncomputable def literalStageFourierModes (N : ℕ) :
    Finset (Fin 2 → ℤ) := by
  classical
  exact ((Finset.Icc (-(N : ℤ)) (N : ℤ)).product
    (Finset.Icc (-(N : ℤ)) (N : ℤ))).image
      (fun p ↦ ![p.1, p.2])
''',label='3880 product-image mode set')
rep('''theorem mem_literalStageFourierModes_iff (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ literalStageFourierModes N ↔
      ∀ i : Fin 2, |k i| ≤ (N : ℤ) := by
  classical
  simp only [literalStageFourierModes, Finset.mem_pi, Finset.mem_univ,
    true_implies, Finset.mem_Icc, neg_le]
  exact forall_congr' fun i ↦ abs_le
''','''theorem mem_literalStageFourierModes_iff (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ literalStageFourierModes N ↔
      ∀ i : Fin 2, |k i| ≤ (N : ℤ) := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, hpk⟩
    have hp' := Finset.mem_product.mp hp
    intro i
    fin_cases i
    · change |k 0| ≤ (N : ℤ)
      have hb := Finset.mem_Icc.mp hp'.1
      have heq : k 0 = p.1 := by simpa using congrFun hpk.symm 0
      rw [heq]
      exact (abs_le).2 hb
    · change |k 1| ≤ (N : ℤ)
      have hb := Finset.mem_Icc.mp hp'.2
      have heq : k 1 = p.2 := by simpa using congrFun hpk.symm 1
      rw [heq]
      exact (abs_le).2 hb
  · intro hk
    apply Finset.mem_image.mpr
    refine ⟨(k 0, k 1), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_Icc.mpr ((abs_le).1 (hk 0))
      · exact Finset.mem_Icc.mpr ((abs_le).1 (hk 1))
    · funext i
      fin_cases i <;> rfl
''',label='3881 explicit mode membership')
rep('''  congr 3
  apply congrArg Complex.measurableEquivPi.symm
  funext i
  rw [UnitAddTorus.coe_measurableEquivPiIoc_apply]
  exact congrArg Subtype.val
    (AddCircle.equivIoc_coe_eq (by simpa using x.2 i))
''','''  congr 3
  norm_num
''',label='3899 interval endpoint')
rep('Module.finrank_complex_real','Complex.finrank_real_complex',3,label='3900/3901/coef finrank API')
rep('''      simp only [Complex.finrank_real_complex, zpow_neg, zpow_ofNat]
''','''      simp only [Complex.finrank_real_complex, smul_eq_mul, zpow_neg, zpow_ofNat]
''',2,label='3900/3901 smul normalization')
rep('''      exact MeasureTheory.setIntegral_le_integral
        (ambientTestCore_normSq_integrable v)
        (Filter.Eventually.of_forall fun w ↦ sq_nonneg ‖v w‖)
''','''      exact Filter.Eventually.of_forall fun w ↦ sq_nonneg ‖v w‖
''',label='3900 gcongr residual nonneg')
rep('''noncomputable def literalStagePlaneWaveRepresentative
    (Y : ℝ) (k : Fin 2 → ℤ) (w : ℂ) : ℂ :=
  if w ∈ literalStageFourierBox Y then
    ((literalStageFourierScale Y)⁻¹ : ℂ) *
      UnitAddTorus.mFourier k (literalStagePhysicalTorusPoint Y w)
  else 0
''','''noncomputable def literalStagePlaneWaveRepresentative
    (Y : ℝ) (k : Fin 2 → ℤ) (w : ℂ) : ℂ := by
  classical
  exact if w ∈ literalStageFourierBox Y then
    ((literalStageFourierScale Y)⁻¹ : ℂ) *
      UnitAddTorus.mFourier k (literalStagePhysicalTorusPoint Y w)
  else 0
''',label='3905 classical if')
rep('''  exact (measurable_const.mul
    (UnitAddTorus.mFourier k).continuous.measurable.comp
      (literalStagePhysicalTorusPoint_measurable Y)).ite
''','''  exact (measurable_const.mul
    ((UnitAddTorus.mFourier k).continuous.measurable.comp
      (literalStagePhysicalTorusPoint_measurable Y))).ite
''',label='3906 measurable comp precedence')
rep('(literalStageNegativePlaneWave_differentiable Y k w).differentiableAt',
    '(literalStageNegativePlaneWave_differentiable Y k).differentiableAt',2,label='3925/3926 differentiableAt')
rep('map_ofReal','starRingEnd_apply, Complex.conj_ofReal',2,label='3939/4182 conj real API')
rep('MeasureTheory.L2.norm_sq_eq_integral','ambientPlaneL2_norm_sq_eq_integral',2,label='3956 L2 norm sq API')
rep('/-! ### Actual bounded point-spectral consequences from Mathlib -/\n', '/-! ### Actual bounded point-spectral consequences from Mathlib -/\n\nopen Module.End\n', label='4184-4187 open Module.End')
rep('LinearMap.mem_eigenspace_iff','Module.End.mem_eigenspace_iff',2,label='4185/4186 mem eigenspace')
rep('exact MeasurableSet.iUnion fun a ↦ (hU.smul a)','exact MeasurableSet.iUnion fun a ↦ MeasurableSet.const_smul hU a',label='4195 measurable const_smul')
out.write_text(s)
decl=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
th=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(x):
    st=[m.start() for m in decl.finditer(x)]; r=[]
    for m in th.finditer(x):
        nxt=next((z for z in st if z>m.start()),len(x)); bl=x[m.start():nxt]; cut=bl.find(':= by')
        if cut<0: cut=bl.find(':=')
        r.append((m.group(2),re.sub(r'\s+',' ',bl if cut<0 else bl[:cut]).strip()))
    return r
assert decl.findall(before)==decl.findall(s)
assert headers(before)==headers(s)
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']
counts={}
for w in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'
    counts[w]=(len(re.findall(pat,before)),len(re.findall(pat,s)))
assert all(a==b for a,b in counts.values()),counts
print(json.dumps({'schema':'fa-v39-safe-clusters','base':hashlib.sha256(before.encode()).hexdigest(),'candidate':hashlib.sha256(s.encode()).hexdigest(),'lines':len(s.splitlines()),'bytes':len(s.encode()),'repairs':repairs,'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'forbidden_lexical_counts_preserved':True,'counts':counts},indent=2,ensure_ascii=False))
