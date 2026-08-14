#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

BASE_SHA='233538124c10727fb00a88d62685f133a604da6a414c00493baa05c21a2f1a7a'
BASE_BYTES=2795006
BASE_LINES=62532
BASE_DECLS=4416
TRUST=('sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool')
DECL_RE=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')

def strip_noncode(text:str)->str:
    out=list(text); i=0; depth=0; string=False; esc=False
    while i<len(out):
        if depth:
            if text.startswith('/-',i): out[i]=out[i+1]=' '; depth+=1; i+=2; continue
            if text.startswith('-/',i): out[i]=out[i+1]=' '; depth-=1; i+=2; continue
            if out[i]!='\n': out[i]=' '
            i+=1; continue
        if string:
            ch=out[i]
            if ch!='\n': out[i]=' '
            if esc: esc=False
            elif ch=='\\': esc=True
            elif ch=='"': string=False
            i+=1; continue
        if text.startswith('/-',i): out[i]=out[i+1]=' '; depth=1; i+=2; continue
        if text.startswith('--',i):
            while i<len(out) and out[i]!='\n': out[i]=' '; i+=1
            continue
        if out[i]=='"': out[i]=' '; string=True
        i+=1
    return ''.join(out)

def trust(text:str):
    code=strip_noncode(text)
    return {t:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(t)+r'(?![A-Za-z0-9_])',code)) for t in TRUST}

PATCHES={
'holder_r1':(
'''        (lsmul ℂ ℂ).coeFn_holder V ut,''',
'''        (lsmul ℂ ℂ).coeFn_holder (r := 1) V ut,'''),
'holder_norm_r1':(
'''      have h := (lsmul ℂ ℂ).norm_holder_apply_apply_le V ut''',
'''      have h := (lsmul ℂ ℂ).norm_holder_apply_apply_le (r := 1) V ut'''),
'houter_comp_def':(
'''      Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk] using hOuter''',
'''      Function.comp_apply, Function.comp_def, LinearMap.coe_mk, AddHom.coe_mk] using hOuter'''),
'ioc_box_linarith':(
'''  exact congrArg Subtype.val
    (AddCircle.equivIoc_coe_eq (by simpa using hx i))''',
'''  exact congrArg Subtype.val
    (AddCircle.equivIoc_coe_eq (by
      constructor
      · exact (hx i).1
      · linarith [(hx i).2]))'''),
'ioc_scaled_linarith':(
'''    exact congrArg Subtype.val
      (AddCircle.equivIoc_coe_eq (by simpa using hscaled))''',
'''    exact congrArg Subtype.val
      (AddCircle.equivIoc_coe_eq (by
        constructor
        · exact hscaled.1
        · linarith [hscaled.2]))'''),
'ring_nf_raise':(
'''  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply, sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.conj_I,
    Complex.conj_ofReal, smul_eq_mul]
  ring

/-- Hermitian lowering transpose applied to the conjugated test is the''',
'''  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply, sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.conj_I,
    Complex.conj_ofReal, smul_eq_mul]
  ring_nf

/-- Hermitian lowering transpose applied to the conjugated test is the'''),
'ring_nf_lower':(
'''  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply, sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.conj_I,
    Complex.conj_ofReal, smul_eq_mul]
  ring

/-- Signed lowering of the periodized conjugate is a chart gauge model for''',
'''  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply, sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.conj_I,
    Complex.conj_ofReal, smul_eq_mul]
  ring_nf

/-- Signed lowering of the periodized conjugate is a chart gauge model for'''),
'w27_holder':(
'''        MeasureTheory.Lp.coeFn_lpSMul
          discriminantFullCarrierWeightLp''',
'''        MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
          discriminantFullCarrierWeightLp'''),
'w27_pointwise':(
'''      simp only [weightedGraphOperator, weightedGraphLinear,
        lpInfinityMultiplier_apply]
      rw [hv, hmul, hw, hu]
      rfl''',
'''      simp only [weightedGraphOperator, weightedGraphLinear,
        lpInfinityMultiplier_apply]
      rw [hv, hmul]
      simp only [Pi.smul_apply, hw, hu]
      rfl'''),
'w27_smul':(
'''      change (upstairsPotential z : ℂ) * (hyperbolicDensity z : ℂ) *
          upstairsInnerDensity (OrbitMultiplier n) V U z =
        (hyperbolicDensity z : ℂ) * ((upstairsPotential z : ℂ) *
          upstairsInnerDensity (OrbitMultiplier n) V U z)
      ring''',
'''      simp only [NNReal.smul_def, Complex.real_smul]
      ring'''),
'w06_nolet_exact':(
'''    Differentiable ℝ (literalStageNegativePlaneWave Y k) := by
  unfold literalStageNegativePlaneWave
  fun_prop''',
'''    Differentiable ℝ (literalStageNegativePlaneWave Y k) := by
  unfold literalStageNegativePlaneWave
  have hFourier (i : Fin 2) :
      Differentiable ℝ (fun x : ℝ =>
        fourier (-(k i)) ((x : ℝ) : UnitAddCircle)) :=
    fun x =>
      (hasDerivAt_fourier_neg (1 : ℝ) (k i) x).differentiableAt
  have hRe : Differentiable ℝ (fun w : ℂ =>
      fourier (-(k 0))
        (((literalStageFourierScale Y)⁻¹ * w.re : ℝ) : UnitAddCircle)) := by
    simpa only [Function.comp_def] using
      (hFourier 0).comp
        (by fun_prop : Differentiable ℝ (fun w : ℂ =>
          (literalStageFourierScale Y)⁻¹ * w.re))
  have hIm : Differentiable ℝ (fun w : ℂ =>
      fourier (-(k 1))
        (((literalStageFourierScale Y)⁻¹ * w.im : ℝ) : UnitAddCircle)) := by
    simpa only [Function.comp_def] using
      (hFourier 1).comp
        (by fun_prop : Differentiable ℝ (fun w : ℂ =>
          (literalStageFourierScale Y)⁻¹ * w.im))
  have hScale : Differentiable ℝ (fun _ : ℂ =>
      ((literalStageFourierScale Y : ℂ)⁻¹)) :=
    differentiable_const _
  simpa only [Pi.mul_apply] using (hScale.mul hRe).mul hIm'''),
'w06_nolet_funprop':(
'''    Differentiable ℝ (literalStageNegativePlaneWave Y k) := by
  unfold literalStageNegativePlaneWave
  fun_prop''',
'''    Differentiable ℝ (literalStageNegativePlaneWave Y k) := by
  unfold literalStageNegativePlaneWave
  have hFourier (i : Fin 2) :
      Differentiable ℝ (fun x : ℝ =>
        fourier (-(k i)) ((x : ℝ) : UnitAddCircle)) :=
    fun x =>
      (hasDerivAt_fourier_neg (1 : ℝ) (k i) x).differentiableAt
  have hRe : Differentiable ℝ (fun w : ℂ =>
      fourier (-(k 0))
        (((literalStageFourierScale Y)⁻¹ * w.re : ℝ) : UnitAddCircle)) := by
    simpa only [Function.comp_def] using
      (hFourier 0).comp
        (by fun_prop : Differentiable ℝ (fun w : ℂ =>
          (literalStageFourierScale Y)⁻¹ * w.re))
  have hIm : Differentiable ℝ (fun w : ℂ =>
      fourier (-(k 1))
        (((literalStageFourierScale Y)⁻¹ * w.im : ℝ) : UnitAddCircle)) := by
    simpa only [Function.comp_def] using
      (hFourier 1).comp
        (by fun_prop : Differentiable ℝ (fun w : ℂ =>
          (literalStageFourierScale Y)⁻¹ * w.im))
  fun_prop'''),
'plane_conj':(
'''  rw [literalStagePlaneWaveRepresentative, if_pos hw]
  calc
    literalStageNegativePlaneWave Y k w =
        ((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier (-k)
            (literalStagePhysicalTorusPoint Y w) := by
      simp only [literalStageNegativePlaneWave, UnitAddTorus.mFourier,
        literalStagePhysicalTorusPoint, ContinuousMap.coe_mk, Pi.neg_apply]
      rw [Fin.prod_univ_two]
      ring
    _ = ((literalStageFourierScale Y)⁻¹ : ℂ) *
          Complex.conj (UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      rw [UnitAddTorus.mFourier_neg]
    _ = star (((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]''',
'''  rw [literalStagePlaneWaveRepresentative, if_pos hw]
  calc
    literalStageNegativePlaneWave Y k w =
        ((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier (-k)
            (literalStagePhysicalTorusPoint Y w) := by
      simp only [literalStageNegativePlaneWave, UnitAddTorus.mFourier,
        literalStagePhysicalTorusPoint, Complex.measurableEquivPi_apply,
        ContinuousMap.coe_mk, Pi.neg_apply]
      rw [Fin.prod_univ_two]
      ring_nf
    _ = ((literalStageFourierScale Y)⁻¹ : ℂ) *
          star (UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      simpa only [starRingEnd_apply] using
        congrArg (fun z : ℂ => ((literalStageFourierScale Y)⁻¹ : ℂ) * z)
          (UnitAddTorus.mFourier_neg (n := k)
            (x := literalStagePhysicalTorusPoint Y w))
    _ = star (((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      simp [star_mul']'''),
'one_names_try':(
'''    simp only [one_div, one_re, one_im, Complex.add_re, Complex.add_im,
      Complex.real_smul, smul_eq_mul, mul_one, add_zero, zero_mul,
      Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring''',
'''    try simp only [one_div, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_one, add_zero, zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''),
'i_names_try':(
'''    simp only [one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul, mul_one, add_zero,
      zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring''',
'''    try simp only [one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul, mul_one, add_zero,
      zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''),
}

SAFE=['holder_r1','holder_norm_r1','houter_comp_def','ioc_box_linarith','ioc_scaled_linarith','ring_nf_raise','ring_nf_lower']
VARIANTS={
 'safe': SAFE,
 'safe_w27': SAFE+['w27_holder','w27_pointwise','w27_smul'],
 'safe_w06_exact': SAFE+['w06_nolet_exact'],
 'safe_w06_funprop': SAFE+['w06_nolet_funprop'],
 'safe_w06_funprop_w27': SAFE+['w06_nolet_funprop','w27_holder','w27_pointwise','w27_smul'],
 'plane_batch': SAFE+['w06_nolet_funprop','plane_conj','one_names_try','i_names_try','w27_holder','w27_pointwise','w27_smul'],
}

def apply_one(text,name):
    old,new=PATCHES[name]
    c=text.count(old)
    if c!=1: raise RuntimeError(f'{name}: expected one old block, got {c}')
    return text.replace(old,new,1)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--base',type=Path,required=True); ap.add_argument('--variant',choices=VARIANTS,required=True); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--audit',type=Path,required=True)
    a=ap.parse_args(); raw=a.base.read_bytes(); text=raw.decode()
    assert hashlib.sha256(raw).hexdigest()==BASE_SHA
    assert len(raw)==BASE_BYTES and len(text.splitlines())==BASE_LINES
    before_decls=DECL_RE.findall(text); assert len(before_decls)==BASE_DECLS
    before_trust=trust(text); assert all(v==0 for v in before_trust.values())
    applied=[]
    for name in VARIANTS[a.variant]:
        text=apply_one(text,name); applied.append(name)
    after_decls=DECL_RE.findall(text); after_trust=trust(text)
    assert after_decls==before_decls
    assert all(v==0 for v in after_trust.values())
    data=text.encode(); a.out.parent.mkdir(parents=True,exist_ok=True); a.out.write_bytes(data)
    audit={
      'schema':'fa-v47-materialization-audit-v1','variant':a.variant,
      'base_sha256':BASE_SHA,'base_bytes':BASE_BYTES,'base_lines':BASE_LINES,'base_declarations':BASE_DECLS,
      'source_sha256':hashlib.sha256(data).hexdigest(),'source_bytes':len(data),'source_lines':len(text.splitlines()),
      'source_declarations':len(after_decls),'declaration_sequence_identical':after_decls==before_decls,
      'trust_before':before_trust,'trust_after':after_trust,'applied_patches':applied,
      'public_header_changes':False,'comments_changed':False,'attributes_changed':False,
    }
    a.audit.parent.mkdir(parents=True,exist_ok=True); a.audit.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
    print(json.dumps(audit,indent=2,sort_keys=True))
if __name__=='__main__': main()
