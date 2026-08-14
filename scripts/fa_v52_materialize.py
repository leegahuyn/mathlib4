#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path
BASE_SHA='6093e976dd6c4d5217850ab39318eeef50531aef3acd8c6d66dcd0a4426c294d'
BASE_BYTES=2798992
BASE_LINES=62637
BASE_DECLS=4416
TRUST=('sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool')
DECL_RE=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
def sha(b):return hashlib.sha256(b).hexdigest()
def strip_noncode(text):
 out=list(text);i=0;d=0;q=False;e=False
 while i<len(out):
  if d:
   if text.startswith('/-',i):out[i]=out[i+1]=' ';d+=1;i+=2;continue
   if text.startswith('-/',i):out[i]=out[i+1]=' ';d-=1;i+=2;continue
   if out[i]!='\n':out[i]=' '
   i+=1;continue
  if q:
   ch=out[i]
   if ch!='\n':out[i]=' '
   if e:e=False
   elif ch=='\\':e=True
   elif ch=='"':q=False
   i+=1;continue
  if text.startswith('/-',i):out[i]=out[i+1]=' ';d=1;i+=2;continue
  if text.startswith('--',i):
   while i<len(out) and out[i]!='\n':out[i]=' ';i+=1
   continue
  if out[i]=='"':out[i]=' ';q=True
  i+=1
 return ''.join(out)
def trust(text):
 c=strip_noncode(text);return {x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',c)) for x in TRUST}
def ranges(text):
 ms=list(DECL_RE.finditer(text));return {m.group(1):(m.start(),ms[i+1].start() if i+1<len(ms) else len(text)) for i,m in enumerate(ms)}
def headers(text):
 out=[]
 for n,(a,b) in ranges(text).items():
  block=text[a:b];p=block.find(':=');out.append((n,block[:p].rstrip()))
 return out
def replace_body(text,name,body):
 a,b=ranges(text)[name];block=text[a:b];p=block.find(':= by')
 if p<0:raise RuntimeError('no body '+name)
 return text[:a]+block[:p]+':= by\n'+body.rstrip()+'\n\n'+text[b:],{'label':'replace_body','declaration':name}
def repl(text,name,old,new,label):
 a,b=ranges(text)[name];block=text[a:b];n=block.count(old)
 if n!=1:raise RuntimeError(f'{label}: expected one in {name}, got {n}')
 return text[:a]+block.replace(old,new,1)+text[b:],{'label':label,'declaration':name}
P3930='''  rw [MeasureTheory.L2.inner_def]
  unfold UnitAddTorus.mFourierCoeff
  rw [show (∫ w : ℂ,
      inner ℂ (literalStagePlaneWave Y k w)
        (ambientTestCoreToPlaneL2Linear v w)) =
      ∫ w : ℂ, literalStageNegativePlaneWave Y k w * v w by
    simpa only [MeasureTheory.L2.inner_def] using
      inner_planeWave_ambientTestCore_eq_integral_negativePlaneWave
        Y k v hv]
  rw [show (∫ t : P5LocalFourierRellich.TwoTorus,
      UnitAddTorus.mFourier (-k) t •
        (literalStageTorusTest Y v) t) =
      ∫ t : P5LocalFourierRellich.TwoTorus,
        UnitAddTorus.mFourier (-k) t *
          literalStageTorusRepresentative Y v t by
    apply integral_congr_ae
    filter_upwards [coeFn_literalStageTorusTest Y v] with t ht
    rw [ht]
    simp only [smul_eq_mul]]
  rw [UnitAddTorus.integral_preimage
    (fun t : P5LocalFourierRellich.TwoTorus ↦
      UnitAddTorus.mFourier (-k) t *
        literalStageTorusRepresentative Y v t)
    (fun _ : Fin 2 ↦ -(1 / 2 : ℝ))]
  have hsupport :
      (∫ w : ℂ, literalStageNegativePlaneWave Y k w * v w) =
        ∫ w in literalStageFourierBox Y,
          literalStageNegativePlaneWave Y k w * v w := by
    rw [← integral_indicator (literalStageFourierBox_measurableSet Y)]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ literalStageFourierBox Y
    · simp [hw]
    · have hv0 : v w = 0 := by
        by_contra hn
        exact hw (hv (subset_tsupport _ hn))
      simp [hw, hv0]
  rw [hsupport]
  calc
    (∫ w in literalStageFourierBox Y,
        literalStageNegativePlaneWave Y k w * v w) =
      (literalStageFourierScale Y : ℂ) ^ 2 *
        ∫ w in Complex.measurableEquivPi.symm '' literalStageUnitPiBox,
          literalStageNegativePlaneWave Y k
              (literalStageFourierScale Y • w) *
            v (literalStageFourierScale Y • w) := by
      rw [literalStageFourierBox_eq_smul_unitPiBox Y]
      have hscale := Measure.setIntegral_comp_smul_of_pos
        (E := ℂ) (F := ℂ) volume
        (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w * v w)
        (Complex.measurableEquivPi.symm '' literalStageUnitPiBox)
        (literalStageFourierScale_pos Y)
      rw [Complex.finrank_real_complex] at hscale
      calc
        _ = (literalStageFourierScale Y : ℂ) ^ 2 *
            ((((literalStageFourierScale Y) ^ 2)⁻¹ : ℝ) •
              ∫ w in literalStageFourierScale Y •
                  (Complex.measurableEquivPi.symm '' literalStageUnitPiBox),
                literalStageNegativePlaneWave Y k w * v w) := by
              simp only [Complex.real_smul]
              push_cast
              field_simp [literalStageFourierScale_ne_zero Y]
        _ = _ := by rw [hscale]
    _ = (literalStageFourierScale Y : ℂ) ^ 2 *
        ∫ x in literalStageUnitPiBox,
          UnitAddTorus.mFourier (-k) (fun i ↦ (x i : UnitAddCircle)) *
            literalStageTorusRepresentative Y v
              (fun i ↦ (x i : UnitAddCircle)) := by
      rw [← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [coeFn_literalStageTorusTest Y v] with x hx
      rw [hx]
      simp only [literalStageNegativePlaneWave,
        literalStageTorusRepresentative, literalStageTorusPoint,
        literalStageTorusCoordinate, smul_eq_mul, Complex.ofReal_mul,
        Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        UnitAddTorus.mFourier, ContinuousMap.coe_mk]
      rw [Fin.prod_univ_two]
      field_simp [literalStageFourierScale_ne_zero Y]
      ring
'''
P3933='''  rw [MeasureTheory.L2.inner_def]
  have hsupport :
      (∫ w : ℂ, inner ℂ (literalStagePlaneWave Y k w)
        (literalStagePlaneWave Y l w)) =
        ∫ w in literalStageFourierBox Y,
          inner ℂ (literalStagePlaneWaveRepresentative Y k w)
            (literalStagePlaneWaveRepresentative Y l w) := by
    rw [← integral_indicator (literalStageFourierBox_measurableSet Y)]
    apply integral_congr_ae
    filter_upwards [coeFn_literalStagePlaneWave Y k,
      coeFn_literalStagePlaneWave Y l] with w hk hl
    rw [hk, hl]
    by_cases hw : w ∈ literalStageFourierBox Y
    · simp [hw]
    · simp [literalStagePlaneWaveRepresentative, hw]
  rw [hsupport]
  calc
    (∫ w in literalStageFourierBox Y,
        inner ℂ (literalStagePlaneWaveRepresentative Y k w)
          (literalStagePlaneWaveRepresentative Y l w)) =
      inner ℂ
        (UnitAddTorus.mFourierLp (d := Fin 2) 2 k)
        (UnitAddTorus.mFourierLp (d := Fin 2) 2 l) := by
      rw [MeasureTheory.L2.inner_def]
      rw [UnitAddTorus.integral_preimage
        (fun t : P5LocalFourierRellich.TwoTorus ↦
          inner ℂ (UnitAddTorus.mFourier k t)
            (UnitAddTorus.mFourier l t))
        (fun _ : Fin 2 ↦ -(1 / 2 : ℝ))]
      calc
        (∫ w in literalStageFourierBox Y,
            inner ℂ (literalStagePlaneWaveRepresentative Y k w)
              (literalStagePlaneWaveRepresentative Y l w)) =
          (literalStageFourierScale Y : ℂ) ^ 2 *
            ∫ w in Complex.measurableEquivPi.symm '' literalStageUnitPiBox,
              inner ℂ
                (literalStagePlaneWaveRepresentative Y k
                  (literalStageFourierScale Y • w))
                (literalStagePlaneWaveRepresentative Y l
                  (literalStageFourierScale Y • w)) := by
          rw [literalStageFourierBox_eq_smul_unitPiBox Y]
          have hscale := Measure.setIntegral_comp_smul_of_pos
            (E := ℂ) (F := ℂ) volume
            (fun w : ℂ ↦ inner ℂ
              (literalStagePlaneWaveRepresentative Y k w)
              (literalStagePlaneWaveRepresentative Y l w))
            (Complex.measurableEquivPi.symm '' literalStageUnitPiBox)
            (literalStageFourierScale_pos Y)
          rw [Complex.finrank_real_complex] at hscale
          calc
            _ = (literalStageFourierScale Y : ℂ) ^ 2 *
                ((((literalStageFourierScale Y) ^ 2)⁻¹ : ℝ) •
                  ∫ w in literalStageFourierScale Y •
                      (Complex.measurableEquivPi.symm '' literalStageUnitPiBox),
                    inner ℂ (literalStagePlaneWaveRepresentative Y k w)
                      (literalStagePlaneWaveRepresentative Y l w)) := by
                  simp only [Complex.real_smul]
                  push_cast
                  field_simp [literalStageFourierScale_ne_zero Y]
            _ = _ := by rw [hscale]
        _ = (literalStageFourierScale Y : ℂ) ^ 2 *
            ∫ x in literalStageUnitPiBox,
              inner ℂ
                (literalStagePlaneWaveRepresentative Y k
                  (literalStageFourierScale Y •
                    Complex.measurableEquivPi.symm x))
                (literalStagePlaneWaveRepresentative Y l
                  (literalStageFourierScale Y •
                    Complex.measurableEquivPi.symm x)) := by
          rw [Complex.volume_preserving_equiv_pi.symm.setIntegral_image_emb
            Complex.measurableEquivPi.symm.measurableEmbedding
            (fun w : ℂ ↦ inner ℂ
              (literalStagePlaneWaveRepresentative Y k
                (literalStageFourierScale Y • w))
              (literalStagePlaneWaveRepresentative Y l
                (literalStageFourierScale Y • w))) literalStageUnitPiBox]
        _ = ∫ x in literalStageUnitPiBox,
            inner ℂ (UnitAddTorus.mFourier k (fun i ↦ (x i : UnitAddCircle)))
              (UnitAddTorus.mFourier l (fun i ↦ (x i : UnitAddCircle))) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          simp [literalStagePlaneWaveRepresentative,
            literalStageFourierBox_eq_smul_unitPiBox,
            literalStageFourierScale_ne_zero Y,
            literalStagePhysicalTorusPoint, RCLike.inner_apply,
            starRingEnd_apply]
          ring
    _ = if k = l then 1 else 0 :=
      (orthonormal_iff_ite.mp
        (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) k l
'''
REM_OLD='''  simpa only [mul_pow, mul_comm] using hsq
''
REM_CONVERT='''  convert hsq using 1 <;> ring
''
REM_CALC='''  calc
    ‖literalStagePlaneFiniteProjection Y N F -!F‖ ^ 2 =
        literalStageFourierScale Y ^ 2 *
           ‖L5LocalFourierRellich.twoTorusFiniteFourierProjection s T - T‖ ^ 2 := hsq
    _ = (literalStageFourierScale Y *
          ‖P5LocalFourierRellich.twoTorusFiniteFourierProjection s T - T‖) ^ 2 := by
      ring
''
ADJ_OLD='''  simp only [sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.conj_I,
    Complex.conj_ofReal, smul_eq_mul]
  ring_nf
''
ADJ_STAR='''  simp only [sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, smul_eq_mul]
  ring
'''
ADJ_SIMP='''  simp [sub_eq_add_neg, Complex.star_def]
  ring
'''
WRAP_NAMES=['graphPotentialOperator_eq_weightedFull','discriminantHardStageOperator_eq_weightedHard','weightedFull_sub_weightedHard_eq_weightedTail','norm_discriminantHardStageOperator_sub_graphPotential_le','graphPotentialOperator_isCompact_unconditional']
VARIANTS={
 'calc_hb2m_star_convert':('calc',2000000,'star','convert'),
 'calc_hb10m_star_convert':('calc',10000000,'star','convert'),
 'calc_hb2m_simp_convert':('calc',2000000,'simp','convert'),
 'calc_hb10m_simp_calc':('calc',10000000,'simp','calc'),
 'calc_nohb_star_convert':('calc',0,'star','convert'),
 'calc_hb5m_star_calc':('calc',5000000,'star','calc'),
}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,required=True);ap.add_argument('--variant',choices=VARIANTS,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--audit',type=Path,required=True);a=ap.parse_args()
 raw=a.base.read_bytes();text=raw.decode()
 if sha(raw)!=BASE_SHA or len(raw)!=BASE_BYTES or len(text.splitlines())!=BASE_LINES or len(DECL_RE.findall(text))!=BASE_DECLS:raise SystemExit('base identity mismatch')
 bh=headers(text);bt=trust(text);changes=[]
 text,r=replace_body(text,'inner_planeWave_ambientTestCore_eq_scale_mul_mFourierCoeff',P3930);changes.append(r)
 text,r=replace_body(text,'inner_literalStagePlaneWave',P3933);changes.append(r)
 _,hb,adj,rem=VARIANTS[a.variant]
 text,r=repl(text,'norm_planeFourierRemainder_eq_scale_mul_torusRemainder',REM_OLD,REM_CONVERT if rem=='convert' else REM_CALC,'remainder_square');changes.append(r)
 for n in ['euclideanRaiseTestAdjoint_conjugate_eq_conj_affineTranspose','euclideanLowerFromSuccTestAdjoint_conjugate_eq_conj_affineTranspose']:
  text,r=repl(text,n,ADJ_OLD,ADJ_STAR if adj=='star' else ADJ_SIMP,'adjoint_star_algebra');changes.append(r)
 if hb:
  for n in WRAP_NAMES:
   a0,_=ranges(text)[n]
   text=text[:a0]+f'set_option maxHeartbeats {hb} in\n'+text[a0:]
   changes.append({'label':'heartbeat_wrapper','declaration':n,'limit':hb})
  text=text.replace(''' := by\n  set_option maxHeartbeats 800000 in\n  ext u v\n''',''' := by\n  ext u v\n''',1)
 ah=headers(text);at=trust(text)
 if ah!=bh:raise SystemExit('headers/order changed')
 if at!=bt or any(at.values()):raise SystemExit(f'trust mismatch {at}')
 outb=text.encode();a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_bytes(outb)
 audit={'schema':'fa-v52-torus-heartbeat-matrix-v1','variant':a.variant,'base_sha256':BASE_SHA,'source_sha256':sha(outb),'source_bytes':len(outb),'source_lines':len(text.splitlines()),'declaration_count':len(DECL_RE.findall(text)),'declaration_headers_identical':True,'trust_before':bt,'trust_after':at,'changes':changes}
 a.audit.parent.mkdir(parents=True,exist_ok=True);a.audit.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n');print(json.dumps(audit,indent=2,sort_keys=True))
if __name__=='__main__':main()
