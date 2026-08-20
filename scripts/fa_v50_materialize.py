#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path
BASE_SHA='94cee5cf092961585335b42a53bbbe91e20989a7839a4f90f1f8fd9ee0ab4a7b'
BASE_BYTES=2797457
BASE_LINES=62601
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
def trust_counts(text):
 code=strip_noncode(text)
 return {t:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(t)+r'(?![A-Za-z0-9_])',code)) for t in TRUST}
def decl_ranges(text):
 ms=list(DECL_RE.finditer(text));return {m.group(1):(m.start(),ms[i+1].start() if i+1<len(ms) else len(text)) for i,m in enumerate(ms)}
def decl_headers(text):
 out=[]
 for n,(a,b) in decl_ranges(text).items():
  block=text[a:b];p=block.find(':=')
  out.append((n,block[:p].rstrip()))
 return out
def replace_decl(text,name,old,new,label):
 a,b=decl_ranges(text)[name];block=text[a:b];n=block.count(old)
 if n!=1:raise RuntimeError(f'{label}: expected one block in {name}, got {n}')
 return text[:a]+block.replace(old,new,1)+text[b:],{'label':label,'declaration':name}

ONE_OLD='''  case e'_8 =>
    funext t
    simp [id, one_div, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul]
    ring_nf
  case e'_9 =>
    simp [id, one_div, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp [literalStageFourierScale_ne_zero Y]
    ring_nf
'''
ONE_NEW='''  case e'_8 =>
    funext t
    simp [id, one_div, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul]
  case e'_9 =>
    simp [id]
'''
I_OLD='''  case e'_8 =>
    funext t
    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul]
    ring_nf
  case e'_9 =>
    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp [literalStageFourierScale_ne_zero Y]
    ring_nf
'''
I_NEW='''  case e'_8 =>
    funext t
    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul]
  case e'_9 =>
    simp [id]
'''

DX_OLD='''  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1)
      (volume : Measure ℂ) := by
    rw [← hdx]
    exact ((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (v := (1 : ℂ))
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  rw [hdx]
  calc
    (∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1) =
'''
DX_CONGR='''  have hdx_apply (w : ℂ) :
      HalfWeightCompactCoordinateGreen.dx v w =
        (fderiv ℝ (v : ℂ → ℂ) w) 1 :=
    congrFun hdx w
  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1)
      (volume : Measure ℂ) := by
    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by rw [hdx_apply w])
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (v := (1 : ℂ))
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  calc
    (∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        HalfWeightCompactCoordinateGreen.dx v w) =
      ∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1 := by
      apply integral_congr_ae
      filter_upwards with w
      rw [hdx_apply w]
    _ =
'''
DX_SIMPA='''  have hdx_apply (w : ℂ) :
      HalfWeightCompactCoordinateGreen.dx v w =
        (fderiv ℝ (v : ℂ → ℂ) w) 1 :=
    congrFun hdx w
  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1)
      (volume : Measure ℂ) := by
    simpa only [← hdx_apply] using
      ((literalStageNegativePlaneWave_continuous Y k).mul
        (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
          (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (v := (1 : ℂ))
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  calc
    (∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        HalfWeightCompactCoordinateGreen.dx v w) =
      ∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1 := by
      apply integral_congr_ae
      filter_upwards with w
      rw [hdx_apply w]
    _ =
'''
DY_OLD='''  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) Complex.I)
      (volume : Measure ℂ) := by
    rw [← hdy]
    exact ((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ))
    (f := literalStageNegativePlaneWave Y k) (g := (v : ℂ → ℂ))
    (v := Complex.I)
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  rw [hdy]
  calc
    (∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) Complex.I) =
'''
DY_CONGR='''  have hdy_apply (w : ℂ) :
      HalfWeightCompactCoordinateGreen.dy v w =
        (fderiv ℝ (v : ℂ → ℂ) w) Complex.I :=
    congrFun hdy w
  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) Complex.I)
      (volume : Measure ℂ) := by
    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by rw [hdy_apply w])
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ))
    (f := literalStageNegativePlaneWave Y k) (g := (v : ℂ → ℂ))
    (v := Complex.I)
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  calc
    (∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        HalfWeightCompactCoordinateGreen.dy v w) =
      ∫ w : ℂ, literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) Complex.I := by
      apply integral_congr_ae
      filter_upwards with w
      rw [hdy_apply w]
    _ =
'''
DY_SIMPA=DY_CONGR.replace("    exact (((literalStageNegativePlaneWave_continuous Y k).mul\n      (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport\n        (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left).congr\n          (Filter.Eventually.of_forall fun w ↦ by rw [hdy_apply w])", "    simpa only [← hdy_apply] using\n      ((literalStageNegativePlaneWave_continuous Y k).mul\n        (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport\n          (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left")
RING_OLD='''  simpa only [mul_pow] using hsq
'''
RING_NEW='''  simpa only [mul_pow] using hsq <;> ring_nf
'''
WEIGHT_OLD='''      rw [hv, hmul]
      rfl
'''
WEIGHT_CHANGE='''      rw [hv, hmul]
      change inner ℂ (fixedPhaseEuclideanGauge n v z)
          (((discriminantFullCarrierWeightLp : ℍ → ℂ) z) *
            ((graphEuclideanBase n (coreMap n u) : ℍ → ℂ) z)) =
        inner ℂ (fixedPhaseEuclideanGauge n v z)
          ((upstairsPotential z : ℂ) * fixedPhaseEuclideanGauge n u z)
      rw [hw, hu]
      rfl
'''
WEIGHT_SHOW='''      rw [hv, hmul]
      rw [show
        ((⇑discriminantFullCarrierWeightLp •
          ⇑(graphEuclideanBase n (coreMap n u))) z) =
          (⇑discriminantFullCarrierWeightLp z) *
            (⇑(graphEuclideanBase n (coreMap n u)) z) by rfl,
        hw, hu]
      rfl
'''
WEIGHT_SIMP='''      rw [hv, hmul]
      change inner ℂ (fixedPhaseEuclideanGauge n v z)
          (((discriminantFullCarrierWeightLp : ℍ → ℂ) z) *
            ((graphEuclideanBase n (coreMap n u) : ℍ → ℂ) z)) = _
      simpa only [hw, hu, discriminantFullCarrierWeight]
'''
ADJ_OLD='''  rw [hfun]
  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
'''
ADJ_NEW='''  have hfderiv :
      fderiv ℝ (reducedChartAmbientTest v hv : ℂ → ℂ) w =
        fderiv ℝ (v : ℂ → ℂ) w :=
    congrArg (fun f : ℂ → ℂ ↦ fderiv ℝ f w) hfun
  rw [hfun, hfderiv]
  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
'''
VARIANTS={
'congr_change_adj':('congr','change',True),
'congr_show_adj':('congr','show',True),
'congr_simp_adj':('congr','simp',True),
'simpa_change_adj':('simpa','change',True),
'congr_change_noadj':('congr','change',False),
'congr_show_noadj':('congr','show',False),
}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,required=True);ap.add_argument('--variant',choices=VARIANTS,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--audit',type=Path,required=True);a=ap.parse_args()
 raw=a.base.read_bytes();text=raw.decode()
 if sha(raw)!=BASE_SHA or len(raw)!=BASE_BYTES or len(text.splitlines())!=BASE_LINES or len(DECL_RE.findall(text))!=BASE_DECLS:raise SystemExit('base identity mismatch')
 before_headers=decl_headers(text);before_trust=trust_counts(text);changes=[]
 text,r=replace_decl(text,'fderiv_literalStageNegativePlaneWave_one',ONE_OLD,ONE_NEW,'deriv_one_clean');changes.append(r)
 text,r=replace_decl(text,'fderiv_literalStageNegativePlaneWave_I',I_OLD,I_NEW,'deriv_I_clean');changes.append(r)
 dxmode,wmode,adj=VARIANTS[a.variant]
 text,r=replace_decl(text,'integral_negativePlaneWave_mul_dx',DX_OLD,DX_CONGR if dxmode=='congr' else DX_SIMPA,'dx_pointwise');changes.append(r)
 text,r=replace_decl(text,'integral_negativePlaneWave_mul_dy',DY_OLD,DY_CONGR if dxmode=='congr' else DY_SIMPA,'dy_pointwise');changes.append(r)
 text,r=replace_decl(text,'norm_planeFourierRemainder_eq_scale_mul_torusRemainder',RING_OLD,RING_NEW,'remainder_ring_nf');changes.append(r)
 text,r=replace_decl(text,'weightedFull_apply_core',WEIGHT_OLD,{'change':WEIGHT_CHANGE,'show':WEIGHT_SHOW,'simp':WEIGHT_SIMP}[wmode],'weighted_pointwise');changes.append(r)
 if adj:
  text,r=replace_decl(text,'euclideanRaiseTestAdjoint_conjugate_eq_conj_affineTranspose',ADJ_OLD,ADJ_NEW,'adj_raise_fderiv');changes.append(r)
  text,r=replace_decl(text,'euclideanLowerFromSuccTestAdjoint_conjugate_eq_conj_affineTranspose',ADJ_OLD,ADJ_NEW,'adj_lower_fderiv');changes.append(r)
 after_headers=decl_headers(text);after_trust=trust_counts(text)
 if after_headers!=before_headers:raise SystemExit('headers/order changed')
 if after_trust!=before_trust or any(after_trust.values()):raise SystemExit(f'trust mismatch {after_trust}')
 outb=text.encode();a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_bytes(outb)
 audit={'schema':'fa-v50-cumulative-safe-matrix-v1','variant':a.variant,'base_sha256':BASE_SHA,'source_sha256':sha(outb),'source_bytes':len(outb),'source_lines':len(text.splitlines()),'declaration_count':len(DECL_RE.findall(text)),'declaration_headers_identical':True,'trust_before':before_trust,'trust_after':after_trust,'changes':changes}
 a.audit.parent.mkdir(parents=True,exist_ok=True);a.audit.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n');print(json.dumps(audit,indent=2,sort_keys=True))
if __name__=='__main__':main()
