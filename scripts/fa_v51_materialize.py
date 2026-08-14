#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path
BASE_SHA='e37ac30b388bee8b46f4316209740c6e86a8a7bb2bc8c2277e08f7f62da3e7dc'
BASE_BYTES=2798434
BASE_LINES=62621
BASE_DECLS=4416
TRUST=('sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool')
DECL_RE=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
def sha(b): return hashlib.sha256(b).hexdigest()
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
 code=strip_noncode(text);return {x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',code)) for x in TRUST}
def ranges(text):
 ms=list(DECL_RE.finditer(text));return {m.group(1):(m.start(),ms[i+1].start() if i+1<len(ms) else len(text)) for i,m in enumerate(ms)}
def headers(text):
 out=[]
 for n,(a,b) in ranges(text).items():
  block=text[a:b];p=block.find(':=');out.append((n,block[:p].rstrip()))
 return out
def repl(text,name,old,new,label):
 a,b=ranges(text)[name];block=text[a:b];n=block.count(old)
 if n!=1:raise RuntimeError(f'{label}: expected 1 in {name}, got {n}')
 return text[:a]+block.replace(old,new,1)+text[b:],{'label':label,'declaration':name}

E9_ONE='''  case e'_9 =>
    simp [id]
'''
E9_ONE_RING='''  case e'_9 =>
    simp [id]
    ring
'''
E9_ONE_RINGNF='''  case e'_9 =>
    simp [id]
    ring_nf
'''
E9_I=E9_ONE
E9_I_RING=E9_ONE_RING
E9_I_RINGNF=E9_ONE_RINGNF

DX_HRIGHT_OLD='''    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by rw [hdx_apply w])
'''
DX_HRIGHT_CHANGE='''    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by
            change literalStageNegativePlaneWave Y k w *
                HalfWeightCompactCoordinateGreen.dx v w =
              literalStageNegativePlaneWave Y k w *
                (fderiv ℝ (v : ℂ → ℂ) w) 1
            rw [hdx_apply w])
'''
DX_HRIGHT_SIMPA='''    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by
            simpa only [Pi.mul_apply] using
              congrArg (fun z : ℂ ↦ literalStageNegativePlaneWave Y k w * z)
                (hdx_apply w))
'''
DX_CALC_OLD='''      apply integral_congr_ae
      filter_upwards with w
      rw [hdx_apply w]
'''
DX_CALC_CHANGE='''      apply integral_congr_ae
      filter_upwards with w
      change literalStageNegativePlaneWave Y k w *
          HalfWeightCompactCoordinateGreen.dx v w =
        literalStageNegativePlaneWave Y k w *
          (fderiv ℝ (v : ℂ → ℂ) w) 1
      rw [hdx_apply w]
'''
DX_CALC_SIMPA='''      apply integral_congr_ae
      filter_upwards with w
      simpa only [Pi.mul_apply] using
        congrArg (fun z : ℂ ↦ literalStageNegativePlaneWave Y k w * z)
          (hdx_apply w)
'''
DY_HRIGHT_OLD='''    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by rw [hdy_apply w])
'''
DY_HRIGHT_CHANGE='''    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by
            change literalStageNegativePlaneWave Y k w *
                HalfWeightCompactCoordinateGreen.dy v w =
              literalStageNegativePlaneWave Y k w *
                (fderiv ℝ (v : ℂ → ℂ) w) Complex.I
            rw [hdy_apply w])
'''
DY_HRIGHT_SIMPA='''    exact (((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left).congr
          (Filter.Eventually.of_forall fun w ↦ by
            simpa only [Pi.mul_apply] using
              congrArg (fun z : ℂ ↦ literalStageNegativePlaneWave Y k w * z)
                (hdy_apply w))
'''
DY_CALC_OLD='''      apply integral_congr_ae
      filter_upwards with w
      rw [hdy_apply w]
'''
DY_CALC_CHANGE='''      apply integral_congr_ae
      filter_upwards with w
      change literalStageNegativePlaneWave Y k w *
          HalfWeightCompactCoordinateGreen.dy v w =
        literalStageNegativePlaneWave Y k w *
          (fderiv ℝ (v : ℂ → ℂ) w) Complex.I
      rw [hdy_apply w]
'''
DY_CALC_SIMPA='''      apply integral_congr_ae
      filter_upwards with w
      simpa only [Pi.mul_apply] using
        congrArg (fun z : ℂ ↦ literalStageNegativePlaneWave Y k w * z)
          (hdy_apply w)
'''
REM_OLD='''  simpa only [mul_pow] using hsq <;> ring_nf
'''
REM_NEW='''  simpa only [mul_pow, mul_comm] using hsq
'''
ADJ_OLD='''  rw [hfun, hfderiv]
  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply, sub_eq_add_neg,
'''
ADJ_NEW='''  rw [hfun]
  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply]
  rw [hfderiv]
  simp only [sub_eq_add_neg,
'''
FORWARD_OLD='''  rw [pairwise_disjoint_smul_iff]
  intro a ha
  exact gammaTwoReducedChart_inter_translate_imp_eq_one z₀ a <| by
    simpa only [image_smul] using ha
'''
FORWARD_NEW='''  rw [pairwise_disjoint_smul_iff]
  intro a ha
  have hinter : (((a • ·) '' gammaTwoReducedChart z₀) ∩
      gammaTwoReducedChart z₀).Nonempty := by
    simpa only [image_smul] using ha
  have hfixA : a • z₀ = z₀ :=
    gammaTwoReducedChart_inter_translate_imp_smul_eq z₀ a hinter
  obtain ⟨gamma, hgamma⟩ := effective_exists_gamma a
  have hfix : ((gamma : SL(2, ℤ)) • z₀) = z₀ := by
    change gamma • z₀ = z₀
    exact (hgamma z₀).symm.trans hfixA
  obtain ⟨delta, hdelta⟩ := ModularGroup.exists_smul_mem_fd z₀
  let w : ℍ := delta • z₀
  let conjugate : SL(2, ℤ) :=
    delta * (gamma : SL(2, ℤ)) * delta⁻¹
  have hConjugateMem : conjugate ∈ CongruenceSubgroup.Gamma 2 := by
    exact (CongruenceSubgroup.Gamma_normal 2).conj_mem
      (gamma : SL(2, ℤ)) gamma.property delta
  have hConjugateFix : conjugate • w = w := by
    dsimp only [conjugate, w]
    simp only [mul_smul, inv_smul_smul, hfix]
  have hCentral : conjugate = 1 ∨ conjugate = -1 := by
    have hcases := ModularGroup.cases_of_mem_fd_smul_mem_fd
      (g := conjugate) hdelta (hConjugateFix.symm ▸ hdelta)
    rcases hcases with hpm | hT | hTinv | hS | hTS | hTinvSTinv |
        hSTinv | hST | hTST | hTinvS
    · exact hpm
    · rcases hT.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hTinv.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hS.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hTS.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hTinvSTinv.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hSTinv.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hST.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hTST.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
    · rcases hTinvS.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hConjugateMem <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hConjugateMem
  have hGamma : gamma = 1 ∨ gamma = gammaTwoCentralNegOne := by
    rcases hCentral with hOne | hNeg
    · left
      apply Subtype.ext
      have h := congrArg
        (fun b : SL(2, ℤ) ↦ delta⁻¹ * b * delta) hOne
      simpa [conjugate, mul_assoc] using h
    · right
      apply Subtype.ext
      have h := congrArg
        (fun b : SL(2, ℤ) ↦ delta⁻¹ * b * delta) hNeg
      simpa [conjugate, gammaTwoCentralNegOne_coe, mul_assoc] using h
  apply Subtype.ext
  apply Equiv.ext
  intro z
  change a • z = (1 : GammaTwoEffective) • z
  rw [hgamma z]
  rcases hGamma with rfl | rfl
  · simp only [one_smul]
  · change ((gammaTwoCentralNegOne : GammaTwo) : SL(2, ℤ)) • z = z
    exact gammaTwoCentralNegOne_smul z
'''
VARIANTS={
 'ring_change_noadj':('ring','change',False,False),
 'ring_change_adj':('ring','change',True,False),
 'ring_change_adj_forward':('ring','change',True,True),
 'ringnf_change_adj':('ring_nf','change',True,False),
 'ring_simpa_adj':('ring','simpa',True,False),
 'ring_simpa_adj_forward':('ring','simpa',True,True),
}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,required=True);ap.add_argument('--variant',choices=VARIANTS,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--audit',type=Path,required=True);a=ap.parse_args()
 raw=a.base.read_bytes();text=raw.decode()
 if sha(raw)!=BASE_SHA or len(raw)!=BASE_BYTES or len(text.splitlines())!=BASE_LINES or len(DECL_RE.findall(text))!=BASE_DECLS:raise SystemExit('base identity mismatch')
 bh=headers(text);bt=trust(text);changes=[]
 ringmode,dxmode,adj,fwd=VARIANTS[a.variant]
 text,r=repl(text,'fderiv_literalStageNegativePlaneWave_one',E9_ONE,E9_ONE_RING if ringmode=='ring' else E9_ONE_RINGNF,'deriv_one_ring');changes.append(r)
 text,r=repl(text,'fderiv_literalStageNegativePlaneWave_I',E9_I,E9_I_RING if ringmode=='ring' else E9_I_RINGNF,'deriv_I_ring');changes.append(r)
 text,r=repl(text,'integral_negativePlaneWave_mul_dx',DX_HRIGHT_OLD,DX_HRIGHT_CHANGE if dxmode=='change' else DX_HRIGHT_SIMPA,'dx_integrable_pointwise');changes.append(r)
 text,r=repl(text,'integral_negativePlaneWave_mul_dx',DX_CALC_OLD,DX_CALC_CHANGE if dxmode=='change' else DX_CALC_SIMPA,'dx_integral_pointwise');changes.append(r)
 text,r=repl(text,'integral_negativePlaneWave_mul_dy',DY_HRIGHT_OLD,DY_HRIGHT_CHANGE if dxmode=='change' else DY_HRIGHT_SIMPA,'dy_integrable_pointwise');changes.append(r)
 text,r=repl(text,'integral_negativePlaneWave_mul_dy',DY_CALC_OLD,DY_CALC_CHANGE if dxmode=='change' else DY_CALC_SIMPA,'dy_integral_pointwise');changes.append(r)
 text,r=repl(text,'norm_planeFourierRemainder_eq_scale_mul_torusRemainder',REM_OLD,REM_NEW,'remainder_mul_comm');changes.append(r)
 if adj:
  text,r=repl(text,'euclideanRaiseTestAdjoint_conjugate_eq_conj_affineTranspose',ADJ_OLD,ADJ_NEW,'adj_raise_reorder');changes.append(r)
  text,r=repl(text,'euclideanLowerFromSuccTestAdjoint_conjugate_eq_conj_affineTranspose',ADJ_OLD,ADJ_NEW,'adj_lower_reorder');changes.append(r)
 if fwd:
  text,r=repl(text,'gammaTwoReducedChart_pairwise_disjoint_translates',FORWARD_OLD,FORWARD_NEW,'reduced_chart_inline_free_action');changes.append(r)
 ah=headers(text);at=trust(text)
 if ah!=bh:raise SystemExit('headers/order changed')
 if at!=bt or any(at.values()):raise SystemExit(f'trust mismatch {at}')
 outb=text.encode();a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_bytes(outb)
 audit={'schema':'fa-v51-frontier-safe-matrix-v1','variant':a.variant,'base_sha256':BASE_SHA,'source_sha256':sha(outb),'source_bytes':len(outb),'source_lines':len(text.splitlines()),'declaration_count':len(DECL_RE.findall(text)),'declaration_headers_identical':True,'trust_before':bt,'trust_after':at,'changes':changes}
 a.audit.parent.mkdir(parents=True,exist_ok=True);a.audit.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n');print(json.dumps(audit,indent=2,sort_keys=True))
if __name__=='__main__':main()
