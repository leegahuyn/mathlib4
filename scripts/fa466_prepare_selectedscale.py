#!/usr/bin/env python3
from __future__ import annotations
import argparse, importlib.util, json, sys
from pathlib import Path

ROOT=Path.cwd()
spec=importlib.util.spec_from_file_location('fa465base',ROOT/'scripts/fa465_prepare_checked_lower.py')
if spec is None or spec.loader is None: raise RuntimeError('cannot load FA465 preparer')
b=importlib.util.module_from_spec(spec);sys.modules[spec.name]=b;spec.loader.exec_module(b)

LOWER_CONFIRMED='''by
  have hScale := euclideanGaugeScale_succ (n - 1) z
  have hExponent := euclideanGaugeExponent_succ (n - 1)
  rw [sub_add_cancel] at hScale hExponent
  simp only [fixedPhaseEuclideanGauge_apply,
    InverseEtaFixedPhaseCore.lower_apply]
  unfold euclideanLowerFromSuccGauge lowerRaw
  rw [dx_fixedPhaseEuclideanGauge, dy_fixedPhaseEuclideanGauge,
    complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply]
  rw [hScale, hExponent]
  have hz : heightC z ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  push_cast
  ring'''
SMOOTH='''by
  have hnum : RealSmooth (fun z => heightC (selectedCosetAction q z)) :=
    RealSmooth.comp_selectedCosetAction realSmooth_heightC q
  have hdenInv : RealSmooth (fun z => (heightC z)⁻¹) :=
    RealSmooth.inv realSmooth_heightC (fun z => heightC_ne_zero z)
  simpa only [selectedCosetConformalScaleC, div_eq_mul_inv] using
    (RealSmooth.mul hnum hdenInv)'''
SCALE_EQ='''by
  have haction : selectedCosetAction q z = selectedCosetGL q • z := by
    apply UpperHalfPlane.ext
    simp [selectedCosetAction, selectedCosetGL]
  unfold selectedCosetConformalScaleC
  rw [haction]
  unfold heightC
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp only [selectedCosetGL_det, Int.reduceAbs, one_mul,
    Complex.ofReal_div, Complex.ofReal_one]
  field_simp [z.im_ne_zero]'''
NORM_DERIV='''by
  have hden := selectedCosetDenom_ne_zero q z
  rw [selectedCosetConformalScaleC_eq_inv_normSq_denom]
  unfold selectedCosetDerivative
  rw [Complex.norm_real, abs_of_pos (one_div_pos.mpr
    (Complex.normSq_pos.mpr hden)), norm_div, norm_one, norm_pow,
    Complex.normSq_eq_norm_sq]'''

def base_repairs(text):
    text=b.replace_body(text,'fixedPhaseEuclideanGauge_lower_pred',LOWER_CONFIRMED)
    text=b.replace_body(text,'height_mul_dx_eq_negI_half_raise_sub_lower_sub',b.HORIZONTAL)
    text=b.replace_in(text,'norm_height_mul_dx_le_euclideanGraph','exact add_le_add_right (norm_sub_le _ _) _','exact add_le_add (norm_sub_le R L) (le_refl ‖c * f z‖)')
    return text,[{'declaration':'fixedPhaseEuclideanGauge_lower_pred','strategy':'direct_verified_all_relations_last_ring'},{'declaration':'height_mul_dx_eq_negI_half_raise_sub_lower_sub','strategy':'explicit_I_coefficient'},{'declaration':'norm_height_mul_dx_le_euclideanGraph','strategy':'typed_add_le_add'}]

def smooth_repairs(text):
    text=b.replace_body(text,'selectedCosetConformalScaleC_realSmooth',SMOOTH)
    return text,[{'declaration':'selectedCosetConformalScaleC_realSmooth','strategy':'fully_qualified_RealSmooth_inv_mul'}]

def scale_repairs(text):
    text=b.replace_body(text,'selectedCosetConformalScaleC_eq_inv_normSq_denom',SCALE_EQ)
    return text,[{'declaration':'selectedCosetConformalScaleC_eq_inv_normSq_denom','strategy':'explicit_selectedCosetGL_action'}]

def dxdy_repairs(text):
    for name in ['dx_selectedCosetConformalScaleC','dy_selectedCosetConformalScaleC']:
        text=b.replace_in(text,name,'realSmooth_heightC.inv (fun w => heightC_ne_zero w)','RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)')
    text=b.replace_in(text,'dy_selectedCosetConformalScaleC','add_zero] using','add_zero, zero_add] using')
    return text,[{'declaration':'dx/dy_selectedCosetConformalScaleC','strategy':'qualified_RealSmooth_inv_and_zero_add'}]

def norm_repairs(text):
    text=b.replace_body(text,'norm_selectedCosetConformalScaleC_eq_derivative',NORM_DERIV)
    text=b.replace_in(text,'norm_selectedCosetA_le_scale','simp only [selectedCosetA, Complex.norm_real]','simp only [selectedCosetA, Complex.norm_real, Real.norm_eq_abs]')
    text=b.replace_in(text,'norm_selectedCosetB_le_scale','simp only [selectedCosetB, Complex.norm_real]','simp only [selectedCosetB, Complex.norm_real, Real.norm_eq_abs]')
    text=b.replace_in(text,'norm_height_mul_dy_selectedCosetConformalScaleC_le','exact add_le_add_right (norm_selectedCosetA_le_scale q z) _','exact add_le_add (norm_selectedCosetA_le_scale q z) (le_refl ‖selectedCosetConformalScaleC q z‖)')
    return text,[{'declaration':'selectedCoset norm bounds','strategy':'keep_denom_folded_real_norm_and_typed_add'}]

def main():
    p=argparse.ArgumentParser();p.add_argument('--variant',required=True,choices=['baseline','confirmed_norm','smooth','scaleeq','dxdy','norms']);p.add_argument('--output-dir',required=True);a=p.parse_args()
    out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True);raw=b.SOURCE.read_bytes()
    if b.sha(raw)!=b.BASE_SHA:raise RuntimeError(f'checked champion SHA mismatch: {b.sha(raw)}')
    text=raw.decode();seq=[m.group(1) for m in b.DECL_RE.finditer(text)]
    protected=['actualEdgeAmbientParam_hasDerivAt','fixedPhaseEuclideanGauge_lower_pred','height_mul_dx_eq_negI_half_raise_sub_lower_sub','norm_height_mul_dx_le_euclideanGraph','selectedCosetConformalScaleC_realSmooth','selectedCosetConformalScaleC_eq_inv_normSq_denom','dx_selectedCosetConformalScaleC','dy_selectedCosetConformalScaleC','norm_selectedCosetConformalScaleC_eq_derivative','norm_selectedCosetA_le_scale','norm_selectedCosetB_le_scale']
    heads={n:b.header(text,n) for n in protected};cand=text;rep=[]
    if a.variant!='baseline': cand,rs=base_repairs(cand);rep+=rs
    if a.variant in ['smooth','scaleeq','dxdy','norms']: cand,rs=smooth_repairs(cand);rep+=rs
    if a.variant in ['scaleeq','dxdy','norms']: cand,rs=scale_repairs(cand);rep+=rs
    if a.variant in ['dxdy','norms']: cand,rs=dxdy_repairs(cand);rep+=rs
    if a.variant=='norms': cand,rs=norm_repairs(cand);rep+=rs
    cseq=[m.group(1) for m in b.DECL_RE.finditer(cand)]
    if cseq!=seq:raise RuntimeError('declaration sequence changed')
    for n,h in heads.items():
        if b.header(cand,n)!=h:raise RuntimeError(f'declaration proposition changed: {n}')
    b.SOURCE.write_text(cand);data=b.SOURCE.read_bytes();meta={'variant':a.variant,'baseline_sha256':b.BASE_SHA,'candidate_sha256':b.sha(data),'line_count':len(cand.splitlines()),'target_declaration':'actualEdgeAmbientParam_hasDerivAt','target_header_sha256':b.sha(heads['actualEdgeAmbientParam_hasDerivAt'].encode()),'declaration_sequence_sha256':b.sha(json.dumps(cseq,separators=(',',':')).encode()),'declaration_count':len(cseq),'repairs':rep};(out/'CANDIDATE.json').write_text(json.dumps(meta,indent=2,ensure_ascii=False)+'\n');(out/'Mock2_FunctionalAnalysis-candidate.lean').write_bytes(data);print(json.dumps(meta,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
