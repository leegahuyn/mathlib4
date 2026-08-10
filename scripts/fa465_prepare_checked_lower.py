#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

ROOT=Path.cwd()
SOURCE=ROOT/'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
BASE_SHA='b51c2ddcdfec8b98a89734575ef57b681f47eefba8b879028a3233439b70906a'
BASE_LINES=60474
DECL_RE=re.compile(r'^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)',re.MULTILINE)

def sha(b:bytes)->str:return hashlib.sha256(b).hexdigest()
def span(text,name):
    ms=list(DECL_RE.finditer(text))
    for i,m in enumerate(ms):
        if m.group(1)==name:return m.start(),ms[i+1].start() if i+1<len(ms) else len(text)
    raise RuntimeError(f'missing declaration {name}')
def header(text,name):
    a,b=span(text,name); block=text[a:b]; p=block.find(':=')
    if p<0:raise RuntimeError(f'no := in {name}')
    return block[:p+2]
def replace_body(text,name,proof):
    a,b=span(text,name); block=text[a:b]; p=block.find(':='); suffix='\n' if block.endswith('\n') else ''
    if p<0:raise RuntimeError(f'no := in {name}')
    return text[:a]+block[:p+2]+' '+proof.rstrip()+'\n'+suffix+text[b:]
def replace_in(text,name,old,new):
    a,b=span(text,name); block=text[a:b]; c=block.count(old)
    if c!=1:raise RuntimeError(f'{name}: expected one replacement, found {c}: {old!r}')
    return text[:a]+block.replace(old,new,1)+text[b:]

LOWER_RW='''by
  have hScale := euclideanGaugeScale_succ (n - 1) z
  have hExponent := euclideanGaugeExponent_succ (n - 1)
  rw [sub_add_cancel] at hScale hExponent
  simp only [fixedPhaseEuclideanGauge_apply,
    InverseEtaFixedPhaseCore.lower_apply]
  unfold euclideanLowerFromSuccGauge lowerRaw
  rw [dx_fixedPhaseEuclideanGauge, dy_fixedPhaseEuclideanGauge,
    complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply, hScale, hExponent]
  have hz : heightC z ≠ 0 :=
    Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  push_cast
  ring'''

LOWER_SIMPRW='''by
  have hScale := euclideanGaugeScale_succ (n - 1) z
  have hExponent := euclideanGaugeExponent_succ (n - 1)
  rw [sub_add_cancel] at hScale hExponent
  simp only [fixedPhaseEuclideanGauge_apply,
    InverseEtaFixedPhaseCore.lower_apply]
  unfold euclideanLowerFromSuccGauge lowerRaw
  rw [dx_fixedPhaseEuclideanGauge, dy_fixedPhaseEuclideanGauge,
    complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply]
  simp_rw [hScale, hExponent]
  have hz : heightC z ≠ 0 :=
    Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  push_cast
  ring'''

LOWER_SIMP='''by
  have hScale := euclideanGaugeScale_succ (n - 1) z
  have hExponent := euclideanGaugeExponent_succ (n - 1)
  rw [sub_add_cancel] at hScale hExponent
  simp only [fixedPhaseEuclideanGauge_apply,
    InverseEtaFixedPhaseCore.lower_apply]
  unfold euclideanLowerFromSuccGauge lowerRaw
  rw [dx_fixedPhaseEuclideanGauge, dy_fixedPhaseEuclideanGauge,
    complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply]
  simp only [hScale, hExponent]
  have hz : heightC z ≠ 0 :=
    Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  push_cast
  ring'''

HORIZONTAL='''by
  rw [euclideanRaiseGauge_sub_lowerPredGauge]
  have hcoef : (-Complex.I / 2) * (2 * Complex.I) = (1 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  calc
    heightC z * dx f z = 1 * (heightC z * dx f z) := by ring
    _ = ((-Complex.I / 2) * (2 * Complex.I)) *
        (heightC z * dx f z) := by rw [hcoef]
    _ = (-Complex.I / 2) *
        (2 * Complex.I * heightC z * dx f z) := by ring'''

PROOFS={'lower_rw':LOWER_RW,'lower_simprw':LOWER_SIMPRW,'lower_simp':LOWER_SIMP}

def main():
    p=argparse.ArgumentParser(); p.add_argument('--variant',required=True,choices=['baseline',*PROOFS,'lower_simprw_horizontal','lower_simprw_horizontal_norm']); p.add_argument('--output-dir',required=True); a=p.parse_args()
    out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True)
    raw=SOURCE.read_bytes()
    if sha(raw)!=BASE_SHA:raise RuntimeError(f'checked champion SHA mismatch {sha(raw)} != {BASE_SHA}')
    text=raw.decode();
    if len(text.splitlines())!=BASE_LINES:raise RuntimeError('checked champion line count mismatch')
    seq=[m.group(1) for m in DECL_RE.finditer(text)]
    protected=['actualEdgeAmbientParam_hasDerivAt','fixedPhaseEuclideanGauge_lower_pred','height_mul_dx_eq_negI_half_raise_sub_lower_sub','norm_height_mul_dx_le_euclideanGraph']
    heads={n:header(text,n) for n in protected}
    cand=text;repairs=[]
    if a.variant!='baseline':
        lower='lower_simprw' if a.variant.startswith('lower_simprw_horizontal') else a.variant
        cand=replace_body(cand,'fixedPhaseEuclideanGauge_lower_pred',PROOFS[lower]);repairs.append({'declaration':'fixedPhaseEuclideanGauge_lower_pred','strategy':lower})
    if a.variant.startswith('lower_simprw_horizontal'):
        cand=replace_body(cand,'height_mul_dx_eq_negI_half_raise_sub_lower_sub',HORIZONTAL);repairs.append({'declaration':'height_mul_dx_eq_negI_half_raise_sub_lower_sub','strategy':'explicit_I_coefficient'})
    if a.variant=='lower_simprw_horizontal_norm':
        cand=replace_in(cand,'norm_height_mul_dx_le_euclideanGraph','exact add_le_add_right (norm_sub_le _ _) _','exact add_le_add (norm_sub_le R L) (le_refl ‖c * f z‖)');repairs.append({'declaration':'norm_height_mul_dx_le_euclideanGraph','strategy':'fully_typed_add_le_add'})
    cseq=[m.group(1) for m in DECL_RE.finditer(cand)]
    if cseq!=seq:raise RuntimeError('declaration sequence changed')
    for n,h in heads.items():
        if header(cand,n)!=h:raise RuntimeError(f'declaration proposition changed: {n}')
    SOURCE.write_text(cand);data=SOURCE.read_bytes()
    meta={'variant':a.variant,'baseline_sha256':BASE_SHA,'candidate_sha256':sha(data),'line_count':len(cand.splitlines()),'baseline_line_count':BASE_LINES,'target_declaration':'actualEdgeAmbientParam_hasDerivAt','target_header_sha256':sha(heads['actualEdgeAmbientParam_hasDerivAt'].encode()),'declaration_sequence_sha256':sha(json.dumps(cseq,separators=(',',':')).encode()),'declaration_count':len(cseq),'repairs':repairs}
    (out/'CANDIDATE.json').write_text(json.dumps(meta,indent=2,ensure_ascii=False)+'\n');(out/'Mock2_FunctionalAnalysis-candidate.lean').write_bytes(data);print(json.dumps(meta,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
