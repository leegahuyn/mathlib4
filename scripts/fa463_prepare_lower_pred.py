#!/usr/bin/env python3
from __future__ import annotations

import argparse, hashlib, importlib.util, json, re, sys
from pathlib import Path

ROOT=Path.cwd(); SOURCE=ROOT/'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
BASE_SHA='1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb'
DECL_RE=re.compile(r'^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)',re.MULTILINE)

spec=importlib.util.spec_from_file_location('fa459base',ROOT/'scripts/fa459_prepare_true_first_cluster.py')
if spec is None or spec.loader is None: raise RuntimeError('cannot load FA459 base')
base=importlib.util.module_from_spec(spec); sys.modules[spec.name]=base; spec.loader.exec_module(base)

def sha(b:bytes)->str:return hashlib.sha256(b).hexdigest()
def span(text,name):
    ms=list(DECL_RE.finditer(text))
    for i,m in enumerate(ms):
        if m.group(1)==name:return m.start(),ms[i+1].start() if i+1<len(ms) else len(text)
    raise RuntimeError(f'missing {name}')
def header(text,name):
    a,b=span(text,name); block=text[a:b]; p=block.find(':=')
    if p<0: raise RuntimeError(f'no := {name}')
    return block[:p+2]
def replace_body(text,name,proof):
    a,b=span(text,name); block=text[a:b]; p=block.find(':='); suffix='\n' if block.endswith('\n') else ''
    return text[:a]+block[:p+2]+' '+proof.rstrip()+'\n'+suffix+text[b:]
def replace_in(text,name,old,new):
    a,b=span(text,name); block=text[a:b]; c=block.count(old)
    if c!=1: raise RuntimeError(f'{name}: expected one replacement, found {c}')
    return text[:a]+block.replace(old,new,1)+text[b:]

GL_SELECTED_AE='''by
  change selectedCosetGL q • modularHalfOpenTile =ᵐ[hyperbolicMeasure]
    selectedCosetGL q • ModularGroup.fdo
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq
    (selectedCosetGL q)
    (measurePreserving_smul (selectedCosetGL q)⁻¹
      hyperbolicMeasure).quasiMeasurePreserving
    modularHalfOpenTile_ae_eq_fdo'''
HSELECTED_OLD='''  have hSelectedTile : MeasurableSet
      (gammaTwoCosetRep q • modularHalfOpenTile) :=
    MeasurableSet.const_smul modularHalfOpenTile_measurable
      (gammaTwoCosetRep q)'''
HSELECTED_GL='''  have hSelectedTile : MeasurableSet
      (gammaTwoCosetRep q • modularHalfOpenTile) := by
    change MeasurableSet (selectedCosetGL q • modularHalfOpenTile)
    exact MeasurableSet.const_smul modularHalfOpenTile_measurable
      (selectedCosetGL q)'''

def apply_gl_pair_cumulative(text):
    repairs=[]
    text,r=base.apply_pair_compat(text,'macro'); repairs.append(r)
    text=replace_body(text,'selectedHalfOpenTile_ae_eq_openTile',GL_SELECTED_AE)
    repairs.append({'declaration':'selectedHalfOpenTile_ae_eq_openTile','strategy':'selectedCosetGL_invariant_measure'})
    text=replace_in(text,'integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola',HSELECTED_OLD,HSELECTED_GL)
    repairs.append({'declaration':'integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola','strategy':'selectedCosetGL_measurable_const_smul'})
    text,rs=base.fa458.apply_cumulative(text,'direct_union'); repairs.extend(rs)
    return text,repairs

COMMON_PREFIX='''by
  have hScale := euclideanGaugeScale_succ (n - 1) z
  have hExponent := euclideanGaugeExponent_succ (n - 1)
  rw [sub_add_cancel] at hScale hExponent
'''
COMMON_BODY='''  simp only [fixedPhaseEuclideanGauge_apply,
    InverseEtaFixedPhaseCore.lower_apply]
  unfold euclideanLowerFromSuccGauge lowerRaw
  rw [dx_fixedPhaseEuclideanGauge, dy_fixedPhaseEuclideanGauge,
    hScale, hExponent, complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply]
  have hz : heightC z ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
'''
PROOF_POW_LINARITH=COMMON_PREFIX+'''  have hExponent' :
      1 + euclideanGaugeExponent (n - 1) = euclideanGaugeExponent n := by
    linarith
'''+COMMON_BODY+'''  rw [hExponent']
  ring'''
PROOF_POW_RING=COMMON_PREFIX+'''  have hExponent' :
      1 + euclideanGaugeExponent (n - 1) = euclideanGaugeExponent n := by
    rw [hExponent]
    ring
'''+COMMON_BODY+'''  rw [hExponent']
  ring'''
PROOF_POW_BEFORE=COMMON_PREFIX+'''  have hPow :
      ((z.im ^ (1 + euclideanGaugeExponent (n - 1)) : ℝ) : ℂ) =
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) := by
    have he : 1 + euclideanGaugeExponent (n - 1) = euclideanGaugeExponent n := by
      rw [hExponent]
      ring
    rw [he]
'''+COMMON_BODY+'''  rw [hPow]
  ring'''
PROOF_NORMALIZED=COMMON_PREFIX+'''  have hExponentNorm :
      euclideanGaugeExponent n = euclideanGaugeExponent (-1 + n) + 1 := by
    have hIndex : -1 + n = n - 1 := by ring
    rw [hIndex]
    exact hExponent
  have hExponentNorm' :
      1 + euclideanGaugeExponent (-1 + n) = euclideanGaugeExponent n := by
    linarith
'''+COMMON_BODY+'''  rw [hExponentNorm']
  ring'''
PROOF_NORMALIZED_POW=COMMON_PREFIX+'''  have hExponentNorm :
      euclideanGaugeExponent n = euclideanGaugeExponent (-1 + n) + 1 := by
    have hIndex : -1 + n = n - 1 := by ring
    rw [hIndex]
    exact hExponent
  have hPowNorm :
      ((z.im ^ (1 + euclideanGaugeExponent (-1 + n)) : ℝ) : ℂ) =
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) := by
    have he : 1 + euclideanGaugeExponent (-1 + n) = euclideanGaugeExponent n := by linarith
    rw [he]
'''+COMMON_BODY+'''  rw [hPowNorm]
  ring'''
PROOFS={'lower_pow_linarith':PROOF_POW_LINARITH,'lower_pow_ring':PROOF_POW_RING,'lower_pow_before':PROOF_POW_BEFORE,'lower_normalized':PROOF_NORMALIZED,'lower_normalized_pow':PROOF_NORMALIZED_POW}

def main():
    p=argparse.ArgumentParser(); p.add_argument('--variant',required=True,choices=['baseline','gl_cumulative',*PROOFS]); p.add_argument('--output-dir',required=True); a=p.parse_args()
    out=Path(a.output_dir); out.mkdir(parents=True,exist_ok=True)
    raw=SOURCE.read_bytes()
    if sha(raw)!=BASE_SHA: raise RuntimeError(f'baseline SHA {sha(raw)}')
    text=raw.decode(); seq=[m.group(1) for m in DECL_RE.finditer(text)]
    protected=['actualEdgeAmbientParam_hasDerivAt','fixedPhaseEuclideanGauge_lower_pred','selectedHalfOpenTile_ae_eq_openTile','integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola']
    heads={n:header(text,n) for n in protected}
    cand=text; repairs=[]
    if a.variant!='baseline':
        cand,rs=apply_gl_pair_cumulative(cand); repairs+=rs
    if a.variant in PROOFS:
        cand=replace_body(cand,'fixedPhaseEuclideanGauge_lower_pred',PROOFS[a.variant]); repairs.append({'declaration':'fixedPhaseEuclideanGauge_lower_pred','strategy':a.variant})
    if [m.group(1) for m in DECL_RE.finditer(cand)]!=seq: raise RuntimeError('declaration sequence changed')
    for n,h in heads.items():
        if header(cand,n)!=h: raise RuntimeError(f'header changed {n}')
    SOURCE.write_text(cand); data=SOURCE.read_bytes(); cseq=[m.group(1) for m in DECL_RE.finditer(cand)]
    meta={'variant':a.variant,'baseline_sha256':BASE_SHA,'candidate_sha256':sha(data),'line_count':len(cand.splitlines()),'target_declaration':'actualEdgeAmbientParam_hasDerivAt','target_header_sha256':sha(heads['actualEdgeAmbientParam_hasDerivAt'].encode()),'declaration_sequence_sha256':sha(json.dumps(cseq,separators=(',',':')).encode()),'declaration_count':len(cseq),'repairs':repairs}
    (out/'CANDIDATE.json').write_text(json.dumps(meta,indent=2,ensure_ascii=False)+'\n'); (out/'Mock2_FunctionalAnalysis-candidate.lean').write_bytes(data); print(json.dumps(meta,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
