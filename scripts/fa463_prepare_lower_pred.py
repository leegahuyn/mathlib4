#!/usr/bin/env python3
from __future__ import annotations

import argparse, hashlib, importlib.util, json, re, sys
from pathlib import Path

ROOT=Path.cwd(); SOURCE=ROOT/'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
BASE_SHA='1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb'
DECL_RE=re.compile(r'^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)',re.MULTILINE)
spec=importlib.util.spec_from_file_location('fa461base',ROOT/'scripts/fa461_prepare_gl_analytic_cluster1.py')
if spec is None or spec.loader is None: raise RuntimeError('cannot load base')
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
    simpa [sub_eq_add_neg, add_comm] using hExponent
  have hExponentNorm' :
      1 + euclideanGaugeExponent (-1 + n) = euclideanGaugeExponent n := by
    linarith
'''+COMMON_BODY+'''  rw [hExponentNorm']
  ring'''
PROOF_NORMALIZED_POW=COMMON_PREFIX+'''  have hExponentNorm :
      euclideanGaugeExponent n = euclideanGaugeExponent (-1 + n) + 1 := by
    simpa [sub_eq_add_neg, add_comm] using hExponent
  have hPowNorm :
      ((z.im ^ (1 + euclideanGaugeExponent (-1 + n)) : ℝ) : ℂ) =
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) := by
    congr 2
    linarith
'''+COMMON_BODY+'''  rw [hPowNorm]
  ring'''
PROOFS={'lower_pow_linarith':PROOF_POW_LINARITH,'lower_pow_ring':PROOF_POW_RING,'lower_pow_before':PROOF_POW_BEFORE,'lower_normalized':PROOF_NORMALIZED,'lower_normalized_pow':PROOF_NORMALIZED_POW}

def main():
    p=argparse.ArgumentParser(); p.add_argument('--variant',required=True,choices=['baseline','gl_cumulative',*PROOFS]); p.add_argument('--output-dir',required=True); a=p.parse_args()
    out=Path(a.output_dir); out.mkdir(parents=True,exist_ok=True)
    raw=SOURCE.read_bytes()
    if sha(raw)!=BASE_SHA: raise RuntimeError(f'baseline SHA {sha(raw)}')
    text=raw.decode(); seq=[m.group(1) for m in DECL_RE.finditer(text)]
    protected=['actualEdgeAmbientParam_hasDerivAt','fixedPhaseEuclideanGauge_lower_pred']
    heads={n:header(text,n) for n in protected}
    cand=text; repairs=[]
    if a.variant!='baseline':
        cand,rs=base.apply_gl_pair_cumulative(cand); repairs+=rs
    if a.variant in PROOFS:
        cand=replace_body(cand,'fixedPhaseEuclideanGauge_lower_pred',PROOFS[a.variant]); repairs.append({'declaration':'fixedPhaseEuclideanGauge_lower_pred','strategy':a.variant})
    if [m.group(1) for m in DECL_RE.finditer(cand)]!=seq: raise RuntimeError('declaration sequence changed')
    for n,h in heads.items():
        if header(cand,n)!=h: raise RuntimeError(f'header changed {n}')
    SOURCE.write_text(cand); data=SOURCE.read_bytes(); cseq=[m.group(1) for m in DECL_RE.finditer(cand)]
    meta={'variant':a.variant,'baseline_sha256':BASE_SHA,'candidate_sha256':sha(data),'line_count':len(cand.splitlines()),'target_declaration':'actualEdgeAmbientParam_hasDerivAt','target_header_sha256':sha(heads['actualEdgeAmbientParam_hasDerivAt'].encode()),'declaration_sequence_sha256':sha(json.dumps(cseq,separators=(',',':')).encode()),'declaration_count':len(cseq),'repairs':repairs}
    (out/'CANDIDATE.json').write_text(json.dumps(meta,indent=2,ensure_ascii=False)+'\n'); (out/'Mock2_FunctionalAnalysis-candidate.lean').write_bytes(data); print(json.dumps(meta,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
