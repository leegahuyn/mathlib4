#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa493_prepare_graph_density_nonneg.py"
spec = importlib.util.spec_from_file_location("fa493base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa493 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa493
spec.loader.exec_module(fa493)

fa466 = fa493.fa466
orig_norm_repairs = fa493.norm_repairs

EXACT_FA493_VARIANT = "explicit_add_mul_nonneg"
REQUIRED_FA493_EVIDENCE_RUN_ID = "31460205923"
REQUIRED_FA493_EVIDENCE_JOB_ID = "93682055075"
REQUIRED_FA493_EVIDENCE_HEAD_SHA = "7611dae00b47dbac9801744c4f4c821eca8dd9c0"
REQUIRED_FA493_SOURCE_SHA256 = "8a0be67731e5cc1314b0ff81829a73b6845612bdf14fa51a648c4442378d3ee9"
REQUIRED_FA493_FIRST_ERROR_LINE = "35567"
REQUIRED_FA493_FIRST_ERROR_COL = "6"
REQUIRED_FA493_FRONTIER_DECLARATION = "selectedHeightGraphDensity_eq_scale_mul_fixedPhaseDensity"
REQUIRED_FA493_FRONTIER_INDEX = "2816"

TARGET_DECLARATION = REQUIRED_FA493_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2816
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA493_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = """  rw [← fixedPhaseEuclideanGauge_raise n u,
    ← fixedPhaseEuclideanGauge_lower_pred n u]"""
NEW_FRAGMENT = """  simp only [Prod.fst, Prod.snd]
  rw [← fixedPhaseEuclideanGauge_raise n u, ← fixedPhaseEuclideanGauge_lower_pred n u]"""

VARIANTS = {
    "zeta_then_rewrite": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "zeta-reduce local lets and product projections before reusing the existing raise/lower gauge rewrites",
    ),
}

def sha(s: str) -> str: return hashlib.sha256(s.encode()).hexdigest()
def bounds(text: str, name: str):
    xs=list(_DECL_START.finditer(text)); hs=[i for i,m in enumerate(xs) if m.group('name')==name]
    if len(hs)!=1: raise RuntimeError(f"expected one {name}, found {len(hs)}")
    i=hs[0]; return xs[i].start(), xs[i+1].start() if i+1<len(xs) else len(text)
def header(region: str):
    p=region.find(':=')
    if p<0: raise RuntimeError('target header has no :=')
    return region[:p+2]
def req(k: str, v: str):
    if os.environ.get(k)!=v: raise RuntimeError(f"FA494 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text: str):
    for k,v in [
        ('FA493_VARIANT',EXACT_FA493_VARIANT),
        ('FA493_EVIDENCE_RUN_ID',REQUIRED_FA493_EVIDENCE_RUN_ID),
        ('FA493_EVIDENCE_JOB_ID',REQUIRED_FA493_EVIDENCE_JOB_ID),
        ('FA493_EVIDENCE_HEAD_SHA',REQUIRED_FA493_EVIDENCE_HEAD_SHA),
        ('FA493_EVIDENCE_SOURCE_SHA256',REQUIRED_FA493_SOURCE_SHA256),
        ('FA493_FIRST_ERROR_LINE',REQUIRED_FA493_FIRST_ERROR_LINE),
        ('FA493_FIRST_ERROR_COL',REQUIRED_FA493_FIRST_ERROR_COL),
        ('FA493_FRONTIER_DECLARATION',REQUIRED_FA493_FRONTIER_DECLARATION),
        ('FA493_FRONTIER_INDEX',REQUIRED_FA493_FRONTIER_INDEX),
    ]: req(k,v)
    variant=os.environ.get('FA494_VARIANT')
    if variant not in VARIANTS: raise RuntimeError(f"unsupported FA494_VARIANT={variant!r}")
    text, repairs=orig_norm_repairs(text)
    if sha(text)!=EXPECTED_INTERMEDIATE_SOURCE_SHA256: raise RuntimeError(f"FA494 exact FA493 source mismatch: {sha(text)}")
    if len(text.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA494 line-count drift before patch')
    start,end=bounds(text,TARGET_DECLARATION); pre,reg,suf=text[:start],text[start:end],text[end:]; h=header(reg)
    replacements,strategy=VARIANTS[variant]
    audit=[]
    for old,new in replacements:
        oc,nc=reg.count(old),reg.count(new)
        if oc!=1 or nc!=0: raise RuntimeError(f"FA494 target old/new counts {oc}/{nc}, expected 1/0")
        reg=reg.replace(old,new,1)
        audit.append({'old_count_before':oc,'old_global_count_before':text.count(old),'new_count_before':nc,'new_global_count_before':text.count(new),'old_sha256':sha(old),'new_sha256':sha(new)})
    cand=pre+reg+suf
    if header(reg)!=h: raise RuntimeError('FA494 header drift')
    before=[m.group('name') for m in _DECL_START.finditer(text)]; after=[m.group('name') for m in _DECL_START.finditer(cand)]
    if before!=after: raise RuntimeError('FA494 declaration sequence drift')
    if len(cand.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA494 candidate line count changed')
    meta={'fa493_intermediate_source_sha256':sha(text),'candidate_source_sha256':sha(cand),'required_line_count':EXPECTED_LINE_COUNT,'candidate_line_count':len(cand.splitlines()),'target_header_sha256':sha(h),'target_header_preserved':True,'source_prefix_preserved':cand[:start]==pre,'source_suffix_preserved':cand[start+len(reg):]==suf,'declaration_sequence_preserved':True,'replacement_audit':audit}
    return cand, repairs + [
        {'declaration':TARGET_DECLARATION,'declaration_index':TARGET_DECLARATION_INDEX,'strategy':strategy,'matrix_variant':variant,'required_fa493_evidence_run_id':int(REQUIRED_FA493_EVIDENCE_RUN_ID),'required_fa493_evidence_job_id':int(REQUIRED_FA493_EVIDENCE_JOB_ID),'required_fa493_evidence_head_sha':REQUIRED_FA493_EVIDENCE_HEAD_SHA,'required_fa493_source_sha256':REQUIRED_FA493_SOURCE_SHA256,'required_fa493_first_error_line':int(REQUIRED_FA493_FIRST_ERROR_LINE),'required_fa493_first_error_col':int(REQUIRED_FA493_FIRST_ERROR_COL),'frontier_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0,'max_errors':32,**meta},
        {'declaration':'FA494 strict-frontier repair','strategy':variant,'target_declaration':TARGET_DECLARATION,'target_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0},
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__': fa466.main()
