#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa494_prepare_height_graph_zeta_rewrite.py"
spec = importlib.util.spec_from_file_location("fa494base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa494 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa494
spec.loader.exec_module(fa494)

fa466 = fa494.fa466
orig_norm_repairs = fa494.norm_repairs

EXACT_FA494_VARIANT = "zeta_then_rewrite"
REQUIRED_FA494_EVIDENCE_RUN_ID = "31463480421"
REQUIRED_FA494_EVIDENCE_JOB_ID = "93691559188"
REQUIRED_FA494_EVIDENCE_HEAD_SHA = "d6c811a4419b75fb0494e14e1095d5c036ed53ae"
REQUIRED_FA494_SOURCE_SHA256 = "0c12385bb59897283b26f5e0065dcee042d784b4e16013f54d34808c7b562328"
REQUIRED_FA494_FIRST_ERROR_LINE = "35577"
REQUIRED_FA494_FIRST_ERROR_COL = "8"
REQUIRED_FA494_FRONTIER_DECLARATION = "orbitEuclideanL2_norm_sq_eq_integral"
REQUIRED_FA494_FRONTIER_INDEX = "2817"

TARGET_DECLARATION = REQUIRED_FA494_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2817
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA494_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = """  rw [← inner_self_eq_norm_sq, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner F F)]"""
NEW_FRAGMENT = """  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner F F)]"""

VARIANTS = {
    "complex_scalar_field": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "pin the scalar field of inner_self_eq_norm_sq to Complex so InnerProductSpace typeclass resolution is no longer metavariable-stuck",
    ),
}

def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()

def bounds(text: str, name: str):
    xs=list(_DECL_START.finditer(text)); hs=[i for i,m in enumerate(xs) if m.group('name')==name]
    if len(hs)!=1: raise RuntimeError(f"expected one {name}, found {len(hs)}")
    i=hs[0]; return xs[i].start(), xs[i+1].start() if i+1<len(xs) else len(text)

def header(region: str):
    p=region.find(':=')
    if p<0: raise RuntimeError('target header has no :=')
    return region[:p+2]

def req(k: str, v: str):
    if os.environ.get(k)!=v: raise RuntimeError(f"FA495 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text: str):
    for k,v in [
        ('FA494_VARIANT',EXACT_FA494_VARIANT),
        ('FA494_EVIDENCE_RUN_ID',REQUIRED_FA494_EVIDENCE_RUN_ID),
        ('FA494_EVIDENCE_JOB_ID',REQUIRED_FA494_EVIDENCE_JOB_ID),
        ('FA494_EVIDENCE_HEAD_SHA',REQUIRED_FA494_EVIDENCE_HEAD_SHA),
        ('FA494_EVIDENCE_SOURCE_SHA256',REQUIRED_FA494_SOURCE_SHA256),
        ('FA494_FIRST_ERROR_LINE',REQUIRED_FA494_FIRST_ERROR_LINE),
        ('FA494_FIRST_ERROR_COL',REQUIRED_FA494_FIRST_ERROR_COL),
        ('FA494_FRONTIER_DECLARATION',REQUIRED_FA494_FRONTIER_DECLARATION),
        ('FA494_FRONTIER_INDEX',REQUIRED_FA494_FRONTIER_INDEX),
    ]: req(k,v)
    variant=os.environ.get('FA495_VARIANT')
    if variant not in VARIANTS: raise RuntimeError(f"unsupported FA495_VARIANT={variant!r}")
    text, repairs=orig_norm_repairs(text)
    if sha(text)!=EXPECTED_INTERMEDIATE_SOURCE_SHA256: raise RuntimeError(f"FA495 exact FA494 source mismatch: {sha(text)}")
    if len(text.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA495 line-count drift before patch')
    start,end=bounds(text,TARGET_DECLARATION); pre,reg,suf=text[:start],text[start:end],text[end:]; h=header(reg)
    replacements,strategy=VARIANTS[variant]; audit=[]
    for old,new in replacements:
        oc,nc=reg.count(old),reg.count(new)
        if oc!=1 or nc!=0: raise RuntimeError(f"FA495 target old/new counts {oc}/{nc}, expected 1/0")
        reg=reg.replace(old,new,1)
        audit.append({'old_count_before':oc,'old_global_count_before':text.count(old),'new_count_before':nc,'new_global_count_before':text.count(new),'old_sha256':sha(old),'new_sha256':sha(new)})
    cand=pre+reg+suf
    if header(reg)!=h: raise RuntimeError('FA495 header drift')
    before=[m.group('name') for m in _DECL_START.finditer(text)]; after=[m.group('name') for m in _DECL_START.finditer(cand)]
    if before!=after: raise RuntimeError('FA495 declaration sequence drift')
    if len(cand.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA495 candidate line count changed')
    meta={'fa494_intermediate_source_sha256':sha(text),'candidate_source_sha256':sha(cand),'required_line_count':EXPECTED_LINE_COUNT,'candidate_line_count':len(cand.splitlines()),'target_header_sha256':sha(h),'target_header_preserved':True,'source_prefix_preserved':cand[:start]==pre,'source_suffix_preserved':cand[start+len(reg):]==suf,'declaration_sequence_preserved':True,'replacement_audit':audit}
    return cand, repairs + [
        {'declaration':TARGET_DECLARATION,'declaration_index':TARGET_DECLARATION_INDEX,'strategy':strategy,'matrix_variant':variant,'required_fa494_evidence_run_id':int(REQUIRED_FA494_EVIDENCE_RUN_ID),'required_fa494_evidence_job_id':int(REQUIRED_FA494_EVIDENCE_JOB_ID),'required_fa494_evidence_head_sha':REQUIRED_FA494_EVIDENCE_HEAD_SHA,'required_fa494_source_sha256':REQUIRED_FA494_SOURCE_SHA256,'required_fa494_first_error_line':int(REQUIRED_FA494_FIRST_ERROR_LINE),'required_fa494_first_error_col':int(REQUIRED_FA494_FIRST_ERROR_COL),'frontier_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0,'max_errors':32,**meta},
        {'declaration':'FA495 strict-frontier repair','strategy':variant,'target_declaration':TARGET_DECLARATION,'target_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0},
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__': fa466.main()
