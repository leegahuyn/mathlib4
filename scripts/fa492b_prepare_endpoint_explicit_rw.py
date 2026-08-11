#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa491_prepare_strip_fubini_prod_restrict.py"
spec = importlib.util.spec_from_file_location("fa491base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa491 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa491
spec.loader.exec_module(fa491)
fa466 = fa491.fa466
orig_norm_repairs = fa491.norm_repairs

EXACT_FA491_VARIANT = "rewrite_prod_restrict_then_fubini"
REQUIRED_FA491_EVIDENCE_RUN_ID = "31458257120"
REQUIRED_FA491_EVIDENCE_JOB_ID = "93676458948"
REQUIRED_FA491_EVIDENCE_HEAD_SHA = "d030aecf662d3f8ff36d5d0776a7ddc93f4c1e70"
REQUIRED_FA491_SOURCE_SHA256 = "ccea869bcd941660cf537806e8ce53a8af242685751bc81e16ff4a6256a8023d"
REQUIRED_FA491_FIRST_ERROR_LINE = "35507"
REQUIRED_FA491_FIRST_ERROR_COL = "6"
REQUIRED_FA491_FRONTIER_DECLARATION = "norm_selectedCuspCoreTrace_sq_le_logHeightEnergy"
REQUIRED_FA491_FRONTIER_INDEX = "2812"
TARGET_DECLARATION = REQUIRED_FA491_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2812
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA491_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535
_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")

OLD_FRAGMENT = """      unfold selectedLogHeightNaturalGauge
      fun_prop"""
NEW_FRAGMENT = """      have hpoint : Continuous (fun t : ℝ => logHeightBasePoint t (Real.log (gammaTwoCuspLevel Y))) := by unfold logHeightBasePoint; exact (((by rw [show (fun t : ℝ => Complex.mk t (Real.exp (Real.log (gammaTwoCuspLevel Y)))) = fun t : ℝ => ((t : ℝ) : ℂ) + (((Real.exp (Real.log (gammaTwoCuspLevel Y)) : ℝ) : ℂ) * Complex.I) by funext t; exact Complex.mk_eq_add_mul_I t (Real.exp (Real.log (gammaTwoCuspLevel Y)))]; fun_prop) : Continuous (fun t : ℝ => Complex.mk t (Real.exp (Real.log (gammaTwoCuspLevel Y))))).upperHalfPlaneMk (fun (_ : ℝ) => Real.exp_pos (Real.log (gammaTwoCuspLevel Y))))
      unfold selectedLogHeightNaturalGauge; simpa only [h] using ((continuous_const.mul (hh.continuous.comp hpoint)).norm.pow 2)"""
VARIANTS = {"explicit_rw_hpoint": (((OLD_FRAGMENT, NEW_FRAGMENT),), "use the already verified typed Complex.mk continuity pattern with an explicit rw/show equality, then compose hh.continuous at the fixed endpoint")}

def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()

def bounds(text: str, declaration: str):
    starts=list(_DECL_START.finditer(text)); hits=[i for i,m in enumerate(starts) if m.group('name')==declaration]
    if len(hits)!=1: raise RuntimeError(f"expected one {declaration}, found {len(hits)}")
    i=hits[0]; return starts[i].start(), starts[i+1].start() if i+1<len(starts) else len(text)

def header(region: str):
    p=region.find(':=')
    if p<0: raise RuntimeError('target header has no :=')
    return region[:p+2]

def req(name, expected):
    actual=os.environ.get(name)
    if actual!=expected: raise RuntimeError(f"FA492B requires {name}={expected}, got {actual!r}")

def replace_target(text, replacements):
    actual=sha256_text(text)
    if actual!=EXPECTED_INTERMEDIATE_SOURCE_SHA256: raise RuntimeError(f"FA492B requires exact FA491 source {EXPECTED_INTERMEDIATE_SOURCE_SHA256}, got {actual}")
    if len(text.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA492B intermediate line-count drift')
    start,end=bounds(text,TARGET_DECLARATION); prefix,region,suffix=text[:start],text[start:end],text[end:]; old_header=header(region); audit=[]
    for old,new in replacements:
        oc,nc=region.count(old),region.count(new)
        if oc!=1 or nc!=0: raise RuntimeError(f"target old/new counts {oc}/{nc}, expected 1/0")
        region=region.replace(old,new,1); audit.append({'old_count_before':oc,'old_global_count_before':text.count(old),'new_count_before':nc,'new_global_count_before':text.count(new),'old_sha256':sha256_text(old),'new_sha256':sha256_text(new)})
    candidate=prefix+region+suffix
    if header(region)!=old_header: raise RuntimeError('FA492B header drift')
    before=[m.group('name') for m in _DECL_START.finditer(text)]; after=[m.group('name') for m in _DECL_START.finditer(candidate)]
    if before!=after: raise RuntimeError('FA492B declaration sequence drift')
    if len(candidate.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA492B candidate line count changed')
    return candidate, {'fa491_intermediate_source_sha256':actual,'candidate_source_sha256':sha256_text(candidate),'required_line_count':EXPECTED_LINE_COUNT,'candidate_line_count':len(candidate.splitlines()),'replacement_count':len(replacements),'target_header_sha256':sha256_text(old_header),'target_header_preserved':True,'source_prefix_preserved':candidate[:start]==prefix,'source_suffix_preserved':candidate[start+len(region):]==suffix,'declaration_sequence_sha256':sha256_text('\n'.join(before)),'declaration_sequence_preserved':True,'replacement_audit':audit}

def norm_repairs(text: str):
    req('FA491_VARIANT',EXACT_FA491_VARIANT); req('FA491_EVIDENCE_RUN_ID',REQUIRED_FA491_EVIDENCE_RUN_ID); req('FA491_EVIDENCE_JOB_ID',REQUIRED_FA491_EVIDENCE_JOB_ID); req('FA491_EVIDENCE_HEAD_SHA',REQUIRED_FA491_EVIDENCE_HEAD_SHA); req('FA491_EVIDENCE_SOURCE_SHA256',REQUIRED_FA491_SOURCE_SHA256); req('FA491_FIRST_ERROR_LINE',REQUIRED_FA491_FIRST_ERROR_LINE); req('FA491_FIRST_ERROR_COL',REQUIRED_FA491_FIRST_ERROR_COL); req('FA491_FRONTIER_DECLARATION',REQUIRED_FA491_FRONTIER_DECLARATION); req('FA491_FRONTIER_INDEX',REQUIRED_FA491_FRONTIER_INDEX)
    variant=os.environ.get('FA492B_VARIANT')
    if variant not in VARIANTS: raise RuntimeError(f"unsupported FA492B_VARIANT={variant!r}")
    text,repairs=orig_norm_repairs(text); replacements,strategy=VARIANTS[variant]; text,audit=replace_target(text,replacements)
    return text, repairs + [{'declaration':TARGET_DECLARATION,'declaration_index':TARGET_DECLARATION_INDEX,'strategy':strategy,'matrix_variant':variant,'required_fa491_evidence_run_id':int(REQUIRED_FA491_EVIDENCE_RUN_ID),'required_fa491_evidence_job_id':int(REQUIRED_FA491_EVIDENCE_JOB_ID),'required_fa491_evidence_head_sha':REQUIRED_FA491_EVIDENCE_HEAD_SHA,'required_fa491_source_sha256':REQUIRED_FA491_SOURCE_SHA256,'required_fa491_first_error_line':int(REQUIRED_FA491_FIRST_ERROR_LINE),'required_fa491_first_error_col':int(REQUIRED_FA491_FIRST_ERROR_COL),'frontier_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0,'max_errors':32,**audit},{'declaration':'FA492B sibling strict-frontier repair','strategy':variant,'target_declaration':TARGET_DECLARATION,'target_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0}]

fa466.norm_repairs=norm_repairs
if __name__=='__main__': fa466.main()
