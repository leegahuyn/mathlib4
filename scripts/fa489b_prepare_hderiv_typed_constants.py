#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa488_prepare_hpoint_typed_by.py"
spec = importlib.util.spec_from_file_location("fa488base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa488 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa488
spec.loader.exec_module(fa488)
fa466 = fa488.fa466
orig_norm_repairs = fa488.norm_repairs

REQ_RUN="31456106488"; REQ_JOB="93670098634"; REQ_HEAD="ca9f7071476b843379f67765ca43ba7cc327d6be"
REQ_SOURCE="efabb4d229666d7a6e292e853aa583833ae6c99d0bb6d65689168015eccb93ca"
TARGET="selectedLogHeightEnergyDensity_continuous"; TARGET_INDEX=2806; EXPECTED_LINES=60535
_DECL=re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD="""    rw [hExplicit]
    fun_prop"""
NEW="""    rw [hExplicit]
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ => ((Real.exp (p.2 / 2) : ℝ) : ℂ))).mul ((((continuous_const : Continuous (fun _ : ℝ × ℝ => (1 / 2 : ℂ))).mul hcomp).add ((HalfWeightDifferentialOperators.realSmooth_heightC.continuous.comp hpoint).mul hdycomp)))"""

def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def bounds(text):
    ms=list(_DECL.finditer(text)); hits=[i for i,m in enumerate(ms) if m.group('name')==TARGET]
    if len(hits)!=1: raise RuntimeError(f"expected one {TARGET}, found {len(hits)}")
    i=hits[0]; return ms[i].start(), ms[i+1].start() if i+1<len(ms) else len(text)
def req(k,v):
    if os.environ.get(k)!=v: raise RuntimeError(f"FA489-B requires {k}={v}, got {os.environ.get(k)!r}")
def norm_repairs(text):
    req('FA488_VARIANT','typed_by'); req('FA488_EVIDENCE_RUN_ID',REQ_RUN); req('FA488_EVIDENCE_JOB_ID',REQ_JOB)
    req('FA488_EVIDENCE_HEAD_SHA',REQ_HEAD); req('FA488_EVIDENCE_SOURCE_SHA256',REQ_SOURCE)
    req('FA488_FIRST_ERROR_LINE','35337'); req('FA488_FIRST_ERROR_COL','4'); req('FA488_FRONTIER_DECLARATION',TARGET); req('FA488_FRONTIER_INDEX',str(TARGET_INDEX))
    req('FA489B_VARIANT','typed_constants')
    text,repairs=orig_norm_repairs(text)
    if sha(text)!=REQ_SOURCE: raise RuntimeError(f"FA489-B upstream source mismatch {sha(text)}")
    if len(text.splitlines())!=EXPECTED_LINES: raise RuntimeError('FA489-B line-count drift')
    a,b=bounds(text); region=text[a:b]
    if region.count(OLD)!=1 or region.count(NEW)!=0: raise RuntimeError('FA489-B target occurrence mismatch')
    candidate=text[:a]+region.replace(OLD,NEW,1)+text[b:]
    if len(candidate.splitlines())!=EXPECTED_LINES: raise RuntimeError('FA489-B candidate line-count changed')
    before=[m.group('name') for m in _DECL.finditer(text)]; after=[m.group('name') for m in _DECL.finditer(candidate)]
    if before!=after: raise RuntimeError('FA489-B declaration sequence drift')
    return candidate, repairs+[
      {'declaration':TARGET,'declaration_index':TARGET_INDEX,'strategy':'explicit derivative continuity using typed half constant plus existing hcomp/hdycomp/hpoint','matrix_variant':'typed_constants','required_fa488_evidence_run_id':int(REQ_RUN),'required_fa488_evidence_job_id':int(REQ_JOB),'required_fa488_evidence_head_sha':REQ_HEAD,'required_fa488_source_sha256':REQ_SOURCE,'required_fa488_first_error_line':35337,'required_fa488_first_error_col':4,'candidate_source_sha256':sha(candidate),'candidate_line_count':len(candidate.splitlines()),'declaration_sequence_preserved':True,'later_repair_count':0,'max_errors':32},
      {'declaration':'FA489 matrix candidate B','strategy':'typed_constants','target_declaration':TARGET,'target_declaration_index':TARGET_INDEX,'later_repair_count':0}
    ]
fa466.norm_repairs=norm_repairs
if __name__=='__main__': fa466.main()
