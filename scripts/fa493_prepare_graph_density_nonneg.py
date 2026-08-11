#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa492_prepare_endpoint_explicit_continuity.py"
spec = importlib.util.spec_from_file_location("fa492base", BASE)
if spec is None or spec.loader is None: raise RuntimeError(f"cannot load {BASE}")
fa492 = importlib.util.module_from_spec(spec); sys.modules[spec.name] = fa492; spec.loader.exec_module(fa492)
fa466 = fa492.fa466
orig_norm_repairs = fa492.norm_repairs

EXACT_FA492_VARIANT = "typed_pointwise_endpoint"
REQUIRED_FA492_EVIDENCE_RUN_ID = "31459499507"
REQUIRED_FA492_EVIDENCE_JOB_ID = "93680057199"
REQUIRED_FA492_EVIDENCE_HEAD_SHA = "76e10532282d2ec9264b11f43ce5ab8a82073065"
REQUIRED_FA492_SOURCE_SHA256 = "266bb3bd12fc43826cbbff63297e1ad2b6399c652b54d69e888eeab3344a8856"
REQUIRED_FA492_FIRST_ERROR_LINE = "35540"
REQUIRED_FA492_FIRST_ERROR_COL = "2"
REQUIRED_FA492_FRONTIER_DECLARATION = "fixedPhaseEuclideanGraphDensity_nonneg"
REQUIRED_FA492_FRONTIER_INDEX = "2814"

TARGET_DECLARATION = REQUIRED_FA492_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2814
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA492_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535
_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_LINE = "  positivity"
NEW_LINE = "  exact add_nonneg (add_nonneg (mul_nonneg (logHeightTraceBaseCoeff_nonneg n) (sq_nonneg _)) (mul_nonneg (by norm_num) (sq_nonneg _))) (mul_nonneg (by norm_num) (sq_nonneg _))"

def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def bounds(text,name):
    xs=list(_DECL_START.finditer(text)); hs=[i for i,m in enumerate(xs) if m.group('name')==name]
    if len(hs)!=1: raise RuntimeError(f"expected one {name}, found {len(hs)}")
    i=hs[0]; return xs[i].start(), xs[i+1].start() if i+1<len(xs) else len(text)
def header(region):
    p=region.find(':=')
    if p<0: raise RuntimeError('no :=')
    return region[:p+2]
def req(k,v):
    if os.environ.get(k)!=v: raise RuntimeError(f"FA493 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text):
    for k,v in [
        ('FA492_VARIANT',EXACT_FA492_VARIANT),('FA492_EVIDENCE_RUN_ID',REQUIRED_FA492_EVIDENCE_RUN_ID),
        ('FA492_EVIDENCE_JOB_ID',REQUIRED_FA492_EVIDENCE_JOB_ID),('FA492_EVIDENCE_HEAD_SHA',REQUIRED_FA492_EVIDENCE_HEAD_SHA),
        ('FA492_EVIDENCE_SOURCE_SHA256',REQUIRED_FA492_SOURCE_SHA256),('FA492_FIRST_ERROR_LINE',REQUIRED_FA492_FIRST_ERROR_LINE),
        ('FA492_FIRST_ERROR_COL',REQUIRED_FA492_FIRST_ERROR_COL),('FA492_FRONTIER_DECLARATION',REQUIRED_FA492_FRONTIER_DECLARATION),
        ('FA492_FRONTIER_INDEX',REQUIRED_FA492_FRONTIER_INDEX),('FA493_VARIANT','explicit_add_mul_nonneg')]: req(k,v)
    text, repairs = orig_norm_repairs(text)
    if sha(text)!=EXPECTED_INTERMEDIATE_SOURCE_SHA256: raise RuntimeError(f"FA493 exact FA492 source mismatch: {sha(text)}")
    if len(text.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA493 line-count drift before patch')
    start,end=bounds(text,TARGET_DECLARATION); pre,reg,suf=text[:start],text[start:end],text[end:]; h=header(reg)
    if reg.count(OLD_LINE)!=1 or reg.count(NEW_LINE)!=0: raise RuntimeError('FA493 target pattern mismatch')
    reg2=reg.replace(OLD_LINE,NEW_LINE,1); cand=pre+reg2+suf
    if header(reg2)!=h: raise RuntimeError('FA493 header drift')
    before=[m.group('name') for m in _DECL_START.finditer(text)]; after=[m.group('name') for m in _DECL_START.finditer(cand)]
    if before!=after: raise RuntimeError('FA493 declaration sequence drift')
    if len(cand.splitlines())!=EXPECTED_LINE_COUNT: raise RuntimeError('FA493 candidate line count changed')
    audit={"fa492_intermediate_source_sha256":sha(text),"candidate_source_sha256":sha(cand),"required_line_count":EXPECTED_LINE_COUNT,"candidate_line_count":len(cand.splitlines()),"target_header_sha256":sha(h),"target_header_preserved":True,"source_prefix_preserved":cand[:start]==pre,"source_suffix_preserved":cand[start+len(reg2):]==suf,"declaration_sequence_preserved":True}
    return cand, repairs + [{"declaration":TARGET_DECLARATION,"declaration_index":TARGET_DECLARATION_INDEX,"strategy":"replace failing bare positivity with explicit add_nonneg/mul_nonneg using logHeightTraceBaseCoeff_nonneg and squared-norm nonnegativity","matrix_variant":"explicit_add_mul_nonneg","required_fa492_evidence_run_id":int(REQUIRED_FA492_EVIDENCE_RUN_ID),"required_fa492_evidence_job_id":int(REQUIRED_FA492_EVIDENCE_JOB_ID),"required_fa492_evidence_head_sha":REQUIRED_FA492_EVIDENCE_HEAD_SHA,"required_fa492_source_sha256":REQUIRED_FA492_SOURCE_SHA256,"required_fa492_first_error_line":int(REQUIRED_FA492_FIRST_ERROR_LINE),"required_fa492_first_error_col":int(REQUIRED_FA492_FIRST_ERROR_COL),"frontier_declaration_index":TARGET_DECLARATION_INDEX,"later_repair_count":0,"max_errors":32,**audit},{"declaration":"FA493 strict-frontier repair","strategy":"explicit_add_mul_nonneg","target_declaration":TARGET_DECLARATION,"target_declaration_index":TARGET_DECLARATION_INDEX,"later_repair_count":0}]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__': fa466.main()
