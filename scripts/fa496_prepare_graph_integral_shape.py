#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa495_prepare_orbit_l2_inner_field.py"
spec = importlib.util.spec_from_file_location("fa495base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa495 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa495
spec.loader.exec_module(fa495)

fa466 = fa495.fa466
orig_norm_repairs = fa495.norm_repairs

EXACT_FA495_VARIANT = "complex_scalar_field"
REQUIRED_FA495_EVIDENCE_RUN_ID = "31464238170"
REQUIRED_FA495_EVIDENCE_JOB_ID = "93693691898"
REQUIRED_FA495_EVIDENCE_HEAD_SHA = "a791a5deea1de804049c44cebbc6b5f04fde1032"
REQUIRED_FA495_SOURCE_SHA256 = "0cea98064a3970aa66099eec020fc787910584231a7dac68f5e27c71d5aa32bd"
REQUIRED_FA495_FIRST_ERROR_LINE = "35642"
REQUIRED_FA495_FIRST_ERROR_COL = "6"
REQUIRED_FA495_FRONTIER_DECLARATION = "integral_fixedPhaseEuclideanGraphDensity_eq_coordinates"
REQUIRED_FA495_FRONTIER_INDEX = "2821"

TARGET_DECLARATION = REQUIRED_FA495_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2821
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA495_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = """  rw [integral_add ((hBase.const_mul _).add (hRaise.const_mul _))
      (hLower.const_mul _),
    integral_add (hBase.const_mul _) (hRaise.const_mul _),"""
NEW_FRAGMENT = """  rw [integral_add (f := fun z => logHeightTraceBaseCoeff n * ‖fixedPhaseEuclideanGauge n u z‖ ^ 2 + 3 * ‖fixedPhaseEuclideanGauge (n + 1) (InverseEtaFixedPhaseCore.raise n u) z‖ ^ 2) (g := fun z => 3 * ‖fixedPhaseEuclideanGauge (n - 1) (InverseEtaFixedPhaseCore.lower n u) z‖ ^ 2) ((hBase.const_mul _).add (hRaise.const_mul _))
      (hLower.const_mul _),
    integral_add (f := fun z => logHeightTraceBaseCoeff n * ‖fixedPhaseEuclideanGauge n u z‖ ^ 2) (g := fun z => 3 * ‖fixedPhaseEuclideanGauge (n + 1) (InverseEtaFixedPhaseCore.raise n u) z‖ ^ 2) (hBase.const_mul _) (hRaise.const_mul _),"""

VARIANTS = {
    "named_pointwise_integrands": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "pin integral_add implicit f/g to the exact pointwise lambda integrands while reusing the existing integrability witnesses",
    ),
}

def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()

def bounds(text: str, name: str):
    xs = list(_DECL_START.finditer(text)); hs = [i for i,m in enumerate(xs) if m.group('name') == name]
    if len(hs) != 1: raise RuntimeError(f"expected one {name}, found {len(hs)}")
    i = hs[0]; return xs[i].start(), xs[i+1].start() if i+1 < len(xs) else len(text)

def header(region: str):
    p = region.find(':=')
    if p < 0: raise RuntimeError('target header has no :=')
    return region[:p+2]

def req(k: str, v: str):
    if os.environ.get(k) != v: raise RuntimeError(f"FA496 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text: str):
    for k,v in [
        ('FA495_VARIANT', EXACT_FA495_VARIANT),
        ('FA495_EVIDENCE_RUN_ID', REQUIRED_FA495_EVIDENCE_RUN_ID),
        ('FA495_EVIDENCE_JOB_ID', REQUIRED_FA495_EVIDENCE_JOB_ID),
        ('FA495_EVIDENCE_HEAD_SHA', REQUIRED_FA495_EVIDENCE_HEAD_SHA),
        ('FA495_EVIDENCE_SOURCE_SHA256', REQUIRED_FA495_SOURCE_SHA256),
        ('FA495_FIRST_ERROR_LINE', REQUIRED_FA495_FIRST_ERROR_LINE),
        ('FA495_FIRST_ERROR_COL', REQUIRED_FA495_FIRST_ERROR_COL),
        ('FA495_FRONTIER_DECLARATION', REQUIRED_FA495_FRONTIER_DECLARATION),
        ('FA495_FRONTIER_INDEX', REQUIRED_FA495_FRONTIER_INDEX),
    ]: req(k,v)
    variant = os.environ.get('FA496_VARIANT')
    if variant not in VARIANTS: raise RuntimeError(f"unsupported FA496_VARIANT={variant!r}")
    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA496 exact FA495 source mismatch: {sha(text)}")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA496 line-count drift before patch')
    start,end = bounds(text,TARGET_DECLARATION); pre,reg,suf = text[:start],text[start:end],text[end:]; h = header(reg)
    replacements,strategy = VARIANTS[variant]; audit = []
    for old,new in replacements:
        oc,nc = reg.count(old),reg.count(new)
        if oc != 1 or nc != 0: raise RuntimeError(f"FA496 target old/new counts {oc}/{nc}, expected 1/0")
        reg = reg.replace(old,new,1)
        audit.append({'old_count_before':oc,'old_global_count_before':text.count(old),'new_count_before':nc,'new_global_count_before':text.count(new),'old_sha256':sha(old),'new_sha256':sha(new)})
    cand = pre + reg + suf
    if header(reg) != h: raise RuntimeError('FA496 header drift')
    before = [m.group('name') for m in _DECL_START.finditer(text)]; after = [m.group('name') for m in _DECL_START.finditer(cand)]
    if before != after: raise RuntimeError('FA496 declaration sequence drift')
    if len(cand.splitlines()) != EXPECTED_LINE_COUNT: raise RuntimeError('FA496 candidate line count changed')
    meta = {'fa495_intermediate_source_sha256':sha(text),'candidate_source_sha256':sha(cand),'required_line_count':EXPECTED_LINE_COUNT,'candidate_line_count':len(cand.splitlines()),'target_header_sha256':sha(h),'target_header_preserved':True,'source_prefix_preserved':cand[:start]==pre,'source_suffix_preserved':cand[start+len(reg):]==suf,'declaration_sequence_preserved':True,'replacement_audit':audit}
    return cand, repairs + [
        {'declaration':TARGET_DECLARATION,'declaration_index':TARGET_DECLARATION_INDEX,'strategy':strategy,'matrix_variant':variant,'required_fa495_evidence_run_id':int(REQUIRED_FA495_EVIDENCE_RUN_ID),'required_fa495_evidence_job_id':int(REQUIRED_FA495_EVIDENCE_JOB_ID),'required_fa495_evidence_head_sha':REQUIRED_FA495_EVIDENCE_HEAD_SHA,'required_fa495_source_sha256':REQUIRED_FA495_SOURCE_SHA256,'required_fa495_first_error_line':int(REQUIRED_FA495_FIRST_ERROR_LINE),'required_fa495_first_error_col':int(REQUIRED_FA495_FIRST_ERROR_COL),'frontier_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0,'max_errors':32,**meta},
        {'declaration':'FA496 strict-frontier repair','strategy':variant,'target_declaration':TARGET_DECLARATION,'target_declaration_index':TARGET_DECLARATION_INDEX,'later_repair_count':0},
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__': fa466.main()
