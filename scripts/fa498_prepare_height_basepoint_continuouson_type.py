#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa497_prepare_height_basepoint_mk_continuity.py"
spec = importlib.util.spec_from_file_location("fa497base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa497 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa497
spec.loader.exec_module(fa497)

fa466 = fa497.fa466
orig_norm_repairs = fa497.norm_repairs

EXACT_FA497_VARIANT = "mk_eq_add_mul_i_continuous_on"
REQUIRED_FA497_EVIDENCE_RUN_ID = "31466476355"
REQUIRED_FA497_EVIDENCE_JOB_ID = "93700363537"
REQUIRED_FA497_EVIDENCE_HEAD_SHA = "f27916a15c00f57e48908d4abcdbc40a2974d2d3"
REQUIRED_FA497_SOURCE_SHA256 = "3c0d028cb84458ba243e8debde0b9067744570a81b08bfb5cf4414b9efede7c3"
REQUIRED_FA497_FIRST_ERROR_LINE = "35657"
REQUIRED_FA497_FIRST_ERROR_COL = "8"
REQUIRED_FA497_FRONTIER_DECLARATION = "selectedHeightBasePoint_continuousOn_Ioi"
REQUIRED_FA497_FRONTIER_INDEX = "2822"

TARGET_DECLARATION = REQUIRED_FA497_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2822
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA497_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = "    (by simpa only [Complex.mk_eq_add_mul_I] using ((by fun_prop : Continuous (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)).continuousOn)) ?_"
NEW_FRAGMENT = "    (by simpa only [Complex.mk_eq_add_mul_I] using (((by fun_prop : Continuous (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)).continuousOn : ContinuousOn (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (Set.Ioi 0)))) ?_"

VARIANTS = {
    "typed_continuous_on_set": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "pin the ContinuousOn domain to Set.Ioi 0 so Complex.mk_eq_add_mul_I simplification cannot leave the set metavariable unconstrained",
    ),
}

def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()

def bounds(text: str, name: str):
    xs = list(_DECL_START.finditer(text))
    hs = [i for i, m in enumerate(xs) if m.group('name') == name]
    if len(hs) != 1:
        raise RuntimeError(f"expected one {name}, found {len(hs)}")
    i = hs[0]
    return xs[i].start(), xs[i + 1].start() if i + 1 < len(xs) else len(text)

def header(region: str):
    p = region.find(':=')
    if p < 0:
        raise RuntimeError('target header has no :=')
    return region[:p + 2]

def req(k: str, v: str):
    if os.environ.get(k) != v:
        raise RuntimeError(f"FA498 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text: str):
    for k, v in [
        ('FA497_VARIANT', EXACT_FA497_VARIANT),
        ('FA497_EVIDENCE_RUN_ID', REQUIRED_FA497_EVIDENCE_RUN_ID),
        ('FA497_EVIDENCE_JOB_ID', REQUIRED_FA497_EVIDENCE_JOB_ID),
        ('FA497_EVIDENCE_HEAD_SHA', REQUIRED_FA497_EVIDENCE_HEAD_SHA),
        ('FA497_EVIDENCE_SOURCE_SHA256', REQUIRED_FA497_SOURCE_SHA256),
        ('FA497_FIRST_ERROR_LINE', REQUIRED_FA497_FIRST_ERROR_LINE),
        ('FA497_FIRST_ERROR_COL', REQUIRED_FA497_FIRST_ERROR_COL),
        ('FA497_FRONTIER_DECLARATION', REQUIRED_FA497_FRONTIER_DECLARATION),
        ('FA497_FRONTIER_INDEX', REQUIRED_FA497_FRONTIER_INDEX),
    ]:
        req(k, v)
    variant = os.environ.get('FA498_VARIANT')
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA498_VARIANT={variant!r}")
    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA498 exact FA497 source mismatch: {sha(text)}")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA498 line-count drift before patch')
    start, end = bounds(text, TARGET_DECLARATION)
    pre, reg, suf = text[:start], text[start:end], text[end:]
    h = header(reg)
    replacements, strategy = VARIANTS[variant]
    audit = []
    for old, new in replacements:
        oc, nc = reg.count(old), reg.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"FA498 target old/new counts {oc}/{nc}, expected 1/0")
        reg = reg.replace(old, new, 1)
        audit.append({
            'old_count_before': oc,
            'old_global_count_before': text.count(old),
            'new_count_before': nc,
            'new_global_count_before': text.count(new),
            'old_sha256': sha(old),
            'new_sha256': sha(new),
        })
    cand = pre + reg + suf
    if header(reg) != h:
        raise RuntimeError('FA498 header drift')
    before = [m.group('name') for m in _DECL_START.finditer(text)]
    after = [m.group('name') for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError('FA498 declaration sequence drift')
    if len(cand.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA498 candidate line count changed')
    meta = {
        'fa497_intermediate_source_sha256': sha(text),
        'candidate_source_sha256': sha(cand),
        'required_line_count': EXPECTED_LINE_COUNT,
        'candidate_line_count': len(cand.splitlines()),
        'target_header_sha256': sha(h),
        'target_header_preserved': True,
        'source_prefix_preserved': cand[:start] == pre,
        'source_suffix_preserved': cand[start + len(reg):] == suf,
        'declaration_sequence_preserved': True,
        'replacement_audit': audit,
    }
    return cand, repairs + [
        {
            'declaration': TARGET_DECLARATION,
            'declaration_index': TARGET_DECLARATION_INDEX,
            'strategy': strategy,
            'matrix_variant': variant,
            'required_fa497_evidence_run_id': int(REQUIRED_FA497_EVIDENCE_RUN_ID),
            'required_fa497_evidence_job_id': int(REQUIRED_FA497_EVIDENCE_JOB_ID),
            'required_fa497_evidence_head_sha': REQUIRED_FA497_EVIDENCE_HEAD_SHA,
            'required_fa497_source_sha256': REQUIRED_FA497_SOURCE_SHA256,
            'required_fa497_first_error_line': int(REQUIRED_FA497_FIRST_ERROR_LINE),
            'required_fa497_first_error_col': int(REQUIRED_FA497_FIRST_ERROR_COL),
            'frontier_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
            'max_errors': 32,
            **meta,
        },
        {
            'declaration': 'FA498 strict-frontier repair',
            'strategy': variant,
            'target_declaration': TARGET_DECLARATION,
            'target_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__':
    fa466.main()
