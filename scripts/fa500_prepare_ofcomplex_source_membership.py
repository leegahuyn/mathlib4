#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa499_prepare_height_basepoint_eta_continuity.py"
spec = importlib.util.spec_from_file_location("fa499base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa499 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa499
spec.loader.exec_module(fa499)

fa466 = fa499.fa466
orig_norm_repairs = fa499.norm_repairs

EXACT_FA499_VARIANT = "eta_expand_complex_mk"
REQUIRED_FA499_EVIDENCE_RUN_ID = "31468842155"
REQUIRED_FA499_EVIDENCE_JOB_ID = "93707506552"
REQUIRED_FA499_EVIDENCE_HEAD_SHA = "2b579f10eac257ba7daa7733674f972a08f88d29"
REQUIRED_FA499_SOURCE_SHA256 = "fa2567ec0c2dec43cec56fe0c3df0894c38a61f6f7a65023da7b4efcd941abb1"
REQUIRED_FA499_FIRST_ERROR_LINE = "35659"
REQUIRED_FA499_FIRST_ERROR_COL = "2"
REQUIRED_FA499_FRONTIER_DECLARATION = "selectedHeightBasePoint_continuousOn_Ioi"
REQUIRED_FA499_FRONTIER_INDEX = "2822"

TARGET_DECLARATION = REQUIRED_FA499_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2822
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA499_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = """  intro y hy
  change 0 < (Complex.mk t y).im
  simpa using hy"""
NEW_FRAGMENT = """  intro y hy
  have hy' : 0 < y := by simpa using hy
  simpa [UpperHalfPlane.ofComplex] using hy'"""

VARIANTS = {
    "explicit_range_witness": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "simplify ofComplex.source membership to positive imaginary part and close it with the Ioi hypothesis",
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
        raise RuntimeError(f"FA500 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text: str):
    for k, v in [
        ('FA499_VARIANT', EXACT_FA499_VARIANT),
        ('FA499_EVIDENCE_RUN_ID', REQUIRED_FA499_EVIDENCE_RUN_ID),
        ('FA499_EVIDENCE_JOB_ID', REQUIRED_FA499_EVIDENCE_JOB_ID),
        ('FA499_EVIDENCE_HEAD_SHA', REQUIRED_FA499_EVIDENCE_HEAD_SHA),
        ('FA499_EVIDENCE_SOURCE_SHA256', REQUIRED_FA499_SOURCE_SHA256),
        ('FA499_FIRST_ERROR_LINE', REQUIRED_FA499_FIRST_ERROR_LINE),
        ('FA499_FIRST_ERROR_COL', REQUIRED_FA499_FIRST_ERROR_COL),
        ('FA499_FRONTIER_DECLARATION', REQUIRED_FA499_FRONTIER_DECLARATION),
        ('FA499_FRONTIER_INDEX', REQUIRED_FA499_FRONTIER_INDEX),
    ]:
        req(k, v)
    variant = os.environ.get('FA500_VARIANT')
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA500_VARIANT={variant!r}")
    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA500 exact FA499 source mismatch: {sha(text)}")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA500 line-count drift before patch')
    start, end = bounds(text, TARGET_DECLARATION)
    pre, reg, suf = text[:start], text[start:end], text[end:]
    h = header(reg)
    replacements, strategy = VARIANTS[variant]
    audit = []
    for old, new in replacements:
        oc, nc = reg.count(old), reg.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"FA500 target old/new counts {oc}/{nc}, expected 1/0")
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
        raise RuntimeError('FA500 header drift')
    before = [m.group('name') for m in _DECL_START.finditer(text)]
    after = [m.group('name') for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError('FA500 declaration sequence drift')
    if len(cand.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA500 candidate line count changed')
    meta = {
        'fa499_intermediate_source_sha256': sha(text),
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
            'required_fa499_evidence_run_id': int(REQUIRED_FA499_EVIDENCE_RUN_ID),
            'required_fa499_evidence_job_id': int(REQUIRED_FA499_EVIDENCE_JOB_ID),
            'required_fa499_evidence_head_sha': REQUIRED_FA499_EVIDENCE_HEAD_SHA,
            'required_fa499_source_sha256': REQUIRED_FA499_SOURCE_SHA256,
            'required_fa499_first_error_line': int(REQUIRED_FA499_FIRST_ERROR_LINE),
            'required_fa499_first_error_col': int(REQUIRED_FA499_FIRST_ERROR_COL),
            'frontier_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
            'frontier_compile_max_errors': int(os.environ.get('FA_COMPILE_MAX_ERRORS', '1')),
            **meta,
        },
        {
            'declaration': 'FA500 strict-frontier repair',
            'strategy': variant,
            'target_declaration': TARGET_DECLARATION,
            'target_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__':
    fa466.main()
