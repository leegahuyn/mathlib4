#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa496_prepare_graph_integral_shape.py"
spec = importlib.util.spec_from_file_location("fa496base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa496 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa496
spec.loader.exec_module(fa496)

fa466 = fa496.fa466
orig_norm_repairs = fa496.norm_repairs

EXACT_FA496_VARIANT = "named_pointwise_integrands"
REQUIRED_FA496_EVIDENCE_RUN_ID = "31465439549"
REQUIRED_FA496_EVIDENCE_JOB_ID = "93697278510"
REQUIRED_FA496_EVIDENCE_HEAD_SHA = "50758d199b5db689e08d78057cc40281cceb9262"
REQUIRED_FA496_SOURCE_SHA256 = "8556a6ccc3eef48d13e359ab3e29488dfa36442ed90e0fbc6509c8772b16b12d"
REQUIRED_FA496_FIRST_ERROR_LINE = "35657"
REQUIRED_FA496_FIRST_ERROR_COL = "8"
REQUIRED_FA496_FRONTIER_DECLARATION = "selectedHeightBasePoint_continuousOn_Ioi"
REQUIRED_FA496_FRONTIER_INDEX = "2822"

TARGET_DECLARATION = REQUIRED_FA496_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2822
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA496_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = "    (by fun_prop) ?_"
NEW_FRAGMENT = "    (by simpa only [Complex.mk_eq_add_mul_I] using ((by fun_prop : Continuous (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)).continuousOn)) ?_"

VARIANTS = {
    "mk_eq_add_mul_i_continuous_on": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "replace the failing Complex.mk ContinuousOn fun_prop search with the already verified Complex.mk_eq_add_mul_I normal form, prove the elementary Complex-valued map globally continuous, then restrict via continuousOn",
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
        raise RuntimeError(f"FA497 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text: str):
    for k, v in [
        ('FA496_VARIANT', EXACT_FA496_VARIANT),
        ('FA496_EVIDENCE_RUN_ID', REQUIRED_FA496_EVIDENCE_RUN_ID),
        ('FA496_EVIDENCE_JOB_ID', REQUIRED_FA496_EVIDENCE_JOB_ID),
        ('FA496_EVIDENCE_HEAD_SHA', REQUIRED_FA496_EVIDENCE_HEAD_SHA),
        ('FA496_EVIDENCE_SOURCE_SHA256', REQUIRED_FA496_SOURCE_SHA256),
        ('FA496_FIRST_ERROR_LINE', REQUIRED_FA496_FIRST_ERROR_LINE),
        ('FA496_FIRST_ERROR_COL', REQUIRED_FA496_FIRST_ERROR_COL),
        ('FA496_FRONTIER_DECLARATION', REQUIRED_FA496_FRONTIER_DECLARATION),
        ('FA496_FRONTIER_INDEX', REQUIRED_FA496_FRONTIER_INDEX),
    ]:
        req(k, v)
    variant = os.environ.get('FA497_VARIANT')
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA497_VARIANT={variant!r}")
    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA497 exact FA496 source mismatch: {sha(text)}")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA497 line-count drift before patch')
    start, end = bounds(text, TARGET_DECLARATION)
    pre, reg, suf = text[:start], text[start:end], text[end:]
    h = header(reg)
    replacements, strategy = VARIANTS[variant]
    audit = []
    for old, new in replacements:
        oc, nc = reg.count(old), reg.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"FA497 target old/new counts {oc}/{nc}, expected 1/0")
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
        raise RuntimeError('FA497 header drift')
    before = [m.group('name') for m in _DECL_START.finditer(text)]
    after = [m.group('name') for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError('FA497 declaration sequence drift')
    if len(cand.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA497 candidate line count changed')
    meta = {
        'fa496_intermediate_source_sha256': sha(text),
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
            'required_fa496_evidence_run_id': int(REQUIRED_FA496_EVIDENCE_RUN_ID),
            'required_fa496_evidence_job_id': int(REQUIRED_FA496_EVIDENCE_JOB_ID),
            'required_fa496_evidence_head_sha': REQUIRED_FA496_EVIDENCE_HEAD_SHA,
            'required_fa496_source_sha256': REQUIRED_FA496_SOURCE_SHA256,
            'required_fa496_first_error_line': int(REQUIRED_FA496_FIRST_ERROR_LINE),
            'required_fa496_first_error_col': int(REQUIRED_FA496_FIRST_ERROR_COL),
            'frontier_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
            'max_errors': 32,
            **meta,
        },
        {
            'declaration': 'FA497 strict-frontier repair',
            'strategy': variant,
            'target_declaration': TARGET_DECLARATION,
            'target_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__':
    fa466.main()
