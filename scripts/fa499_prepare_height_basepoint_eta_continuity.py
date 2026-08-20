#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa498_prepare_height_basepoint_continuouson_type.py"
spec = importlib.util.spec_from_file_location("fa498base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa498 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa498
spec.loader.exec_module(fa498)

fa466 = fa498.fa466
orig_norm_repairs = fa498.norm_repairs

EXACT_FA498_VARIANT = "typed_continuous_on_set"
REQUIRED_FA498_EVIDENCE_RUN_ID = "31467555411"
REQUIRED_FA498_EVIDENCE_JOB_ID = "93703523832"
REQUIRED_FA498_EVIDENCE_HEAD_SHA = "199243051aaccaf3ab13c3e1d444b0020758c13f"
REQUIRED_FA498_SOURCE_SHA256 = "a4c29aaf4669f99dbdfe7de1c2c4f305bfb7067e8cdc1b08aa3d2a6d6ec9b627"
REQUIRED_FA498_FIRST_ERROR_LINE = "35657"
REQUIRED_FA498_FIRST_ERROR_COL = "8"
REQUIRED_FA498_FRONTIER_DECLARATION = "selectedHeightBasePoint_continuousOn_Ioi"
REQUIRED_FA498_FRONTIER_INDEX = "2822"

TARGET_DECLARATION = REQUIRED_FA498_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2822
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA498_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = "    (by simpa only [Complex.mk_eq_add_mul_I] using (((by fun_prop : Continuous (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)).continuousOn : ContinuousOn (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (Set.Ioi 0)))) ?_"
NEW_FRAGMENT = "    (by change ContinuousOn (fun y : ℝ => Complex.mk t y) (Set.Ioi 0); simpa only [Complex.mk_eq_add_mul_I] using (((by fun_prop : Continuous (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)).continuousOn : ContinuousOn (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (Set.Ioi 0)))) ?_"

VARIANTS = {
    "eta_expand_complex_mk": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "eta-expand the partially applied Complex.mk t target before applying the already smoke-verified Complex.mk_eq_add_mul_I continuity proof",
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
        raise RuntimeError(f"FA499 requires {k}={v}, got {os.environ.get(k)!r}")

def norm_repairs(text: str):
    for k, v in [
        ('FA498_VARIANT', EXACT_FA498_VARIANT),
        ('FA498_EVIDENCE_RUN_ID', REQUIRED_FA498_EVIDENCE_RUN_ID),
        ('FA498_EVIDENCE_JOB_ID', REQUIRED_FA498_EVIDENCE_JOB_ID),
        ('FA498_EVIDENCE_HEAD_SHA', REQUIRED_FA498_EVIDENCE_HEAD_SHA),
        ('FA498_EVIDENCE_SOURCE_SHA256', REQUIRED_FA498_SOURCE_SHA256),
        ('FA498_FIRST_ERROR_LINE', REQUIRED_FA498_FIRST_ERROR_LINE),
        ('FA498_FIRST_ERROR_COL', REQUIRED_FA498_FIRST_ERROR_COL),
        ('FA498_FRONTIER_DECLARATION', REQUIRED_FA498_FRONTIER_DECLARATION),
        ('FA498_FRONTIER_INDEX', REQUIRED_FA498_FRONTIER_INDEX),
    ]:
        req(k, v)
    variant = os.environ.get('FA499_VARIANT')
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA499_VARIANT={variant!r}")
    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA499 exact FA498 source mismatch: {sha(text)}")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA499 line-count drift before patch')
    start, end = bounds(text, TARGET_DECLARATION)
    pre, reg, suf = text[:start], text[start:end], text[end:]
    h = header(reg)
    replacements, strategy = VARIANTS[variant]
    audit = []
    for old, new in replacements:
        oc, nc = reg.count(old), reg.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"FA499 target old/new counts {oc}/{nc}, expected 1/0")
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
        raise RuntimeError('FA499 header drift')
    before = [m.group('name') for m in _DECL_START.finditer(text)]
    after = [m.group('name') for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError('FA499 declaration sequence drift')
    if len(cand.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError('FA499 candidate line count changed')
    meta = {
        'fa498_intermediate_source_sha256': sha(text),
        'candidate_source_sha256': sha(cand),
        'required_line_count': EXPECTED_LINE_COUNT,
        'candidate_line_count': len(cand.splitlines()),
        'target_header_sha256': sha(h),
        'target_header_preserved': True,
        'source_prefix_preserved': cand[:start] == pre,
        'source_suffix_preserved': cand[start + len(reg):] == suf,
        'declaration_sequence_preserved': True,
        'replacement_audit': audit,
        'smoke_run_id': 31468258552,
        'smoke_result': 'success',
    }
    return cand, repairs + [
        {
            'declaration': TARGET_DECLARATION,
            'declaration_index': TARGET_DECLARATION_INDEX,
            'strategy': strategy,
            'matrix_variant': variant,
            'required_fa498_evidence_run_id': int(REQUIRED_FA498_EVIDENCE_RUN_ID),
            'required_fa498_evidence_job_id': int(REQUIRED_FA498_EVIDENCE_JOB_ID),
            'required_fa498_evidence_head_sha': REQUIRED_FA498_EVIDENCE_HEAD_SHA,
            'required_fa498_source_sha256': REQUIRED_FA498_SOURCE_SHA256,
            'required_fa498_first_error_line': int(REQUIRED_FA498_FIRST_ERROR_LINE),
            'required_fa498_first_error_col': int(REQUIRED_FA498_FIRST_ERROR_COL),
            'frontier_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
            'frontier_compile_max_errors': int(os.environ.get('FA_COMPILE_MAX_ERRORS', '32')),
            **meta,
        },
        {
            'declaration': 'FA499 strict-frontier repair',
            'strategy': variant,
            'target_declaration': TARGET_DECLARATION,
            'target_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__':
    fa466.main()
