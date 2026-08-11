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

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = "  change 0 < (Complex.mk t y).im\n  simpa using hy"
NEW_FRAGMENT = "  simpa [UpperHalfPlane.ofComplex] using hy\n  -- source membership is exactly positivity of the imaginary part"


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def bounds(text: str, name: str):
    xs = list(_DECL_START.finditer(text))
    hs = [i for i, m in enumerate(xs) if m.group('name') == name]
    if len(hs) != 1:
        raise RuntimeError(f"expected one {name}, found {len(hs)}")
    i = hs[0]
    return xs[i].start(), xs[i + 1].start() if i + 1 < len(xs) else len(text)


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
    if os.environ.get('FA500_VARIANT') != 'simp_ofcomplex_source':
        raise RuntimeError(f"unsupported FA500_VARIANT={os.environ.get('FA500_VARIANT')!r}")
    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA500 exact FA499 source mismatch: {sha(text)}")
    start, end = bounds(text, TARGET_DECLARATION)
    reg = text[start:end]
    if reg.count(OLD_FRAGMENT) != 1:
        raise RuntimeError(f"FA500 target fragment count={reg.count(OLD_FRAGMENT)}, expected 1")
    new_reg = reg.replace(OLD_FRAGMENT, NEW_FRAGMENT, 1)
    cand = text[:start] + new_reg + text[end:]
    before = [m.group('name') for m in _DECL_START.finditer(text)]
    after = [m.group('name') for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError('FA500 declaration sequence drift')
    return cand, repairs + [
        {
            'declaration': TARGET_DECLARATION,
            'declaration_index': TARGET_DECLARATION_INDEX,
            'strategy': 'discharge UpperHalfPlane.ofComplex.source membership by simp unfolding ofComplex and range_coe from the positive-height hypothesis',
            'matrix_variant': 'simp_ofcomplex_source',
            'required_fa499_evidence_run_id': int(REQUIRED_FA499_EVIDENCE_RUN_ID),
            'required_fa499_evidence_job_id': int(REQUIRED_FA499_EVIDENCE_JOB_ID),
            'required_fa499_evidence_head_sha': REQUIRED_FA499_EVIDENCE_HEAD_SHA,
            'required_fa499_source_sha256': REQUIRED_FA499_SOURCE_SHA256,
            'required_fa499_first_error_line': int(REQUIRED_FA499_FIRST_ERROR_LINE),
            'required_fa499_first_error_col': int(REQUIRED_FA499_FIRST_ERROR_COL),
            'candidate_source_sha256': sha(cand),
            'candidate_line_count': len(cand.splitlines()),
            'declaration_sequence_preserved': True,
            'claims_preserved': True,
            'later_repair_count': 0,
        },
        {
            'declaration': 'FA500 strict-frontier repair',
            'strategy': 'simp_ofcomplex_source',
            'target_declaration': TARGET_DECLARATION,
            'target_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__':
    fa466.main()
