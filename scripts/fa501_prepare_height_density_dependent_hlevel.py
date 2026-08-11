#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa500_prepare_ofcomplex_source_membership.py"
spec = importlib.util.spec_from_file_location("fa500base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa500 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa500
spec.loader.exec_module(fa500)

fa466 = fa500.fa466
orig_norm_repairs = fa500.norm_repairs

EXACT_FA500_VARIANT = "explicit_range_witness"
REQUIRED_FA500_EVIDENCE_RUN_ID = "31470489635"
REQUIRED_FA500_EVIDENCE_JOB_ID = "93712581127"
REQUIRED_FA500_EVIDENCE_HEAD_SHA = "bbda106c0fafed1dcc64ed4dc7ce84728fac12b5"
REQUIRED_FA500_SOURCE_SHA256 = "1227fa2790152efa58c5f4e4acc14bde93a29259c5951c890eab80db6eedcc95"
REQUIRED_FA500_FIRST_ERROR_LINE = "35735"
REQUIRED_FA500_FIRST_ERROR_COL = "8"
REQUIRED_FA500_FRONTIER_DECLARATION = "selectedHeightGraphDensity_uniform_eventually_zero"
REQUIRED_FA500_FRONTIER_INDEX = "2825"

TARGET_DECLARATION = REQUIRED_FA500_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2825
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA500_SOURCE_SHA256

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = "    rw [hlevel]"
NEW_FRAGMENT = "    simp only [hlevel]"


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
        raise RuntimeError(f"FA501 requires {k}={v}, got {os.environ.get(k)!r}")


def norm_repairs(text: str):
    for k, v in [
        ('FA500_VARIANT', EXACT_FA500_VARIANT),
        ('FA500_EVIDENCE_RUN_ID', REQUIRED_FA500_EVIDENCE_RUN_ID),
        ('FA500_EVIDENCE_JOB_ID', REQUIRED_FA500_EVIDENCE_JOB_ID),
        ('FA500_EVIDENCE_HEAD_SHA', REQUIRED_FA500_EVIDENCE_HEAD_SHA),
        ('FA500_EVIDENCE_SOURCE_SHA256', REQUIRED_FA500_SOURCE_SHA256),
        ('FA500_FIRST_ERROR_LINE', REQUIRED_FA500_FIRST_ERROR_LINE),
        ('FA500_FIRST_ERROR_COL', REQUIRED_FA500_FIRST_ERROR_COL),
        ('FA500_FRONTIER_DECLARATION', REQUIRED_FA500_FRONTIER_DECLARATION),
        ('FA500_FRONTIER_INDEX', REQUIRED_FA500_FRONTIER_INDEX),
    ]:
        req(k, v)
    if os.environ.get('FA501_VARIANT') != 'simp_only_hlevel':
        raise RuntimeError(f"unsupported FA501_VARIANT={os.environ.get('FA501_VARIANT')!r}")

    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA501 exact FA500 source mismatch: {sha(text)}")

    start, end = bounds(text, TARGET_DECLARATION)
    reg = text[start:end]
    if reg.count(OLD_FRAGMENT) != 1:
        raise RuntimeError(f"FA501 target fragment count={reg.count(OLD_FRAGMENT)}, expected 1")
    new_reg = reg.replace(OLD_FRAGMENT, NEW_FRAGMENT, 1)
    cand = text[:start] + new_reg + text[end:]

    before = [m.group('name') for m in _DECL_START.finditer(text)]
    after = [m.group('name') for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError('FA501 declaration sequence drift')

    return cand, repairs + [
        {
            'declaration': TARGET_DECLARATION,
            'declaration_index': TARGET_DECLARATION_INDEX,
            'strategy': 'replace dependent rw [hlevel] with simp-only rewriting so proof-valued UpperHalfPlane fields are transported by simplifier congruence',
            'matrix_variant': 'simp_only_hlevel',
            'required_fa500_evidence_run_id': int(REQUIRED_FA500_EVIDENCE_RUN_ID),
            'required_fa500_evidence_job_id': int(REQUIRED_FA500_EVIDENCE_JOB_ID),
            'required_fa500_evidence_head_sha': REQUIRED_FA500_EVIDENCE_HEAD_SHA,
            'required_fa500_source_sha256': REQUIRED_FA500_SOURCE_SHA256,
            'required_fa500_first_error_line': int(REQUIRED_FA500_FIRST_ERROR_LINE),
            'required_fa500_first_error_col': int(REQUIRED_FA500_FIRST_ERROR_COL),
            'candidate_source_sha256': sha(cand),
            'candidate_line_count': len(cand.splitlines()),
            'declaration_sequence_preserved': True,
            'claims_preserved': True,
            'later_repair_count': 0,
        },
        {
            'declaration': 'FA501 strict-frontier repair',
            'strategy': 'simp_only_hlevel',
            'target_declaration': TARGET_DECLARATION,
            'target_declaration_index': TARGET_DECLARATION_INDEX,
            'later_repair_count': 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == '__main__':
    fa466.main()
