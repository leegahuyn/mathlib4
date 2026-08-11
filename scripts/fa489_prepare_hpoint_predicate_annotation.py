#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa488_prepare_hpoint_explicit_complex.py"
spec = importlib.util.spec_from_file_location("fa488base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa488 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa488
spec.loader.exec_module(fa488)

fa466 = fa488.fa466
orig_norm_repairs = fa488.norm_repairs

REQUIRED_VARIANT = "explicit_complex_subtype_continuity"
REQUIRED_RUN = "31455142823"
REQUIRED_JOB = "93667256223"
REQUIRED_HEAD = "7b41dc35cd137fe8827331e7a514b50e85546ce7"
REQUIRED_SOURCE = "701d7a7218cb73aeded5090f813487d07f384f38a08b67a0a9518f1dd54ef89a"
REQUIRED_LINE = "35311"
REQUIRED_COL = "59"
TARGET = "selectedLogHeightEnergyDensity_continuous"
TARGET_INDEX = 2806
EXPECTED_LINES = 60535

_DECL = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD = "    refine Continuous.subtype_mk ?_ (fun p => Real.exp_pos p.2)"
NEW = "    refine Continuous.subtype_mk ?_ (fun p : ℝ × ℝ => Real.exp_pos p.2)"


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def bounds(text: str):
    ms = list(_DECL.finditer(text)); hits = [i for i,m in enumerate(ms) if m.group('name') == TARGET]
    if len(hits) != 1: raise RuntimeError(f"expected one {TARGET}, found {len(hits)}")
    i = hits[0]; return ms[i].start(), ms[i+1].start() if i+1 < len(ms) else len(text)


def req(k: str, v: str):
    if os.environ.get(k) != v: raise RuntimeError(f"FA489 requires {k}={v}, got {os.environ.get(k)!r}")


def norm_repairs(text: str):
    req("FA488_VARIANT", REQUIRED_VARIANT); req("FA488_EVIDENCE_RUN_ID", REQUIRED_RUN)
    req("FA488_EVIDENCE_JOB_ID", REQUIRED_JOB); req("FA488_EVIDENCE_HEAD_SHA", REQUIRED_HEAD)
    req("FA488_EVIDENCE_SOURCE_SHA256", REQUIRED_SOURCE); req("FA488_FIRST_ERROR_LINE", REQUIRED_LINE)
    req("FA488_FIRST_ERROR_COL", REQUIRED_COL); req("FA488_FRONTIER_DECLARATION", TARGET)
    req("FA488_FRONTIER_INDEX", str(TARGET_INDEX)); req("FA489_VARIANT", "annotate_predicate_lambda")

    text, repairs = orig_norm_repairs(text)
    if sha(text) != REQUIRED_SOURCE: raise RuntimeError(f"FA489 upstream source mismatch: {sha(text)}")
    if len(text.splitlines()) != EXPECTED_LINES: raise RuntimeError("FA489 upstream line-count drift")
    start,end = bounds(text); region = text[start:end]
    if region.count(OLD) != 1 or region.count(NEW) != 0: raise RuntimeError("FA489 target occurrence mismatch")
    candidate = text[:start] + region.replace(OLD, NEW, 1) + text[end:]
    if len(candidate.splitlines()) != EXPECTED_LINES: raise RuntimeError("FA489 line-count changed")
    before=[m.group('name') for m in _DECL.finditer(text)]; after=[m.group('name') for m in _DECL.finditer(candidate)]
    if before != after: raise RuntimeError("FA489 declaration sequence drift")
    return candidate, repairs + [
        {"declaration": TARGET, "declaration_index": TARGET_INDEX,
         "strategy": "annotate Continuous.subtype_mk predicate lambda with p : ℝ × ℝ",
         "matrix_variant": "annotate_predicate_lambda",
         "required_fa488_evidence_run_id": int(REQUIRED_RUN), "required_fa488_evidence_job_id": int(REQUIRED_JOB),
         "required_fa488_evidence_head_sha": REQUIRED_HEAD, "required_fa488_source_sha256": REQUIRED_SOURCE,
         "required_fa488_first_error_line": int(REQUIRED_LINE), "required_fa488_first_error_col": int(REQUIRED_COL),
         "candidate_source_sha256": sha(candidate), "candidate_line_count": len(candidate.splitlines()),
         "declaration_sequence_preserved": True, "later_repair_count": 0, "max_errors": 32},
        {"declaration": "FA489 strict-frontier repair", "strategy": "annotate_predicate_lambda",
         "target_declaration": TARGET, "target_declaration_index": TARGET_INDEX, "later_repair_count": 0}
    ]

fa466.norm_repairs = norm_repairs
if __name__ == "__main__": fa466.main()
