#!/usr/bin/env python3
from __future__ import annotations
import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa492_prepare_endpoint_explicit_continuity.py"
spec = importlib.util.spec_from_file_location("fa492base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa492 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa492
spec.loader.exec_module(fa492)
fa466 = fa492.fa466
orig_norm_repairs = fa492.norm_repairs

EXACT_FA492_VARIANT = "reuse_hh_endpoint"
REQUIRED_RUN = "31459011892"
REQUIRED_JOB = "93678608893"
REQUIRED_HEAD = "2c7cbbc2ba102674d34e713d18098ed9e7ba30d1"
REQUIRED_SOURCE = "91a277662a1cee06b849445865d8a85331a1cef250c150d5c3f5e4c1b66fe7f7"
REQUIRED_LINE = "35507"
REQUIRED_COL = "44"
TARGET_DECLARATION = "norm_selectedCuspCoreTrace_sq_le_logHeightEnergy"
TARGET_INDEX = 2812
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD = "      unfold selectedLogHeightNaturalGauge; simpa only [h] using ((continuous_const.mul (hh.continuous.comp hpoint)).norm.pow 2)"
NEW = "      unfold selectedLogHeightNaturalGauge; have hconst : Continuous (fun _ : ℝ => (((Real.exp (Real.log (gammaTwoCuspLevel Y) / 2) : ℝ) : ℂ))) := continuous_const; have hcomp' : Continuous (fun t : ℝ => h (logHeightBasePoint t (Real.log (gammaTwoCuspLevel Y)))) := hh.continuous.comp hpoint; have hprod : Continuous (fun t : ℝ => (((Real.exp (Real.log (gammaTwoCuspLevel Y) / 2) : ℝ) : ℂ) * h (logHeightBasePoint t (Real.log (gammaTwoCuspLevel Y))))) := hconst.mul hcomp'; simpa only [h] using hprod.norm.pow 2"

def sha(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()

def bounds(text: str) -> tuple[int, int]:
    starts = list(_DECL_START.finditer(text))
    hits = [i for i, m in enumerate(starts) if m.group("name") == TARGET_DECLARATION]
    if len(hits) != 1:
        raise RuntimeError(f"expected one {TARGET_DECLARATION}, found {len(hits)}")
    i = hits[0]
    return starts[i].start(), starts[i + 1].start() if i + 1 < len(starts) else len(text)

def header(region: str) -> str:
    p = region.find(":=")
    if p < 0:
        raise RuntimeError("target header has no :=")
    return region[:p + 2]

def req(name: str, expected: str):
    actual = os.environ.get(name)
    if actual != expected:
        raise RuntimeError(f"FA492-r3 requires {name}={expected}, got {actual!r}")

def norm_repairs(text: str):
    for name, expected in [
        ("FA492_VARIANT", EXACT_FA492_VARIANT),
        ("FA492_EVIDENCE_RUN_ID", REQUIRED_RUN),
        ("FA492_EVIDENCE_JOB_ID", REQUIRED_JOB),
        ("FA492_EVIDENCE_HEAD_SHA", REQUIRED_HEAD),
        ("FA492_EVIDENCE_SOURCE_SHA256", REQUIRED_SOURCE),
        ("FA492_FIRST_ERROR_LINE", REQUIRED_LINE),
        ("FA492_FIRST_ERROR_COL", REQUIRED_COL),
        ("FA492_FRONTIER_DECLARATION", TARGET_DECLARATION),
        ("FA492_FRONTIER_INDEX", str(TARGET_INDEX)),
    ]:
        req(name, expected)
    text, repairs = orig_norm_repairs(text)
    if sha(text) != REQUIRED_SOURCE:
        raise RuntimeError(f"FA492-r3 requires exact FA492 source {REQUIRED_SOURCE}, got {sha(text)}")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA492-r3 intermediate line-count drift")
    start, end = bounds(text)
    prefix, region, suffix = text[:start], text[start:end], text[end:]
    old_header = header(region)
    if region.count(OLD) != 1 or region.count(NEW) != 0:
        raise RuntimeError(f"FA492-r3 target old/new counts {region.count(OLD)}/{region.count(NEW)}")
    region = region.replace(OLD, NEW, 1)
    candidate = prefix + region + suffix
    if header(region) != old_header or len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA492-r3 invariant drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA492-r3 declaration sequence drift")
    audit = {
        "fa492_intermediate_source_sha256": REQUIRED_SOURCE,
        "candidate_source_sha256": sha(candidate),
        "required_line_count": EXPECTED_LINE_COUNT,
        "candidate_line_count": len(candidate.splitlines()),
        "replacement_count": 1,
        "target_header_sha256": sha(old_header),
        "target_header_preserved": True,
        "source_prefix_preserved": candidate[:start] == prefix,
        "source_suffix_preserved": candidate[start + len(region):] == suffix,
        "declaration_sequence_sha256": sha("\n".join(before)),
        "declaration_sequence_preserved": True,
    }
    return candidate, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_INDEX,
            "strategy": "pin the constant factor, composed pullback, and product as explicitly typed lambda-valued Continuous proofs before taking norm-square",
            "matrix_variant": "explicit_hconst_hcomp_hprod",
            "required_fa492_evidence_run_id": int(REQUIRED_RUN),
            "required_fa492_evidence_job_id": int(REQUIRED_JOB),
            "required_fa492_evidence_head_sha": REQUIRED_HEAD,
            "required_fa492_source_sha256": REQUIRED_SOURCE,
            "required_fa492_first_error_line": int(REQUIRED_LINE),
            "required_fa492_first_error_col": int(REQUIRED_COL),
            "frontier_declaration_index": TARGET_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA492-r3 strict-frontier repair",
            "strategy": "explicit_hconst_hcomp_hprod",
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_INDEX,
            "later_repair_count": 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == "__main__":
    fa466.main()
