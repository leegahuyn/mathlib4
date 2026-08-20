#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa503_prepare_joint_basepoint_complex_mk.py"
spec = importlib.util.spec_from_file_location("fa503base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa503 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa503
spec.loader.exec_module(fa503)

fa466 = fa503.fa466
orig_norm_repairs = fa503.norm_repairs

EXACT_FA503_VARIANT = "joint_mk_eq_add_mul_i"
REQUIRED_FA503_EVIDENCE_RUN_ID = "31475061266"
REQUIRED_FA503_EVIDENCE_JOB_ID = "93726750556"
REQUIRED_FA503_EVIDENCE_HEAD_SHA = "60d9820e64ab5ef3f14abc7cfbd0c1f2b1d4a522"
REQUIRED_FA503_SOURCE_SHA256 = "46d208e7893993190355c092623882dd3df8c4e36b9df3d21a0b28db1a583a2f"
REQUIRED_FA503_FIRST_ERROR_LINE = "35917"
REQUIRED_FA503_FIRST_ERROR_COL = "2"
REQUIRED_FA503_FRONTIER_DECLARATION = "selectedHeightBasePoint_joint_continuousOn_positive"
REQUIRED_FA503_FRONTIER_INDEX = "2831"

TARGET_DECLARATION = REQUIRED_FA503_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2831
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA503_SOURCE_SHA256

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = """  intro p hp
  change 0 < (Complex.mk p.1 p.2).im
  simpa using hp.2"""
NEW_FRAGMENT = """  intro p hp
  have hp' : 0 < p.2 := by simpa using hp.2
  simpa [UpperHalfPlane.ofComplex] using hp'"""


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def bounds(text: str, name: str):
    xs = list(_DECL_START.finditer(text))
    hs = [i for i, m in enumerate(xs) if m.group("name") == name]
    if len(hs) != 1:
        raise RuntimeError(f"expected one {name}, found {len(hs)}")
    i = hs[0]
    return xs[i].start(), xs[i + 1].start() if i + 1 < len(xs) else len(text)


def header(region: str) -> str:
    p = region.find(":=")
    if p < 0:
        raise RuntimeError("target header has no :=")
    return region[:p + 2]


def req(k: str, v: str):
    if os.environ.get(k) != v:
        raise RuntimeError(f"FA504 requires {k}={v}, got {os.environ.get(k)!r}")


def norm_repairs(text: str):
    for k, v in [
        ("FA503_VARIANT", EXACT_FA503_VARIANT),
        ("FA503_EVIDENCE_RUN_ID", REQUIRED_FA503_EVIDENCE_RUN_ID),
        ("FA503_EVIDENCE_JOB_ID", REQUIRED_FA503_EVIDENCE_JOB_ID),
        ("FA503_EVIDENCE_HEAD_SHA", REQUIRED_FA503_EVIDENCE_HEAD_SHA),
        ("FA503_EVIDENCE_SOURCE_SHA256", REQUIRED_FA503_SOURCE_SHA256),
        ("FA503_FIRST_ERROR_LINE", REQUIRED_FA503_FIRST_ERROR_LINE),
        ("FA503_FIRST_ERROR_COL", REQUIRED_FA503_FIRST_ERROR_COL),
        ("FA503_FRONTIER_DECLARATION", REQUIRED_FA503_FRONTIER_DECLARATION),
        ("FA503_FRONTIER_INDEX", REQUIRED_FA503_FRONTIER_INDEX),
    ]:
        req(k, v)
    if os.environ.get("FA504_VARIANT") != "explicit_range_witness":
        raise RuntimeError(f"unsupported FA504_VARIANT={os.environ.get('FA504_VARIANT')!r}")

    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA504 exact FA503 source mismatch: {sha(text)}")

    start, end = bounds(text, TARGET_DECLARATION)
    pre, reg, suf = text[:start], text[start:end], text[end:]
    h = header(reg)
    if reg.count(OLD_FRAGMENT) != 1:
        raise RuntimeError(f"FA504 target fragment count={reg.count(OLD_FRAGMENT)}, expected 1")
    new_reg = reg.replace(OLD_FRAGMENT, NEW_FRAGMENT, 1)
    cand = pre + new_reg + suf

    if header(new_reg) != h:
        raise RuntimeError("FA504 theorem header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError("FA504 declaration sequence drift")

    return cand, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": "reuse the verified ofComplex explicit range witness: extract positivity of p.2 from the product-set hypothesis and simplify UpperHalfPlane.ofComplex.source membership",
            "matrix_variant": "explicit_range_witness",
            "required_fa503_evidence_run_id": int(REQUIRED_FA503_EVIDENCE_RUN_ID),
            "required_fa503_evidence_job_id": int(REQUIRED_FA503_EVIDENCE_JOB_ID),
            "required_fa503_evidence_head_sha": REQUIRED_FA503_EVIDENCE_HEAD_SHA,
            "required_fa503_source_sha256": REQUIRED_FA503_SOURCE_SHA256,
            "required_fa503_first_error_line": int(REQUIRED_FA503_FIRST_ERROR_LINE),
            "required_fa503_first_error_col": int(REQUIRED_FA503_FIRST_ERROR_COL),
            "candidate_source_sha256": sha(cand),
            "candidate_line_count": len(cand.splitlines()),
            "target_header_preserved": True,
            "declaration_sequence_preserved": True,
            "claims_preserved": True,
            "later_repair_count": 0,
        },
        {
            "declaration": "FA504 strict-frontier repair",
            "strategy": "explicit_range_witness",
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == "__main__":
    fa466.main()
