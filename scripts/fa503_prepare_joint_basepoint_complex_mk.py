#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa502_prepare_exp_density_pi_zero_apply.py"
spec = importlib.util.spec_from_file_location("fa502base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa502 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa502
spec.loader.exec_module(fa502)

fa466 = fa502.fa466
orig_norm_repairs = fa502.norm_repairs

EXACT_FA502_VARIANT = "pi_zero_apply"
REQUIRED_FA502_EVIDENCE_RUN_ID = "31472717984"
REQUIRED_FA502_EVIDENCE_JOB_ID = "93719392970"
REQUIRED_FA502_EVIDENCE_HEAD_SHA = "1bcbb825fa91498278381a0ffc2946cdcbce1f01"
REQUIRED_FA502_SOURCE_SHA256 = "db38b9ffb4820e5f7b91816173d635461cd559ff74a36cc69f4c2e5e3034faf3"
REQUIRED_FA502_FIRST_ERROR_LINE = "35912"
REQUIRED_FA502_FIRST_ERROR_COL = "8"
REQUIRED_FA502_FRONTIER_DECLARATION = "selectedHeightBasePoint_joint_continuousOn_positive"
REQUIRED_FA502_FRONTIER_INDEX = "2831"

TARGET_DECLARATION = REQUIRED_FA502_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2831
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA502_SOURCE_SHA256

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = """  refine UpperHalfPlane.ofComplex.continuousOn.comp
    (by fun_prop) ?_
"""
NEW_FRAGMENT = """  refine UpperHalfPlane.ofComplex.continuousOn.comp
    (by
      simpa only [Complex.mk_eq_add_mul_I] using
        ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
          (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).continuousOn)) ?_
"""


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
        raise RuntimeError(f"FA503 requires {k}={v}, got {os.environ.get(k)!r}")


def norm_repairs(text: str):
    for k, v in [
        ("FA502_VARIANT", EXACT_FA502_VARIANT),
        ("FA502_EVIDENCE_RUN_ID", REQUIRED_FA502_EVIDENCE_RUN_ID),
        ("FA502_EVIDENCE_JOB_ID", REQUIRED_FA502_EVIDENCE_JOB_ID),
        ("FA502_EVIDENCE_HEAD_SHA", REQUIRED_FA502_EVIDENCE_HEAD_SHA),
        ("FA502_EVIDENCE_SOURCE_SHA256", REQUIRED_FA502_SOURCE_SHA256),
        ("FA502_FIRST_ERROR_LINE", REQUIRED_FA502_FIRST_ERROR_LINE),
        ("FA502_FIRST_ERROR_COL", REQUIRED_FA502_FIRST_ERROR_COL),
        ("FA502_FRONTIER_DECLARATION", REQUIRED_FA502_FRONTIER_DECLARATION),
        ("FA502_FRONTIER_INDEX", REQUIRED_FA502_FRONTIER_INDEX),
    ]:
        req(k, v)
    if os.environ.get("FA503_VARIANT") != "joint_mk_eq_add_mul_i":
        raise RuntimeError(f"unsupported FA503_VARIANT={os.environ.get('FA503_VARIANT')!r}")

    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA503 exact FA502 source mismatch: {sha(text)}")

    start, end = bounds(text, TARGET_DECLARATION)
    pre, reg, suf = text[:start], text[start:end], text[end:]
    h = header(reg)
    if reg.count(OLD_FRAGMENT) != 1:
        raise RuntimeError(f"FA503 target fragment count={reg.count(OLD_FRAGMENT)}, expected 1")
    new_reg = reg.replace(OLD_FRAGMENT, NEW_FRAGMENT, 1)
    cand = pre + new_reg + suf

    if header(new_reg) != h:
        raise RuntimeError("FA503 theorem header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError("FA503 declaration sequence drift")

    return cand, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": "normalize the joint Complex.mk map with Complex.mk_eq_add_mul_I and prove the resulting pair-projection complex map globally Continuous before restricting to ContinuousOn",
            "matrix_variant": "joint_mk_eq_add_mul_i",
            "required_fa502_evidence_run_id": int(REQUIRED_FA502_EVIDENCE_RUN_ID),
            "required_fa502_evidence_job_id": int(REQUIRED_FA502_EVIDENCE_JOB_ID),
            "required_fa502_evidence_head_sha": REQUIRED_FA502_EVIDENCE_HEAD_SHA,
            "required_fa502_source_sha256": REQUIRED_FA502_SOURCE_SHA256,
            "required_fa502_first_error_line": int(REQUIRED_FA502_FIRST_ERROR_LINE),
            "required_fa502_first_error_col": int(REQUIRED_FA502_FIRST_ERROR_COL),
            "candidate_source_sha256": sha(cand),
            "candidate_line_count": len(cand.splitlines()),
            "target_header_preserved": True,
            "declaration_sequence_preserved": True,
            "claims_preserved": True,
            "later_repair_count": 0,
        },
        {
            "declaration": "FA503 strict-frontier repair",
            "strategy": "joint_mk_eq_add_mul_i",
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == "__main__":
    fa466.main()
