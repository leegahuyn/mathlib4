#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, os, re, sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa501_prepare_height_density_dependent_hlevel.py"
spec = importlib.util.spec_from_file_location("fa501base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa501 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa501
spec.loader.exec_module(fa501)

fa466 = fa501.fa466
orig_norm_repairs = fa501.norm_repairs

EXACT_FA501_VARIANT = "simp_only_hlevel"
REQUIRED_FA501_EVIDENCE_RUN_ID = "31471647828"
REQUIRED_FA501_EVIDENCE_JOB_ID = "93716072700"
REQUIRED_FA501_EVIDENCE_HEAD_SHA = "7a5baf0922ecde4b97c77974ceb80e48bf88e094"
REQUIRED_FA501_SOURCE_SHA256 = "926ee8186e0a41fda6135a83268c27db9605236674d023b07ab63ae1366a8e7c"
REQUIRED_FA501_FIRST_ERROR_LINE = "35814"
REQUIRED_FA501_FIRST_ERROR_COL = "32"
REQUIRED_FA501_FRONTIER_DECLARATION = "exp_mul_selectedHeightGraphDensity_integrableOn_Ici_log"
REQUIRED_FA501_FRONTIER_INDEX = "2828"

TARGET_DECLARATION = REQUIRED_FA501_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2828
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA501_SOURCE_SHA256

_DECL_START = re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD_FRAGMENT = "  simp only [g, hZero t ht (Real.exp r) hr, zero_mul]"
NEW_FRAGMENT = "  simp only [g, hZero t ht (Real.exp r) hr, zero_mul, Pi.zero_apply]"


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def bounds(text: str, name: str):
    xs = list(_DECL_START.finditer(text))
    hs = [i for i, m in enumerate(xs) if m.group('name') == name]
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
        raise RuntimeError(f"FA502 requires {k}={v}, got {os.environ.get(k)!r}")


def norm_repairs(text: str):
    for k, v in [
        ("FA501_VARIANT", EXACT_FA501_VARIANT),
        ("FA501_EVIDENCE_RUN_ID", REQUIRED_FA501_EVIDENCE_RUN_ID),
        ("FA501_EVIDENCE_JOB_ID", REQUIRED_FA501_EVIDENCE_JOB_ID),
        ("FA501_EVIDENCE_HEAD_SHA", REQUIRED_FA501_EVIDENCE_HEAD_SHA),
        ("FA501_EVIDENCE_SOURCE_SHA256", REQUIRED_FA501_SOURCE_SHA256),
        ("FA501_FIRST_ERROR_LINE", REQUIRED_FA501_FIRST_ERROR_LINE),
        ("FA501_FIRST_ERROR_COL", REQUIRED_FA501_FIRST_ERROR_COL),
        ("FA501_FRONTIER_DECLARATION", REQUIRED_FA501_FRONTIER_DECLARATION),
        ("FA501_FRONTIER_INDEX", REQUIRED_FA501_FRONTIER_INDEX),
    ]:
        req(k, v)
    if os.environ.get("FA502_VARIANT") != "pi_zero_apply":
        raise RuntimeError(f"unsupported FA502_VARIANT={os.environ.get('FA502_VARIANT')!r}")

    text, repairs = orig_norm_repairs(text)
    if sha(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA502 exact FA501 source mismatch: {sha(text)}")

    start, end = bounds(text, TARGET_DECLARATION)
    reg = text[start:end]
    h = header(reg)
    if reg.count(OLD_FRAGMENT) != 1:
        raise RuntimeError(f"FA502 target fragment count={reg.count(OLD_FRAGMENT)}, expected 1")
    new_reg = reg.replace(OLD_FRAGMENT, NEW_FRAGMENT, 1)
    cand = text[:start] + new_reg + text[end:]

    if header(new_reg) != h:
        raise RuntimeError("FA502 theorem header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(cand)]
    if before != after:
        raise RuntimeError("FA502 declaration sequence drift")

    return cand, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": "add Pi.zero_apply to the terminal simp-only closure for the observed residual goal 0 = 0 r",
            "matrix_variant": "pi_zero_apply",
            "required_fa501_evidence_run_id": int(REQUIRED_FA501_EVIDENCE_RUN_ID),
            "required_fa501_evidence_job_id": int(REQUIRED_FA501_EVIDENCE_JOB_ID),
            "required_fa501_evidence_head_sha": REQUIRED_FA501_EVIDENCE_HEAD_SHA,
            "required_fa501_source_sha256": REQUIRED_FA501_SOURCE_SHA256,
            "required_fa501_first_error_line": int(REQUIRED_FA501_FIRST_ERROR_LINE),
            "required_fa501_first_error_col": int(REQUIRED_FA501_FIRST_ERROR_COL),
            "candidate_source_sha256": sha(cand),
            "candidate_line_count": len(cand.splitlines()),
            "target_header_preserved": True,
            "declaration_sequence_preserved": True,
            "claims_preserved": True,
            "later_repair_count": 0,
        },
        {
            "declaration": "FA502 strict-frontier repair",
            "strategy": "pi_zero_apply",
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]

fa466.norm_repairs = norm_repairs
if __name__ == "__main__":
    fa466.main()
