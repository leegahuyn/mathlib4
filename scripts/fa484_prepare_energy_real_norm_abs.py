#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa483_prepare_selected_height_exp.py"
spec = importlib.util.spec_from_file_location("fa483base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa483 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa483
spec.loader.exec_module(fa483)

fa466 = fa483.fa466
orig_norm_repairs = fa483.norm_repairs

EXACT_FA483_VARIANT = "upper_ext_remove_mk_im"
REQUIRED_FA483_EVIDENCE_RUN_ID = "31451101943"
REQUIRED_FA483_EVIDENCE_JOB_ID = "93655461634"
REQUIRED_FA483_EVIDENCE_HEAD_SHA = "9ff7ac197487de1f38f63c28d5e52382718738b3"
REQUIRED_FA483_SOURCE_SHA256 = "34756fc6e6c20dab3d2ff5a125934dde7a065fdee57a9c5b6f2381240ee8481d"
REQUIRED_FA483_FIRST_ERROR_LINE = "35255"
REQUIRED_FA483_FIRST_ERROR_COL = "37"
REQUIRED_FA483_FRONTIER_DECLARATION = "selectedLogHeightEnergyDensity_le_exp_mul_heightGraphDensity"
REQUIRED_FA483_FRONTIER_INDEX = "2805"

TARGET_DECLARATION = REQUIRED_FA483_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2805
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA483_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_RW = """    rw [norm_mul, Complex.norm_real, abs_of_pos (Real.exp_pos _),
      hPullNorm, mul_pow, mul_pow, hExp]"""
NEW_RW = """    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), hPullNorm, mul_pow, mul_pow, hExp]"""

VARIANTS = {
    "real_norm_eq_abs": (
        ((OLD_RW, NEW_RW),),
        "insert Real.norm_eq_abs between Complex.norm_real and abs_of_pos in hNatural",
    ),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def bounds(text: str, declaration: str) -> tuple[int, int]:
    starts = list(_DECL_START.finditer(text))
    hits = [i for i, m in enumerate(starts) if m.group("name") == declaration]
    if len(hits) != 1:
        raise RuntimeError(f"expected one {declaration}, found {len(hits)}")
    i = hits[0]
    return starts[i].start(), starts[i + 1].start() if i + 1 < len(starts) else len(text)


def header(region: str) -> str:
    p = region.find(":=")
    if p < 0:
        raise RuntimeError("target header has no :=")
    return region[: p + 2]


def replace_target(text: str, replacements: tuple[tuple[str, str], ...]):
    if sha256_text(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError("FA484 upstream FA483 source identity mismatch")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA484 intermediate line-count drift")
    start, end = bounds(text, TARGET_DECLARATION)
    prefix, region, suffix = text[:start], text[start:end], text[end:]
    old_header = header(region)
    audit = []
    for old, new in replacements:
        oc, nc = region.count(old), region.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"target old/new counts {oc}/{nc}, expected 1/0")
        region = region.replace(old, new, 1)
        audit.append({"old_count_before": oc, "old_global_count_before": text.count(old),
                      "new_count_before": nc, "new_global_count_before": text.count(new),
                      "old_sha256": sha256_text(old), "new_sha256": sha256_text(new)})
    candidate = prefix + region + suffix
    if header(region) != old_header:
        raise RuntimeError("FA484 header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA484 declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA484 line count changed")
    return candidate, {
        "fa483_intermediate_source_sha256": sha256_text(text),
        "candidate_source_sha256": sha256_text(candidate),
        "required_line_count": EXPECTED_LINE_COUNT,
        "candidate_line_count": len(candidate.splitlines()),
        "replacement_count": len(replacements),
        "target_header_sha256": sha256_text(old_header),
        "target_header_preserved": True,
        "source_prefix_preserved": candidate[:start] == prefix,
        "source_suffix_preserved": candidate[start + len(region):] == suffix,
        "declaration_sequence_sha256": sha256_text("\n".join(before)),
        "declaration_sequence_preserved": True,
        "replacement_audit": audit,
    }


def req(name: str, expected: str):
    actual = os.environ.get(name)
    if actual != expected:
        raise RuntimeError(f"FA484 requires {name}={expected}, got {actual!r}")


def norm_repairs(text: str):
    req("FA483_VARIANT", EXACT_FA483_VARIANT)
    req("FA483_EVIDENCE_RUN_ID", REQUIRED_FA483_EVIDENCE_RUN_ID)
    req("FA483_EVIDENCE_JOB_ID", REQUIRED_FA483_EVIDENCE_JOB_ID)
    req("FA483_EVIDENCE_HEAD_SHA", REQUIRED_FA483_EVIDENCE_HEAD_SHA)
    req("FA483_EVIDENCE_SOURCE_SHA256", REQUIRED_FA483_SOURCE_SHA256)
    req("FA483_FIRST_ERROR_LINE", REQUIRED_FA483_FIRST_ERROR_LINE)
    req("FA483_FIRST_ERROR_COL", REQUIRED_FA483_FIRST_ERROR_COL)
    req("FA483_FRONTIER_DECLARATION", REQUIRED_FA483_FRONTIER_DECLARATION)
    req("FA483_FRONTIER_INDEX", REQUIRED_FA483_FRONTIER_INDEX)
    variant = os.environ.get("FA484_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA484_VARIANT={variant!r}")
    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target(text, replacements)
    return text, repairs + [
        {"declaration": TARGET_DECLARATION, "declaration_index": TARGET_DECLARATION_INDEX,
         "strategy": strategy, "matrix_variant": variant,
         "required_fa483_evidence_run_id": int(REQUIRED_FA483_EVIDENCE_RUN_ID),
         "required_fa483_evidence_job_id": int(REQUIRED_FA483_EVIDENCE_JOB_ID),
         "required_fa483_evidence_head_sha": REQUIRED_FA483_EVIDENCE_HEAD_SHA,
         "required_fa483_source_sha256": REQUIRED_FA483_SOURCE_SHA256,
         "required_fa483_first_error_line": int(REQUIRED_FA483_FIRST_ERROR_LINE),
         "required_fa483_first_error_col": int(REQUIRED_FA483_FIRST_ERROR_COL),
         "frontier_declaration_index": TARGET_DECLARATION_INDEX, "later_repair_count": 0,
         "max_errors": 32, **audit},
        {"declaration": "FA484 strict-frontier repair", "strategy": variant,
         "target_declaration": TARGET_DECLARATION,
         "target_declaration_index": TARGET_DECLARATION_INDEX, "later_repair_count": 0},
    ]

fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
