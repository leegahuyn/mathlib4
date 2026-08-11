#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa487_prepare_hpoint_unfold.py"
spec = importlib.util.spec_from_file_location("fa487base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa487 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa487
spec.loader.exec_module(fa487)

fa466 = fa487.fa466
orig_norm_repairs = fa487.norm_repairs

EXACT_FA487_VARIANT = "unfold_then_fun_prop"
REQUIRED_FA487_EVIDENCE_RUN_ID = "31454231182"
REQUIRED_FA487_EVIDENCE_JOB_ID = "93664635881"
REQUIRED_FA487_EVIDENCE_HEAD_SHA = "00698e6abd9848b6f12c2a51b5f19d115505be00"
REQUIRED_FA487_SOURCE_SHA256 = "9c38c6e6a405f6f3f117b9c3085938d52287ac34bc6a2e247460209b2df09404"
REQUIRED_FA487_FIRST_ERROR_LINE = "35312"
REQUIRED_FA487_FIRST_ERROR_COL = "4"
REQUIRED_FA487_FRONTIER_DECLARATION = "selectedLogHeightEnergyDensity_continuous"
REQUIRED_FA487_FRONTIER_INDEX = "2806"

TARGET_DECLARATION = REQUIRED_FA487_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2806
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA487_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_BLOCK = """    unfold logHeightBasePoint
    fun_prop"""
NEW_BLOCK = """    refine Continuous.subtype_mk ?_ (fun p => Real.exp_pos p.2)
    simpa only [Complex.mk_eq_add_mul_I] using ((Complex.continuous_ofReal.comp continuous_fst).add ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_snd)).mul continuous_const))"""

VARIANTS = {
    "explicit_complex_subtype_continuity": (
        ((OLD_BLOCK, NEW_BLOCK),),
        "prove the underlying Complex.mk chart explicitly via ofReal/add/mul/I, then lift continuity with Continuous.subtype_mk and Real.exp_pos",
    ),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def bounds(text: str, declaration: str) -> tuple[int, int]:
    starts = list(_DECL_START.finditer(text))
    hits = [i for i, m in enumerate(starts) if m.group("name") == declaration]
    if len(hits) != 1:
        raise RuntimeError(f"expected exactly one declaration {declaration!r}, found {len(hits)}")
    i = hits[0]
    return starts[i].start(), starts[i + 1].start() if i + 1 < len(starts) else len(text)


def header(region: str) -> str:
    p = region.find(":=")
    if p < 0:
        raise RuntimeError("target declaration header has no :=")
    return region[:p + 2]


def replace_target(text: str, replacements: tuple[tuple[str, str], ...]):
    actual_sha = sha256_text(text)
    if actual_sha != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(
            f"FA488 requires exact FA487 source {EXPECTED_INTERMEDIATE_SOURCE_SHA256}, got {actual_sha}"
        )
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA488 intermediate line-count drift")

    start, end = bounds(text, TARGET_DECLARATION)
    prefix, region, suffix = text[:start], text[start:end], text[end:]
    old_header = header(region)
    audit = []
    for old, new in replacements:
        oc, nc = region.count(old), region.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"{TARGET_DECLARATION}: expected target old/new 1/0, got {oc}/{nc}")
        region = region.replace(old, new, 1)
        audit.append({
            "old_count_before": oc,
            "old_global_count_before": text.count(old),
            "new_count_before": nc,
            "new_global_count_before": text.count(new),
            "old_sha256": sha256_text(old),
            "new_sha256": sha256_text(new),
        })

    candidate = prefix + region + suffix
    if header(region) != old_header:
        raise RuntimeError("FA488 target header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA488 declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA488 candidate line count changed")
    return candidate, {
        "fa487_intermediate_source_sha256": actual_sha,
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
        raise RuntimeError(f"FA488 requires {name}={expected}, got {actual!r}")


def norm_repairs(text: str):
    req("FA487_VARIANT", EXACT_FA487_VARIANT)
    req("FA487_EVIDENCE_RUN_ID", REQUIRED_FA487_EVIDENCE_RUN_ID)
    req("FA487_EVIDENCE_JOB_ID", REQUIRED_FA487_EVIDENCE_JOB_ID)
    req("FA487_EVIDENCE_HEAD_SHA", REQUIRED_FA487_EVIDENCE_HEAD_SHA)
    req("FA487_EVIDENCE_SOURCE_SHA256", REQUIRED_FA487_SOURCE_SHA256)
    req("FA487_FIRST_ERROR_LINE", REQUIRED_FA487_FIRST_ERROR_LINE)
    req("FA487_FIRST_ERROR_COL", REQUIRED_FA487_FIRST_ERROR_COL)
    req("FA487_FRONTIER_DECLARATION", REQUIRED_FA487_FRONTIER_DECLARATION)
    req("FA487_FRONTIER_INDEX", REQUIRED_FA487_FRONTIER_INDEX)

    variant = os.environ.get("FA488_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA488_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "required_fa487_evidence_run_id": int(REQUIRED_FA487_EVIDENCE_RUN_ID),
            "required_fa487_evidence_job_id": int(REQUIRED_FA487_EVIDENCE_JOB_ID),
            "required_fa487_evidence_head_sha": REQUIRED_FA487_EVIDENCE_HEAD_SHA,
            "required_fa487_source_sha256": REQUIRED_FA487_SOURCE_SHA256,
            "required_fa487_first_error_line": int(REQUIRED_FA487_FIRST_ERROR_LINE),
            "required_fa487_first_error_col": int(REQUIRED_FA487_FIRST_ERROR_COL),
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA488 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]

fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
