#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa486_prepare_hpoint_upperhalfplanemk.py"
spec = importlib.util.spec_from_file_location("fa486base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa486 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa486
spec.loader.exec_module(fa486)

fa466 = fa486.fa466
orig_norm_repairs = fa486.norm_repairs

EXACT_FA486_VARIANT = "explicit_upper_half_plane_mk"
REQUIRED_FA486_EVIDENCE_RUN_ID = "31454730748"
REQUIRED_FA486_EVIDENCE_JOB_ID = "93666070352"
REQUIRED_FA486_EVIDENCE_HEAD_SHA = "946e1900d0470dc8db26fce4f5590e1302533ca5"
REQUIRED_FA486_SOURCE_SHA256 = "22b60d646ff8744f3a59d6d2e35f8698a746b30df1e11a5c4ea0042929decadb"
REQUIRED_FA486_FIRST_ERROR_LINE = "35312"
REQUIRED_FA486_FIRST_ERROR_COL = "14"
REQUIRED_FA486_FRONTIER_DECLARATION = "selectedLogHeightEnergyDensity_continuous"
REQUIRED_FA486_FRONTIER_INDEX = "2806"

TARGET_DECLARATION = REQUIRED_FA486_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2806
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA486_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_FRAGMENT = """    unfold logHeightBasePoint
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ => Complex.mk p.1 (Real.exp p.2))).upperHalfPlaneMk (fun p => Real.exp_pos p.2)"""
NEW_FRAGMENT = """    unfold logHeightBasePoint
    exact (by simpa only [Complex.mk_eq_add_mul_I] using (by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) + ((Real.exp p.2 : ℝ) : ℂ) * Complex.I))).upperHalfPlaneMk (fun p => Real.exp_pos p.2)"""

VARIANTS = {
    "mk_eq_add_mul_i": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "keep the verified Continuous.upperHalfPlaneMk construction but prove the underlying Complex.mk map continuous by rewriting Complex.mk with Complex.mk_eq_add_mul_I before fun_prop",
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
    intermediate_sha = sha256_text(text)
    if intermediate_sha != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(
            f"FA487 requires exact FA486 source {EXPECTED_INTERMEDIATE_SOURCE_SHA256}, got {intermediate_sha}"
        )
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA487 intermediate line-count drift")

    start, end = bounds(text, TARGET_DECLARATION)
    prefix, region, suffix = text[:start], text[start:end], text[end:]
    old_header = header(region)
    audit = []
    for old, new in replacements:
        oc, nc = region.count(old), region.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"target old/new counts {oc}/{nc}, expected 1/0")
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
        raise RuntimeError("FA487 header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA487 declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA487 candidate line count changed")

    return candidate, {
        "fa486_intermediate_source_sha256": intermediate_sha,
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
        raise RuntimeError(f"FA487 requires {name}={expected}, got {actual!r}")


def norm_repairs(text: str):
    req("FA486_VARIANT", EXACT_FA486_VARIANT)
    req("FA486_EVIDENCE_RUN_ID", REQUIRED_FA486_EVIDENCE_RUN_ID)
    req("FA486_EVIDENCE_JOB_ID", REQUIRED_FA486_EVIDENCE_JOB_ID)
    req("FA486_EVIDENCE_HEAD_SHA", REQUIRED_FA486_EVIDENCE_HEAD_SHA)
    req("FA486_EVIDENCE_SOURCE_SHA256", REQUIRED_FA486_SOURCE_SHA256)
    req("FA486_FIRST_ERROR_LINE", REQUIRED_FA486_FIRST_ERROR_LINE)
    req("FA486_FIRST_ERROR_COL", REQUIRED_FA486_FIRST_ERROR_COL)
    req("FA486_FRONTIER_DECLARATION", REQUIRED_FA486_FRONTIER_DECLARATION)
    req("FA486_FRONTIER_INDEX", REQUIRED_FA486_FRONTIER_INDEX)

    variant = os.environ.get("FA487_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA487_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "required_fa486_evidence_run_id": int(REQUIRED_FA486_EVIDENCE_RUN_ID),
            "required_fa486_evidence_job_id": int(REQUIRED_FA486_EVIDENCE_JOB_ID),
            "required_fa486_evidence_head_sha": REQUIRED_FA486_EVIDENCE_HEAD_SHA,
            "required_fa486_source_sha256": REQUIRED_FA486_SOURCE_SHA256,
            "required_fa486_first_error_line": int(REQUIRED_FA486_FIRST_ERROR_LINE),
            "required_fa486_first_error_col": int(REQUIRED_FA486_FIRST_ERROR_COL),
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA487 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
