#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa488_prepare_hpoint_typed_by.py"
spec = importlib.util.spec_from_file_location("fa488base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa488 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa488
spec.loader.exec_module(fa488)

fa466 = fa488.fa466
orig_norm_repairs = fa488.norm_repairs

EXACT_FA488_VARIANT = "typed_by"
REQUIRED_FA488_EVIDENCE_RUN_ID = "31456106488"
REQUIRED_FA488_EVIDENCE_JOB_ID = "93670098634"
REQUIRED_FA488_EVIDENCE_HEAD_SHA = "ca9f7071476b843379f67765ca43ba7cc327d6be"
REQUIRED_FA488_SOURCE_SHA256 = "efabb4d229666d7a6e292e853aa583833ae6c99d0bb6d65689168015eccb93ca"
REQUIRED_FA488_FIRST_ERROR_LINE = "35337"
REQUIRED_FA488_FIRST_ERROR_COL = "4"
REQUIRED_FA488_FRONTIER_DECLARATION = "selectedLogHeightEnergyDensity_continuous"
REQUIRED_FA488_FRONTIER_INDEX = "2806"

TARGET_DECLARATION = REQUIRED_FA488_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2806
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA488_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_FRAGMENT = """    rw [hExplicit]
    fun_prop"""
NEW_FRAGMENT = """    rw [hExplicit]
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ => ((Real.exp (p.2 / 2) : ℝ) : ℂ))).mul ((continuous_const.mul hcomp).add ((HalfWeightDifferentialOperators.realSmooth_heightC.continuous.comp hpoint).mul hdycomp))"""

VARIANTS = {
    "reuse_local_continuity": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "replace the failing global fun_prop search with explicit continuity composition from the already proved hcomp, hdycomp, hpoint, realSmooth_heightC, and the elementary exponential prefactor",
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
            f"FA489 requires exact FA488 source {EXPECTED_INTERMEDIATE_SOURCE_SHA256}, got {intermediate_sha}"
        )
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA489 intermediate line-count drift")

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
        raise RuntimeError("FA489 header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA489 declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA489 candidate line count changed")

    return candidate, {
        "fa488_intermediate_source_sha256": intermediate_sha,
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
        raise RuntimeError(f"FA489 requires {name}={expected}, got {actual!r}")


def norm_repairs(text: str):
    req("FA488_VARIANT", EXACT_FA488_VARIANT)
    req("FA488_EVIDENCE_RUN_ID", REQUIRED_FA488_EVIDENCE_RUN_ID)
    req("FA488_EVIDENCE_JOB_ID", REQUIRED_FA488_EVIDENCE_JOB_ID)
    req("FA488_EVIDENCE_HEAD_SHA", REQUIRED_FA488_EVIDENCE_HEAD_SHA)
    req("FA488_EVIDENCE_SOURCE_SHA256", REQUIRED_FA488_SOURCE_SHA256)
    req("FA488_FIRST_ERROR_LINE", REQUIRED_FA488_FIRST_ERROR_LINE)
    req("FA488_FIRST_ERROR_COL", REQUIRED_FA488_FIRST_ERROR_COL)
    req("FA488_FRONTIER_DECLARATION", REQUIRED_FA488_FRONTIER_DECLARATION)
    req("FA488_FRONTIER_INDEX", REQUIRED_FA488_FRONTIER_INDEX)

    variant = os.environ.get("FA489_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA489_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "required_fa488_evidence_run_id": int(REQUIRED_FA488_EVIDENCE_RUN_ID),
            "required_fa488_evidence_job_id": int(REQUIRED_FA488_EVIDENCE_JOB_ID),
            "required_fa488_evidence_head_sha": REQUIRED_FA488_EVIDENCE_HEAD_SHA,
            "required_fa488_source_sha256": REQUIRED_FA488_SOURCE_SHA256,
            "required_fa488_first_error_line": int(REQUIRED_FA488_FIRST_ERROR_LINE),
            "required_fa488_first_error_col": int(REQUIRED_FA488_FIRST_ERROR_COL),
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA489 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
