#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa484_prepare_logheight_energy_real_norm.py"
spec = importlib.util.spec_from_file_location("fa484base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa484 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa484
spec.loader.exec_module(fa484)

fa466 = fa484.fa466
orig_norm_repairs = fa484.norm_repairs

EXACT_FA484_VARIANT = "real_norm_eq_abs_bridge"
REQUIRED_FA484_EVIDENCE_RUN_ID = "31451815080"
REQUIRED_FA484_EVIDENCE_JOB_ID = "93657549435"
REQUIRED_FA484_EVIDENCE_HEAD_SHA = "5553ea94b57f065f578569b6a75daf184c18b841"
REQUIRED_FA484_SOURCE_SHA256 = "c4a4dc3bac0d11381071fd11513b175f8eb5f93037e27ed3622bba1a2df26eb6"
REQUIRED_FA484_FIRST_ERROR_LINE = "35280"
REQUIRED_FA484_FIRST_ERROR_COL = "8"
REQUIRED_FA484_FRONTIER_DECLARATION = (
    "selectedLogHeightEnergyDensity_le_exp_mul_heightGraphDensity"
)
REQUIRED_FA484_FRONTIER_INDEX = "2805"

TARGET_DECLARATION = REQUIRED_FA484_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2805
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA484_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_REDUNDANT_RING = """        rw [mul_pow, mul_pow, hExp]
        ring"""
NEW_REDUNDANT_RING = """        rw [mul_pow, mul_pow, hExp]
        -- The rewrite already closes this normalized square identity."""

VARIANTS = {
    "drop_redundant_ring": (
        ((OLD_REDUNDANT_RING, NEW_REDUNDANT_RING),),
        (
            "remove the redundant ring tactic after rw [mul_pow, mul_pow, hExp] "
            "because direct Lean reports that the rewrite already closes the goal"
        ),
    ),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def declaration_bounds(text: str, declaration: str) -> tuple[int, int]:
    starts = list(_DECL_START.finditer(text))
    hits = [i for i, m in enumerate(starts) if m.group("name") == declaration]
    if len(hits) != 1:
        raise RuntimeError(
            f"expected exactly one declaration {declaration!r}, found {len(hits)}"
        )
    i = hits[0]
    start = starts[i].start()
    end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
    return start, end


def declaration_header(region: str) -> str:
    marker = region.find(":=")
    if marker < 0:
        raise RuntimeError(f"{TARGET_DECLARATION}: declaration header has no :=")
    return region[: marker + 2]


def replace_target_only(text: str, replacements: tuple[tuple[str, str], ...]):
    intermediate_sha256 = sha256_text(text)
    if intermediate_sha256 != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(
            "FA485 requires exact direct-Lean-observed FA484 source; got "
            f"{intermediate_sha256}, expected {EXPECTED_INTERMEDIATE_SOURCE_SHA256}"
        )
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError(
            f"FA485 intermediate line-count drift: {len(text.splitlines())} != "
            f"{EXPECTED_LINE_COUNT}"
        )

    start, end = declaration_bounds(text, TARGET_DECLARATION)
    next_doc = text.rfind("\n/--", start, end)
    logical_end = next_doc + 1 if next_doc >= start else end
    prefix = text[:start]
    original_region = text[start:logical_end]
    suffix = text[logical_end:]
    original_header = declaration_header(original_region)

    region = original_region
    audits: list[dict[str, object]] = []
    for old, new in replacements:
        old_count_target = region.count(old)
        new_count_target = region.count(new)
        if old_count_target != 1 or new_count_target != 0:
            raise RuntimeError(
                f"{TARGET_DECLARATION}: expected target old/new counts 1/0, got "
                f"{old_count_target}/{new_count_target}"
            )
        region = region.replace(old, new, 1)
        audits.append(
            {
                "old_count_before": old_count_target,
                "old_global_count_before": text.count(old),
                "new_count_before": new_count_target,
                "new_global_count_before": text.count(new),
                "old_sha256": sha256_text(old),
                "new_sha256": sha256_text(new),
                "old_bytes": len(old.encode("utf-8")),
                "new_bytes": len(new.encode("utf-8")),
            }
        )

    candidate = prefix + region + suffix
    candidate_end = start + len(region)
    header_preserved = declaration_header(region) == original_header
    prefix_preserved = candidate[:start] == prefix
    suffix_preserved = candidate[candidate_end:] == suffix
    if not (header_preserved and prefix_preserved and suffix_preserved):
        raise RuntimeError(f"{TARGET_DECLARATION}: preservation failure")

    before_sequence = [m.group("name") for m in _DECL_START.finditer(text)]
    after_sequence = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before_sequence != after_sequence:
        raise RuntimeError(f"{TARGET_DECLARATION}: declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA485 candidate line count changed")

    return candidate, {
        "fa484_intermediate_source_sha256": intermediate_sha256,
        "candidate_source_sha256": sha256_text(candidate),
        "required_line_count": EXPECTED_LINE_COUNT,
        "candidate_line_count": len(candidate.splitlines()),
        "replacement_count": len(replacements),
        "target_header_sha256": sha256_text(original_header),
        "target_header_preserved": header_preserved,
        "source_prefix_sha256": sha256_text(prefix),
        "source_prefix_bytes": len(prefix.encode("utf-8")),
        "source_prefix_preserved": prefix_preserved,
        "source_suffix_sha256": sha256_text(suffix),
        "source_suffix_bytes": len(suffix.encode("utf-8")),
        "source_suffix_preserved": suffix_preserved,
        "target_region_before_sha256": sha256_text(original_region),
        "target_region_after_sha256": sha256_text(region),
        "declaration_sequence_sha256": sha256_text("\n".join(before_sequence)),
        "declaration_sequence_preserved": True,
        "replacement_audit": audits,
    }


def _require(name: str, expected: str) -> str:
    actual = os.environ.get(name)
    if actual != expected:
        raise RuntimeError(f"FA485 requires {name}={expected}, got {actual!r}")
    return actual


def norm_repairs(text: str):
    _require("FA484_VARIANT", EXACT_FA484_VARIANT)
    _require("FA484_EVIDENCE_RUN_ID", REQUIRED_FA484_EVIDENCE_RUN_ID)
    _require("FA484_EVIDENCE_JOB_ID", REQUIRED_FA484_EVIDENCE_JOB_ID)
    _require("FA484_EVIDENCE_HEAD_SHA", REQUIRED_FA484_EVIDENCE_HEAD_SHA)
    _require("FA484_EVIDENCE_SOURCE_SHA256", REQUIRED_FA484_SOURCE_SHA256)
    _require("FA484_FIRST_ERROR_LINE", REQUIRED_FA484_FIRST_ERROR_LINE)
    _require("FA484_FIRST_ERROR_COL", REQUIRED_FA484_FIRST_ERROR_COL)
    _require("FA484_FRONTIER_DECLARATION", REQUIRED_FA484_FRONTIER_DECLARATION)
    _require("FA484_FRONTIER_INDEX", REQUIRED_FA484_FRONTIER_INDEX)

    variant = os.environ.get("FA485_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported or missing FA485_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    if sha256_text(text) != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError("FA485 upstream FA484 materialization identity mismatch")

    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target_only(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "fa484_variant": EXACT_FA484_VARIANT,
            "required_fa484_evidence_run_id": int(REQUIRED_FA484_EVIDENCE_RUN_ID),
            "required_fa484_evidence_job_id": int(REQUIRED_FA484_EVIDENCE_JOB_ID),
            "required_fa484_evidence_head_sha": REQUIRED_FA484_EVIDENCE_HEAD_SHA,
            "required_fa484_source_sha256": REQUIRED_FA484_SOURCE_SHA256,
            "required_fa484_first_error_line": int(REQUIRED_FA484_FIRST_ERROR_LINE),
            "required_fa484_first_error_col": int(REQUIRED_FA484_FIRST_ERROR_COL),
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA485 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
