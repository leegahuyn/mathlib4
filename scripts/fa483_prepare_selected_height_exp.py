#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa482_prepare_selected_height_remove_mk_im.py"
spec = importlib.util.spec_from_file_location("fa482base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa482 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa482
spec.loader.exec_module(fa482)

fa466 = fa482.fa466
orig_norm_repairs = fa482.norm_repairs

EXACT_FA482_VARIANT = "remove_complex_mk_im"
REQUIRED_FA482_EVIDENCE_RUN_ID = "31450425677"
REQUIRED_FA482_EVIDENCE_JOB_ID = "93653492331"
REQUIRED_FA482_EVIDENCE_HEAD_SHA = "a0a19ee27ba6c07d30bdd347150bd71550c80f69"
REQUIRED_FA482_SOURCE_SHA256 = "daeb276e2c3886ebd9cd93c752e813dc7b288ceb4a872ba734c7634bd0c807ca"
REQUIRED_FA482_FIRST_ERROR_LINE = "35203"
REQUIRED_FA482_FIRST_ERROR_COL = "2"
REQUIRED_FA482_FRONTIER_DECLARATION = "selectedHeightBasePoint_exp"
REQUIRED_FA482_FRONTIER_INDEX = "2803"

TARGET_DECLARATION = "selectedHeightBasePoint_exp"
TARGET_DECLARATION_INDEX = 2803
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA482_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_EXT = "  apply Subtype.ext"
NEW_EXT = "  apply UpperHalfPlane.ext"
OLD_SIMP = """  simp only [selectedHeightBasePoint, logHeightBasePoint,
    UpperHalfPlane.ofComplex_apply_of_im_pos, Complex.mk_im, Real.exp_pos]"""
NEW_SIMP = """  simp only [selectedHeightBasePoint, logHeightBasePoint,
    UpperHalfPlane.ofComplex_apply_of_im_pos, Real.exp_pos]"""

VARIANTS = {
    "upper_ext_remove_mk_im": (
        ((OLD_EXT, NEW_EXT), (OLD_SIMP, NEW_SIMP)),
        "use UpperHalfPlane.ext and remove nonexistent Complex.mk_im within declaration 2803",
    ),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def declaration_bounds(text: str, declaration: str) -> tuple[int, int]:
    starts = list(_DECL_START.finditer(text))
    hits = [i for i, m in enumerate(starts) if m.group("name") == declaration]
    if len(hits) != 1:
        raise RuntimeError(f"expected exactly one declaration {declaration!r}, found {len(hits)}")
    i = hits[0]
    return starts[i].start(), starts[i + 1].start() if i + 1 < len(starts) else len(text)


def declaration_header(region: str) -> str:
    marker = region.find(":=")
    if marker < 0:
        raise RuntimeError(f"{TARGET_DECLARATION}: declaration header has no :=")
    return region[: marker + 2]


def replace_target_only(text: str, replacements: tuple[tuple[str, str], ...]):
    intermediate_sha256 = sha256_text(text)
    if intermediate_sha256 != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(
            f"FA483 requires exact FA482 source {EXPECTED_INTERMEDIATE_SOURCE_SHA256}, got {intermediate_sha256}"
        )
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA483 intermediate line-count drift")

    start, end = declaration_bounds(text, TARGET_DECLARATION)
    prefix, original_region, suffix = text[:start], text[start:end], text[end:]
    original_header = declaration_header(original_region)
    region = original_region
    audit = []
    for old, new in replacements:
        oc, nc = region.count(old), region.count(new)
        if oc != 1 or nc != 0:
            raise RuntimeError(f"{TARGET_DECLARATION}: expected target old/new counts 1/0, got {oc}/{nc}")
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
    if declaration_header(region) != original_header:
        raise RuntimeError("FA483 target header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA483 declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA483 candidate line count changed")
    return candidate, {
        "fa482_intermediate_source_sha256": intermediate_sha256,
        "candidate_source_sha256": sha256_text(candidate),
        "required_line_count": EXPECTED_LINE_COUNT,
        "candidate_line_count": len(candidate.splitlines()),
        "replacement_count": len(replacements),
        "target_header_sha256": sha256_text(original_header),
        "target_header_preserved": True,
        "source_prefix_preserved": candidate[:start] == prefix,
        "source_suffix_preserved": candidate[start + len(region):] == suffix,
        "declaration_sequence_sha256": sha256_text("\n".join(before)),
        "declaration_sequence_preserved": True,
        "replacement_audit": audit,
    }


def _require(name: str, expected: str) -> str:
    actual = os.environ.get(name)
    if actual != expected:
        raise RuntimeError(f"FA483 requires {name}={expected}, got {actual!r}")
    return actual


def norm_repairs(text: str):
    _require("FA482_VARIANT", EXACT_FA482_VARIANT)
    _require("FA482_EVIDENCE_RUN_ID", REQUIRED_FA482_EVIDENCE_RUN_ID)
    _require("FA482_EVIDENCE_JOB_ID", REQUIRED_FA482_EVIDENCE_JOB_ID)
    _require("FA482_EVIDENCE_HEAD_SHA", REQUIRED_FA482_EVIDENCE_HEAD_SHA)
    _require("FA482_EVIDENCE_SOURCE_SHA256", REQUIRED_FA482_SOURCE_SHA256)
    _require("FA482_FIRST_ERROR_LINE", REQUIRED_FA482_FIRST_ERROR_LINE)
    _require("FA482_FIRST_ERROR_COL", REQUIRED_FA482_FIRST_ERROR_COL)
    _require("FA482_FRONTIER_DECLARATION", REQUIRED_FA482_FRONTIER_DECLARATION)
    _require("FA482_FRONTIER_INDEX", REQUIRED_FA482_FRONTIER_INDEX)

    variant = os.environ.get("FA483_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported or missing FA483_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target_only(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "required_fa482_evidence_run_id": int(REQUIRED_FA482_EVIDENCE_RUN_ID),
            "required_fa482_evidence_job_id": int(REQUIRED_FA482_EVIDENCE_JOB_ID),
            "required_fa482_evidence_head_sha": REQUIRED_FA482_EVIDENCE_HEAD_SHA,
            "required_fa482_source_sha256": REQUIRED_FA482_SOURCE_SHA256,
            "required_fa482_first_error_line": int(REQUIRED_FA482_FIRST_ERROR_LINE),
            "required_fa482_first_error_col": int(REQUIRED_FA482_FIRST_ERROR_COL),
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA483 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]

fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
