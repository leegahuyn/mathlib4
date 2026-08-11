#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa489_prepare_hderiv_explicit_continuity.py"
spec = importlib.util.spec_from_file_location("fa489base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa489 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa489
spec.loader.exec_module(fa489)

fa466 = fa489.fa466
orig_norm_repairs = fa489.norm_repairs

EXACT_FA489_VARIANT = "reuse_local_continuity"
REQUIRED_FA489_EVIDENCE_RUN_ID = "31456858385"
REQUIRED_FA489_EVIDENCE_JOB_ID = "93672410171"
REQUIRED_FA489_EVIDENCE_HEAD_SHA = "a0b047f5d5894547847966e7e049519b1f9b9edd"
REQUIRED_FA489_SOURCE_SHA256 = "365b4489c1a6c60380a40466a50ca338aae5efa14cbdf21fbe97d848bcf540af"
REQUIRED_FA489_FIRST_ERROR_LINE = "35363"
REQUIRED_FA489_FIRST_ERROR_COL = "8"
REQUIRED_FA489_FRONTIER_DECLARATION = "selectedLogHeightNaturalGauge_uniform_eventually_zero"
REQUIRED_FA489_FRONTIER_INDEX = "2807"

TARGET_DECLARATION = REQUIRED_FA489_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2807
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA489_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_LINE = "    rw [hlevel]"
NEW_LINE = "    simp only [hlevel]"

VARIANTS = {
    "simp_only_hlevel": (
        ((OLD_LINE, NEW_LINE),),
        "replace the observed dependent rw [hlevel] with simp-only rewriting so UpperHalfPlane proof fields are handled by simplifier congruence",
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
            f"FA490 requires exact FA489 source {EXPECTED_INTERMEDIATE_SOURCE_SHA256}, got {intermediate_sha}"
        )
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA490 intermediate line-count drift")

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
        raise RuntimeError("FA490 target header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA490 declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA490 candidate line count changed")

    return candidate, {
        "fa489_intermediate_source_sha256": intermediate_sha,
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
        raise RuntimeError(f"FA490 requires {name}={expected}, got {actual!r}")


def norm_repairs(text: str):
    req("FA489_VARIANT", EXACT_FA489_VARIANT)
    req("FA489_EVIDENCE_RUN_ID", REQUIRED_FA489_EVIDENCE_RUN_ID)
    req("FA489_EVIDENCE_JOB_ID", REQUIRED_FA489_EVIDENCE_JOB_ID)
    req("FA489_EVIDENCE_HEAD_SHA", REQUIRED_FA489_EVIDENCE_HEAD_SHA)
    req("FA489_EVIDENCE_SOURCE_SHA256", REQUIRED_FA489_SOURCE_SHA256)
    req("FA489_FIRST_ERROR_LINE", REQUIRED_FA489_FIRST_ERROR_LINE)
    req("FA489_FIRST_ERROR_COL", REQUIRED_FA489_FIRST_ERROR_COL)
    req("FA489_FRONTIER_DECLARATION", REQUIRED_FA489_FRONTIER_DECLARATION)
    req("FA489_FRONTIER_INDEX", REQUIRED_FA489_FRONTIER_INDEX)

    variant = os.environ.get("FA490_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA490_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "required_fa489_evidence_run_id": int(REQUIRED_FA489_EVIDENCE_RUN_ID),
            "required_fa489_evidence_job_id": int(REQUIRED_FA489_EVIDENCE_JOB_ID),
            "required_fa489_evidence_head_sha": REQUIRED_FA489_EVIDENCE_HEAD_SHA,
            "required_fa489_source_sha256": REQUIRED_FA489_SOURCE_SHA256,
            "required_fa489_first_error_line": int(REQUIRED_FA489_FIRST_ERROR_LINE),
            "required_fa489_first_error_col": int(REQUIRED_FA489_FIRST_ERROR_COL),
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA490 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
