#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa490_prepare_uniform_hlevel_simp.py"
spec = importlib.util.spec_from_file_location("fa490base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa490 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa490
spec.loader.exec_module(fa490)

fa466 = fa490.fa466
orig_norm_repairs = fa490.norm_repairs

EXACT_FA490_VARIANT = "simp_only_hlevel"
REQUIRED_FA490_EVIDENCE_RUN_ID = "31457497428"
REQUIRED_FA490_EVIDENCE_JOB_ID = "93674247669"
REQUIRED_FA490_EVIDENCE_HEAD_SHA = "8c0c3bfc53b2bdcd7b5b571e4c26852bd0e3a051"
REQUIRED_FA490_SOURCE_SHA256 = "e1fd4d4370c14185f81faea26e09b8611bf78e19e583026e55d8ee7adbccd40d"
REQUIRED_FA490_FIRST_ERROR_LINE = "35483"
REQUIRED_FA490_FIRST_ERROR_COL = "2"
REQUIRED_FA490_FRONTIER_DECLARATION = "integral_selectedLogHeightEnergyDensity_stripTail_eq_iterated"
REQUIRED_FA490_FRONTIER_INDEX = "2811"

TARGET_DECLARATION = REQUIRED_FA490_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2811
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA490_SOURCE_SHA256
EXPECTED_LINE_COUNT = 60535

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_FRAGMENT = """  change (∫ p, selectedLogHeightEnergyDensity n q u p ∂μ.prod ν) =
    ∫ t, ∫ r, selectedLogHeightEnergyDensity n q u (t, r) ∂ν ∂μ
  exact integral_prod _ hProd"""
NEW_FRAGMENT = """  rw [← Measure.prod_restrict]
  change (∫ p, selectedLogHeightEnergyDensity n q u p ∂μ.prod ν) = ∫ t, ∫ r, selectedLogHeightEnergyDensity n q u (t, r) ∂ν ∂μ
  exact integral_prod _ hProd"""

VARIANTS = {
    "rewrite_prod_restrict_then_fubini": (
        ((OLD_FRAGMENT, NEW_FRAGMENT),),
        "rewrite the set-integral product restriction to the product of the two restricted measures via Measure.prod_restrict before the existing integral_prod Fubini step",
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
    actual_sha = sha256_text(text)
    if actual_sha != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(f"FA491 requires exact FA490 source {EXPECTED_INTERMEDIATE_SOURCE_SHA256}, got {actual_sha}")
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA491 intermediate line-count drift")
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
        raise RuntimeError("FA491 target header drift")
    before = [m.group("name") for m in _DECL_START.finditer(text)]
    after = [m.group("name") for m in _DECL_START.finditer(candidate)]
    if before != after:
        raise RuntimeError("FA491 declaration sequence drift")
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA491 candidate line count changed")
    return candidate, {
        "fa490_intermediate_source_sha256": actual_sha,
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
        raise RuntimeError(f"FA491 requires {name}={expected}, got {actual!r}")


def norm_repairs(text: str):
    req("FA490_VARIANT", EXACT_FA490_VARIANT)
    req("FA490_EVIDENCE_RUN_ID", REQUIRED_FA490_EVIDENCE_RUN_ID)
    req("FA490_EVIDENCE_JOB_ID", REQUIRED_FA490_EVIDENCE_JOB_ID)
    req("FA490_EVIDENCE_HEAD_SHA", REQUIRED_FA490_EVIDENCE_HEAD_SHA)
    req("FA490_EVIDENCE_SOURCE_SHA256", REQUIRED_FA490_SOURCE_SHA256)
    req("FA490_FIRST_ERROR_LINE", REQUIRED_FA490_FIRST_ERROR_LINE)
    req("FA490_FIRST_ERROR_COL", REQUIRED_FA490_FIRST_ERROR_COL)
    req("FA490_FRONTIER_DECLARATION", REQUIRED_FA490_FRONTIER_DECLARATION)
    req("FA490_FRONTIER_INDEX", REQUIRED_FA490_FRONTIER_INDEX)
    variant = os.environ.get("FA491_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA491_VARIANT={variant!r}")
    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target(text, replacements)
    return text, repairs + [
        {"declaration": TARGET_DECLARATION, "declaration_index": TARGET_DECLARATION_INDEX,
         "strategy": strategy, "matrix_variant": variant,
         "required_fa490_evidence_run_id": int(REQUIRED_FA490_EVIDENCE_RUN_ID),
         "required_fa490_evidence_job_id": int(REQUIRED_FA490_EVIDENCE_JOB_ID),
         "required_fa490_evidence_head_sha": REQUIRED_FA490_EVIDENCE_HEAD_SHA,
         "required_fa490_source_sha256": REQUIRED_FA490_SOURCE_SHA256,
         "required_fa490_first_error_line": int(REQUIRED_FA490_FIRST_ERROR_LINE),
         "required_fa490_first_error_col": int(REQUIRED_FA490_FIRST_ERROR_COL),
         "frontier_declaration_index": TARGET_DECLARATION_INDEX, "later_repair_count": 0,
         "max_errors": 32, **audit},
        {"declaration": "FA491 strict-frontier repair", "strategy": variant,
         "target_declaration": TARGET_DECLARATION, "target_declaration_index": TARGET_DECLARATION_INDEX,
         "later_repair_count": 0},
    ]

fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
