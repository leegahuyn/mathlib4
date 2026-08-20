#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa504_prepare_joint_basepoint_source_membership.py"
spec = importlib.util.spec_from_file_location("fa504base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa504 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa504
spec.loader.exec_module(fa504)

fa466 = fa504.fa466
orig_norm_repairs = fa504.norm_repairs

EXACT_FA504_VARIANT = "explicit_range_witness"
REQUIRED_FA504_EVIDENCE_RUN_ID = "31476200843"
REQUIRED_FA504_EVIDENCE_JOB_ID = "93730366964"
REQUIRED_FA504_EVIDENCE_HEAD_SHA = "abb10a69c70e9077f17ca7aa9f27f3ca63f31070"
REQUIRED_FA504_SOURCE_SHA256 = "57d05b04902887e305dcc34c4193a72747540292ee690a087ee958d771203c18"
REQUIRED_FA504_SOURCE_BYTES = 2700129
REQUIRED_FA504_SOURCE_LINES = 60538
REQUIRED_FA504_FIRST_ERROR_LINE = "36042"
REQUIRED_FA504_FIRST_ERROR_COL = "2"
REQUIRED_FA504_FRONTIER_DECLARATION = (
    "integral_selectedHeightGraphDensity_stripTail_eq_iterated"
)
REQUIRED_FA504_FRONTIER_INDEX = "2835"

TARGET_DECLARATION = REQUIRED_FA504_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2835
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA504_SOURCE_SHA256
EXPECTED_CANDIDATE_SHA256 = (
    "c56e320e31dbb4c2d80a7b6c05e3417b9683fe982a9f006bbd6166add95ea9e7"
)
EXPECTED_CANDIDATE_BYTES = 2700162
EXPECTED_CANDIDATE_LINES = 60539

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_FRAGMENT = """  change (∫ p, selectedHeightGraphDensity n q u p ∂μ.prod ν) =
    ∫ t, ∫ y, selectedHeightGraphDensity n q u (t, y) ∂ν ∂μ
  exact integral_prod _ hProd
"""

NEW_FRAGMENT = """  rw [← Measure.prod_restrict]
  change (∫ p, selectedHeightGraphDensity n q u p ∂μ.prod ν) =
    ∫ t, ∫ y, selectedHeightGraphDensity n q u (t, y) ∂ν ∂μ
  exact integral_prod _ hProd
"""

_FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "new_global_axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def bounds(text: str, declaration: str) -> tuple[int, int]:
    starts = list(_DECL_START.finditer(text))
    hits = [i for i, match in enumerate(starts) if match.group("name") == declaration]
    if len(hits) != 1:
        raise RuntimeError(f"expected one {declaration}, found {len(hits)}")
    i = hits[0]
    end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
    return starts[i].start(), end


def header(region: str) -> str:
    marker = region.find(":=")
    if marker < 0:
        raise RuntimeError("target header has no :=")
    return region[: marker + 2]


def forbidden_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in _FORBIDDEN.items()}


def require_env(name: str, expected: str) -> None:
    actual = os.environ.get(name)
    if actual != expected:
        raise RuntimeError(f"FA505 requires {name}={expected}, got {actual!r}")


def replace_target(text: str) -> tuple[str, dict[str, object]]:
    source_sha = sha256_text(text)
    source_bytes = len(text.encode("utf-8"))
    source_lines = len(text.splitlines())
    if source_sha != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(
            f"FA505 exact FA504 source mismatch: {source_sha}; "
            f"expected {EXPECTED_INTERMEDIATE_SOURCE_SHA256}"
        )
    if source_bytes != REQUIRED_FA504_SOURCE_BYTES:
        raise RuntimeError(
            f"FA505 FA504 source byte drift: {source_bytes}; "
            f"expected {REQUIRED_FA504_SOURCE_BYTES}"
        )
    if source_lines != REQUIRED_FA504_SOURCE_LINES:
        raise RuntimeError(
            f"FA505 FA504 source line drift: {source_lines}; "
            f"expected {REQUIRED_FA504_SOURCE_LINES}"
        )

    start, end = bounds(text, TARGET_DECLARATION)
    prefix, region, suffix = text[:start], text[start:end], text[end:]
    old_header = header(region)
    old_target_count = region.count(OLD_FRAGMENT)
    old_global_count = text.count(OLD_FRAGMENT)
    new_target_count = region.count(NEW_FRAGMENT)
    new_global_count = text.count(NEW_FRAGMENT)
    if (old_target_count, old_global_count, new_target_count, new_global_count) != (
        1,
        1,
        0,
        0,
    ):
        raise RuntimeError(
            "FA505 old/new fragment counts were "
            f"target/global={old_target_count}/{old_global_count}/"
            f"{new_target_count}/{new_global_count}, expected 1/1/0/0"
        )

    new_region = region.replace(OLD_FRAGMENT, NEW_FRAGMENT, 1)
    candidate = prefix + new_region + suffix
    if header(new_region) != old_header:
        raise RuntimeError("FA505 theorem header drift")
    before_sequence = [match.group("name") for match in _DECL_START.finditer(text)]
    after_sequence = [match.group("name") for match in _DECL_START.finditer(candidate)]
    if before_sequence != after_sequence:
        raise RuntimeError("FA505 declaration sequence drift")
    if candidate[:start] != prefix:
        raise RuntimeError("FA505 source prefix drift")
    if candidate[start + len(new_region) :] != suffix:
        raise RuntimeError("FA505 source suffix drift")
    before_forbidden = forbidden_counts(text)
    after_forbidden = forbidden_counts(candidate)
    if before_forbidden != after_forbidden:
        raise RuntimeError(
            f"FA505 forbidden-token count drift: {before_forbidden} -> {after_forbidden}"
        )

    candidate_sha = sha256_text(candidate)
    candidate_bytes = len(candidate.encode("utf-8"))
    candidate_lines = len(candidate.splitlines())
    if candidate_sha != EXPECTED_CANDIDATE_SHA256:
        raise RuntimeError(
            f"FA505 candidate SHA drift: {candidate_sha}; "
            f"expected {EXPECTED_CANDIDATE_SHA256}"
        )
    if candidate_bytes != EXPECTED_CANDIDATE_BYTES:
        raise RuntimeError(
            f"FA505 candidate byte drift: {candidate_bytes}; "
            f"expected {EXPECTED_CANDIDATE_BYTES}"
        )
    if candidate_lines != EXPECTED_CANDIDATE_LINES:
        raise RuntimeError(
            f"FA505 candidate line drift: {candidate_lines}; "
            f"expected {EXPECTED_CANDIDATE_LINES}"
        )

    audit: dict[str, object] = {
        "fa504_intermediate_source_sha256": source_sha,
        "fa504_intermediate_source_bytes": source_bytes,
        "fa504_intermediate_source_lines": source_lines,
        "candidate_source_sha256": candidate_sha,
        "candidate_source_bytes": candidate_bytes,
        "candidate_line_count": candidate_lines,
        "replacement_count": 1,
        "old_fragment_sha256": sha256_text(OLD_FRAGMENT),
        "new_fragment_sha256": sha256_text(NEW_FRAGMENT),
        "old_global_count_before": old_global_count,
        "new_global_count_before": new_global_count,
        "target_header_sha256": sha256_text(old_header),
        "target_header_preserved": True,
        "source_prefix_sha256": sha256_text(prefix),
        "source_prefix_bytes": len(prefix.encode("utf-8")),
        "source_prefix_preserved": True,
        "source_suffix_sha256": sha256_text(suffix),
        "source_suffix_bytes": len(suffix.encode("utf-8")),
        "source_suffix_preserved": True,
        "target_region_before_sha256": sha256_text(region),
        "target_region_after_sha256": sha256_text(new_region),
        "declaration_sequence_sha256": sha256_text("\n".join(before_sequence)),
        "declaration_sequence_preserved": True,
        "forbidden_counts_before": before_forbidden,
        "forbidden_counts_after": after_forbidden,
        "forbidden_not_increased": True,
        "claims_preserved": True,
    }
    return candidate, audit


def norm_repairs(text: str):
    for name, expected in [
        ("FA504_VARIANT", EXACT_FA504_VARIANT),
        ("FA504_EVIDENCE_RUN_ID", REQUIRED_FA504_EVIDENCE_RUN_ID),
        ("FA504_EVIDENCE_JOB_ID", REQUIRED_FA504_EVIDENCE_JOB_ID),
        ("FA504_EVIDENCE_HEAD_SHA", REQUIRED_FA504_EVIDENCE_HEAD_SHA),
        ("FA504_EVIDENCE_SOURCE_SHA256", REQUIRED_FA504_SOURCE_SHA256),
        ("FA504_FIRST_ERROR_LINE", REQUIRED_FA504_FIRST_ERROR_LINE),
        ("FA504_FIRST_ERROR_COL", REQUIRED_FA504_FIRST_ERROR_COL),
        ("FA504_FRONTIER_DECLARATION", REQUIRED_FA504_FRONTIER_DECLARATION),
        ("FA504_FRONTIER_INDEX", REQUIRED_FA504_FRONTIER_INDEX),
    ]:
        require_env(name, expected)
    variant = os.environ.get("FA505_VARIANT")
    if variant != "reuse_verified_prod_restrict_rewrite":
        raise RuntimeError(f"unsupported FA505_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    candidate, audit = replace_target(text)
    return candidate, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": (
                "reuse the already direct-Lean-verified Fubini bridge from "
                "integral_selectedLogHeightEnergyDensity_stripTail_eq_iterated: "
                "rewrite the set-integral measure with ← Measure.prod_restrict, "
                "then apply integral_prod to hProd"
            ),
            "matrix_variant": variant,
            "required_fa504_evidence_run_id": int(REQUIRED_FA504_EVIDENCE_RUN_ID),
            "required_fa504_evidence_job_id": int(REQUIRED_FA504_EVIDENCE_JOB_ID),
            "required_fa504_evidence_head_sha": REQUIRED_FA504_EVIDENCE_HEAD_SHA,
            "required_fa504_source_sha256": REQUIRED_FA504_SOURCE_SHA256,
            "required_fa504_first_error_line": int(REQUIRED_FA504_FIRST_ERROR_LINE),
            "required_fa504_first_error_col": int(REQUIRED_FA504_FIRST_ERROR_COL),
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA505 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
