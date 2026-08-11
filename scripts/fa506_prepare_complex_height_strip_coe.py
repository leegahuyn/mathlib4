#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa505_prepare_height_graph_strip_fubini.py"
spec = importlib.util.spec_from_file_location("fa505base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa505 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa505
spec.loader.exec_module(fa505)

fa466 = fa505.fa466
orig_norm_repairs = fa505.norm_repairs

EXACT_FA505_VARIANT = "reuse_verified_prod_restrict_rewrite"
REQUIRED_FA505_SOURCE_SHA256 = (
    "c56e320e31dbb4c2d80a7b6c05e3417b9683fe982a9f006bbd6166add95ea9e7"
)
REQUIRED_FA505_SOURCE_BYTES = 2700162
REQUIRED_FA505_SOURCE_LINES = 60539
REQUIRED_FA505_PREVIOUS_FRONTIER_DECLARATION = (
    "integral_selectedHeightGraphDensity_stripTail_eq_iterated"
)
REQUIRED_FA505_PREVIOUS_FRONTIER_INDEX = "2835"
REQUIRED_FA505_FRONTIER_DECLARATION = (
    "complex_image_heightStrip_eq_coe_image_selectedBaseCuspStrip"
)
REQUIRED_FA505_FRONTIER_INDEX = "2839"

TARGET_DECLARATION = REQUIRED_FA505_FRONTIER_DECLARATION
TARGET_DECLARATION_INDEX = 2839
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = REQUIRED_FA505_SOURCE_SHA256
EXPECTED_CANDIDATE_SHA256 = (
    "fbf76ffa75885c76492c6795ac907d47693d964d30043fd8cced93ca71719611"
)
EXPECTED_CANDIDATE_BYTES = 2700268
EXPECTED_CANDIDATE_LINES = 60541

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_FORWARD = (
    "    simpa only [z, Complex.measurableEquivRealProd_symm_apply] using hp"
)
NEW_FORWARD = """    simpa only [z, Complex.measurableEquivRealProd_symm_apply,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hp"""

OLD_REVERSE = """    apply Complex.ext <;>
      simp only [Complex.measurableEquivRealProd_symm_apply]"""
NEW_REVERSE = """    apply Complex.ext <;>
      simp only [Complex.measurableEquivRealProd_symm_apply,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]"""

REPLACEMENTS = (
    ("forward_membership", OLD_FORWARD, NEW_FORWARD),
    ("reverse_complex_ext", OLD_REVERSE, NEW_REVERSE),
)

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
        raise RuntimeError(f"FA506 requires {name}={expected}, got {actual!r}")


def require_positive_decimal(name: str) -> int:
    actual = os.environ.get(name, "")
    if re.fullmatch(r"[1-9][0-9]*", actual) is None:
        raise RuntimeError(f"FA506 requires verified positive decimal {name}, got {actual!r}")
    return int(actual)


def require_sha(name: str) -> str:
    actual = os.environ.get(name, "")
    if (
        re.fullmatch(r"[0-9a-f]{40}", actual) is None
        or actual == "0" * 40
    ):
        raise RuntimeError(f"FA506 requires verified 40-hex {name}, got {actual!r}")
    return actual


def require_fa505_evidence() -> dict[str, object]:
    require_env("FA505_EVIDENCE_STATUS", "VERIFIED")
    run_id = require_positive_decimal("FA505_EVIDENCE_RUN_ID")
    job_id = require_positive_decimal("FA505_EVIDENCE_JOB_ID")
    head_sha = require_sha("FA505_EVIDENCE_HEAD_SHA")
    require_env("FA505_EVIDENCE_SOURCE_SHA256", REQUIRED_FA505_SOURCE_SHA256)
    require_env("FA505_CLASSIFICATION", "LEAN_FAILURE")
    require_env("FA505_INFRA_REASONS", "[]")
    require_env("FA505_MOCK2_EXIT", "0")
    require_env("FA505_MOCK2_ADVANCED_EXIT", "0")
    require_env("FA505_FA_EXIT", "1")
    require_env(
        "FA505_PREVIOUS_FRONTIER_DECLARATION",
        REQUIRED_FA505_PREVIOUS_FRONTIER_DECLARATION,
    )
    require_env(
        "FA505_PREVIOUS_FRONTIER_INDEX", REQUIRED_FA505_PREVIOUS_FRONTIER_INDEX
    )
    require_env("FA505_FIRST_ERROR_DECLARATION", REQUIRED_FA505_FRONTIER_DECLARATION)
    require_env("FA505_FIRST_ERROR_INDEX", REQUIRED_FA505_FRONTIER_INDEX)
    first_line = require_positive_decimal("FA505_FIRST_ERROR_LINE")
    first_col = require_positive_decimal("FA505_FIRST_ERROR_COL")
    if TARGET_DECLARATION_INDEX <= int(REQUIRED_FA505_PREVIOUS_FRONTIER_INDEX):
        raise RuntimeError("FA506 frontier did not advance beyond FA505 repaired index")
    return {
        "required_fa505_evidence_run_id": run_id,
        "required_fa505_evidence_job_id": job_id,
        "required_fa505_evidence_head_sha": head_sha,
        "required_fa505_source_sha256": REQUIRED_FA505_SOURCE_SHA256,
        "required_fa505_first_error_line": first_line,
        "required_fa505_first_error_col": first_col,
        "required_fa505_first_error_declaration": REQUIRED_FA505_FRONTIER_DECLARATION,
        "required_fa505_first_error_index": TARGET_DECLARATION_INDEX,
        "fa505_previous_frontier_closed": True,
    }


def replace_target(text: str) -> tuple[str, dict[str, object]]:
    source_sha = sha256_text(text)
    source_bytes = len(text.encode("utf-8"))
    source_lines = len(text.splitlines())
    if source_sha != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(
            f"FA506 exact FA505 source mismatch: {source_sha}; "
            f"expected {EXPECTED_INTERMEDIATE_SOURCE_SHA256}"
        )
    if source_bytes != REQUIRED_FA505_SOURCE_BYTES:
        raise RuntimeError(
            f"FA506 FA505 source byte drift: {source_bytes}; "
            f"expected {REQUIRED_FA505_SOURCE_BYTES}"
        )
    if source_lines != REQUIRED_FA505_SOURCE_LINES:
        raise RuntimeError(
            f"FA506 FA505 source line drift: {source_lines}; "
            f"expected {REQUIRED_FA505_SOURCE_LINES}"
        )

    start, end = bounds(text, TARGET_DECLARATION)
    prefix, region, suffix = text[:start], text[start:end], text[end:]
    old_header = header(region)
    replacement_audit = []
    new_region = region
    for label, old, new in REPLACEMENTS:
        old_target_count = new_region.count(old)
        old_global_count = text.count(old)
        new_target_count = new_region.count(new)
        new_global_count = text.count(new)
        if (old_target_count, old_global_count, new_target_count, new_global_count) != (
            1,
            1,
            0,
            0,
        ):
            raise RuntimeError(
                f"FA506 {label} old/new target/global counts were "
                f"{old_target_count}/{old_global_count}/"
                f"{new_target_count}/{new_global_count}, expected 1/1/0/0"
            )
        new_region = new_region.replace(old, new, 1)
        replacement_audit.append(
            {
                "label": label,
                "old_count_before": old_target_count,
                "old_global_count_before": old_global_count,
                "new_count_before": new_target_count,
                "new_global_count_before": new_global_count,
                "old_sha256": sha256_text(old),
                "new_sha256": sha256_text(new),
            }
        )

    candidate = prefix + new_region + suffix
    if header(new_region) != old_header:
        raise RuntimeError("FA506 theorem header drift")
    before_sequence = [match.group("name") for match in _DECL_START.finditer(text)]
    after_sequence = [match.group("name") for match in _DECL_START.finditer(candidate)]
    if before_sequence != after_sequence:
        raise RuntimeError("FA506 declaration sequence drift")
    if candidate[:start] != prefix:
        raise RuntimeError("FA506 source prefix drift")
    if candidate[start + len(new_region) :] != suffix:
        raise RuntimeError("FA506 source suffix drift")
    before_forbidden = forbidden_counts(text)
    after_forbidden = forbidden_counts(candidate)
    if before_forbidden != after_forbidden:
        raise RuntimeError(
            f"FA506 forbidden-token count drift: {before_forbidden} -> {after_forbidden}"
        )

    candidate_sha = sha256_text(candidate)
    candidate_bytes = len(candidate.encode("utf-8"))
    candidate_lines = len(candidate.splitlines())
    if candidate_sha != EXPECTED_CANDIDATE_SHA256:
        raise RuntimeError(
            f"FA506 candidate SHA drift: {candidate_sha}; "
            f"expected {EXPECTED_CANDIDATE_SHA256}"
        )
    if candidate_bytes != EXPECTED_CANDIDATE_BYTES:
        raise RuntimeError(
            f"FA506 candidate byte drift: {candidate_bytes}; "
            f"expected {EXPECTED_CANDIDATE_BYTES}"
        )
    if candidate_lines != EXPECTED_CANDIDATE_LINES:
        raise RuntimeError(
            f"FA506 candidate line drift: {candidate_lines}; "
            f"expected {EXPECTED_CANDIDATE_LINES}"
        )

    audit: dict[str, object] = {
        "fa505_intermediate_source_sha256": source_sha,
        "fa505_intermediate_source_bytes": source_bytes,
        "fa505_intermediate_source_lines": source_lines,
        "candidate_source_sha256": candidate_sha,
        "candidate_source_bytes": candidate_bytes,
        "candidate_line_count": candidate_lines,
        "replacement_count": len(REPLACEMENTS),
        "replacement_audit": replacement_audit,
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
    require_env("FA505_VARIANT", EXACT_FA505_VARIANT)
    evidence = require_fa505_evidence()
    variant = os.environ.get("FA506_VARIANT")
    if variant != "explicit_upper_half_plane_coe_projections":
        raise RuntimeError(f"unsupported FA506_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    candidate, audit = replace_target(text)
    return candidate, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": (
                "make both directions' subtype-coercion projections explicit by adding "
                "UpperHalfPlane.coe_re and UpperHalfPlane.coe_im to the local simp-only "
                "closures; preserve the image-set theorem and its witnesses"
            ),
            "matrix_variant": variant,
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **evidence,
            **audit,
        },
        {
            "declaration": "FA506 strict-frontier repair",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
