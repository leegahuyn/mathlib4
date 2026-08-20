#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path


ROOT = Path.cwd()
BASE = ROOT / "scripts/fa477_prepare_log_cusp.py"
spec = importlib.util.spec_from_file_location("fa477base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa477 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa477
spec.loader.exec_module(fa477)

fa466 = fa477.fa466
orig_norm_repairs = fa477.norm_repairs


EXACT_FA477_VARIANT = "upper_ext_h_simp_only"
REQUIRED_UPSTREAM_EVIDENCE_RUN_ID = "31409787172"
REQUIRED_UPSTREAM_EVIDENCE_JOB_ID = "93524786715"
REQUIRED_UPSTREAM_EVIDENCE_HEAD_SHA = (
    "faf902ceda7cce10ada4399326330effaa4d669b"
)
REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_ID = "9071387258"
REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_NAME = (
    "codex-fa477-minimal_simpa-run31407777360-artifact9070636218-"
    "upper_ext_h_simp_only"
)
REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_SIZE = "598253"
REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_DIGEST = (
    "sha256:25928120f3113f98886a469b255eec59754bfd232b4df621f4efa4e1e9940b81"
)
TARGET_DECLARATION = "normSq_selectedLogHeightNaturalGauge_at_log_cuspLevel"
TARGET_DECLARATION_INDEX = 2794
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = (
    "1436e87661def2f8a70bd5c864bbe1a037474ba7df9e6d6222294c507394bcab"
)
EXPECTED_CANDIDATE_SHA256 = (
    "53a703d3e138ae7a964b7221c52337082cb59820595cfce877a679f024fbcf82"
)
EXPECTED_INTERMEDIATE_SOURCE_BYTES = 2697522
EXPECTED_CANDIDATE_BYTES = 2697540
EXPECTED_LINE_COUNT = 60535
EXPECTED_TARGET_HEADER_SHA256 = (
    "ca370d3eebc84e0c68aca1f5735d16c9b921231e9b3a82cf55839ef832963d3d"
)
EXPECTED_TARGET_REGION_SHA256 = (
    "a4a91f5b08c19c072ee127db8b0573d581092f31c22d1205a720c043bac8b603"
)
EXPECTED_TARGET_REGION_AFTER_SHA256 = (
    "0d7f2f8366e3db85daa9982689ddbb813e7ff944eb3344a8d88d07d42c3e6116"
)
EXPECTED_SOURCE_PREFIX_SHA256 = (
    "35323e90717342d1ed3f3958c9f2849163da1c374e1dbf47958df756f321b709"
)
EXPECTED_SOURCE_PREFIX_BYTES = 1502683
EXPECTED_SOURCE_SUFFIX_SHA256 = (
    "b5df15ad10dc149bcf63d387fc0d30509285c0d60f5f994072dc5ae6ae12c6b5"
)
EXPECTED_SOURCE_SUFFIX_BYTES = 1194070
EXPECTED_DECLARATION_SEQUENCE_SHA256 = (
    "c997317cd459891eea590671da4aa9941e5c083cbd5dffe91ee96601b12cc4f2"
)

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_NORM_REWRITE = """  rw [norm_mul, Complex.norm_real,
    abs_of_pos (Real.exp_pos _), mul_pow, hExp]"""

NEW_NORM_REWRITE = """  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, hExp]"""

VARIANTS = {
    "real_norm_eq_abs_only": (
        ((OLD_NORM_REWRITE, NEW_NORM_REWRITE),),
        (
            "insert Real.norm_eq_abs immediately after Complex.norm_real in "
            "the declaration-2794 norm/absolute-value rewrite"
        ),
    ),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def declaration_bounds(text: str, declaration: str) -> tuple[int, int]:
    starts = list(_DECL_START.finditer(text))
    hits = [
        index
        for index, match in enumerate(starts)
        if match.group("name") == declaration
    ]
    if len(hits) != 1:
        raise RuntimeError(
            f"expected exactly one declaration {declaration!r}, found {len(hits)}"
        )
    index = hits[0]
    start = starts[index].start()
    end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
    return start, end


def declaration_header(region: str) -> str:
    marker = region.find(":=")
    if marker < 0:
        raise RuntimeError(f"{TARGET_DECLARATION}: declaration header has no :=")
    return region[: marker + 2]


def replace_target_only(
    text: str, replacements: tuple[tuple[str, str], ...]
) -> tuple[str, dict[str, object]]:
    intermediate_sha256 = sha256_text(text)
    if intermediate_sha256 != EXPECTED_INTERMEDIATE_SOURCE_SHA256:
        raise RuntimeError(
            "FA478 requires the exact authoritative FA477 candidate source; got "
            f"{intermediate_sha256}, expected {EXPECTED_INTERMEDIATE_SOURCE_SHA256}"
        )
    intermediate_bytes = len(text.encode("utf-8"))
    if intermediate_bytes != EXPECTED_INTERMEDIATE_SOURCE_BYTES:
        raise RuntimeError(
            "FA478 intermediate byte-count drift: "
            f"{intermediate_bytes} != {EXPECTED_INTERMEDIATE_SOURCE_BYTES}"
        )
    line_count = len(text.splitlines())
    if line_count != EXPECTED_LINE_COUNT:
        raise RuntimeError(
            f"FA478 line-count drift: {line_count} != {EXPECTED_LINE_COUNT}"
        )

    start, end = declaration_bounds(text, TARGET_DECLARATION)
    next_doc = text.rfind("\n/--", start, end)
    if next_doc < start:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: expected the next declaration doc comment"
        )
    logical_end = next_doc + 1
    prefix = text[:start]
    original_region = text[start:logical_end]
    suffix = text[logical_end:]
    original_header = declaration_header(original_region)
    observed_guard = {
        "target_header_sha256": sha256_text(original_header),
        "target_region_sha256": sha256_text(original_region),
        "source_prefix_sha256": sha256_text(prefix),
        "source_prefix_bytes": len(prefix.encode("utf-8")),
        "source_suffix_sha256": sha256_text(suffix),
        "source_suffix_bytes": len(suffix.encode("utf-8")),
    }
    expected_guard = {
        "target_header_sha256": EXPECTED_TARGET_HEADER_SHA256,
        "target_region_sha256": EXPECTED_TARGET_REGION_SHA256,
        "source_prefix_sha256": EXPECTED_SOURCE_PREFIX_SHA256,
        "source_prefix_bytes": EXPECTED_SOURCE_PREFIX_BYTES,
        "source_suffix_sha256": EXPECTED_SOURCE_SUFFIX_SHA256,
        "source_suffix_bytes": EXPECTED_SOURCE_SUFFIX_BYTES,
    }
    if observed_guard != expected_guard:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: exact target/suffix guard mismatch: "
            f"{observed_guard!r} != {expected_guard!r}"
        )

    region = original_region
    replacement_audit = []
    for old, new in replacements:
        old_count_in_target = region.count(old)
        old_count_global = text.count(old)
        new_count_before = region.count(new)
        new_count_global_before = text.count(new)
        if (
            old_count_in_target != 1
            or old_count_global != 1
            or new_count_before != 0
            or new_count_global_before != 0
        ):
            raise RuntimeError(
                f"{TARGET_DECLARATION}: expected target/global old/new counts "
                "1/1/0/0, got "
                f"{old_count_in_target}/{old_count_global}/"
                f"{new_count_before}/{new_count_global_before}"
            )
        region = region.replace(old, new, 1)
        replacement_audit.append(
            {
                "old_count_before": old_count_in_target,
                "old_global_count_before": old_count_global,
                "new_count_before": new_count_before,
                "new_global_count_before": new_count_global_before,
                "old_sha256": sha256_text(old),
                "new_sha256": sha256_text(new),
                "old_bytes": len(old.encode("utf-8")),
                "new_bytes": len(new.encode("utf-8")),
            }
        )

    if sha256_text(region) != EXPECTED_TARGET_REGION_AFTER_SHA256:
        raise RuntimeError(f"{TARGET_DECLARATION}: edited target-region hash drift")
    candidate = prefix + region + suffix
    candidate_end = start + len(region)
    candidate_header = declaration_header(region)
    prefix_preserved = candidate[:start] == prefix
    suffix_preserved = candidate[candidate_end:] == suffix
    header_preserved = candidate_header == original_header
    if not prefix_preserved or not suffix_preserved or not header_preserved:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: prefix, suffix, or declaration header drift"
        )

    before_sequence = [match.group("name") for match in _DECL_START.finditer(text)]
    after_sequence = [
        match.group("name") for match in _DECL_START.finditer(candidate)
    ]
    declaration_sequence_preserved = before_sequence == after_sequence
    if not declaration_sequence_preserved:
        raise RuntimeError(f"{TARGET_DECLARATION}: declaration sequence drift")
    declaration_sequence_sha256 = sha256_text("\n".join(before_sequence))
    if declaration_sequence_sha256 != EXPECTED_DECLARATION_SEQUENCE_SHA256:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: declaration sequence hash drift"
        )
    candidate_sha256 = sha256_text(candidate)
    if candidate_sha256 != EXPECTED_CANDIDATE_SHA256:
        raise RuntimeError(
            f"FA478 candidate hash drift: {candidate_sha256} != "
            f"{EXPECTED_CANDIDATE_SHA256}"
        )
    candidate_bytes = len(candidate.encode("utf-8"))
    if candidate_bytes != EXPECTED_CANDIDATE_BYTES:
        raise RuntimeError(
            f"FA478 candidate byte-count drift: {candidate_bytes} != "
            f"{EXPECTED_CANDIDATE_BYTES}"
        )
    if len(candidate.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError("FA478 candidate line-count drift after replacement")

    return candidate, {
        "fa477_intermediate_source_sha256": intermediate_sha256,
        "fa477_intermediate_source_bytes": intermediate_bytes,
        "candidate_source_sha256": candidate_sha256,
        "candidate_source_bytes": candidate_bytes,
        "required_line_count": EXPECTED_LINE_COUNT,
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
        "declaration_sequence_sha256": declaration_sequence_sha256,
        "declaration_sequence_preserved": declaration_sequence_preserved,
        "replacement_audit": replacement_audit,
    }


def norm_repairs(text: str):
    fa477_variant = os.environ.get("FA477_VARIANT")
    if fa477_variant != EXACT_FA477_VARIANT:
        raise RuntimeError(
            "FA478 requires FA477_VARIANT=upper_ext_h_simp_only, got "
            f"{fa477_variant!r}"
        )
    upstream_run_id = os.environ.get("FA477_EVIDENCE_RUN_ID")
    if upstream_run_id != REQUIRED_UPSTREAM_EVIDENCE_RUN_ID:
        raise RuntimeError(
            "FA478 requires authoritative FA477 closure evidence from run "
            f"{REQUIRED_UPSTREAM_EVIDENCE_RUN_ID}, got {upstream_run_id!r}"
        )
    upstream_job_id = os.environ.get("FA477_EVIDENCE_JOB_ID")
    if upstream_job_id != REQUIRED_UPSTREAM_EVIDENCE_JOB_ID:
        raise RuntimeError(
            "FA478 requires exact FA477 evidence job "
            f"{REQUIRED_UPSTREAM_EVIDENCE_JOB_ID}, got {upstream_job_id!r}"
        )
    upstream_head_sha = os.environ.get("FA477_EVIDENCE_HEAD_SHA")
    if upstream_head_sha != REQUIRED_UPSTREAM_EVIDENCE_HEAD_SHA:
        raise RuntimeError(
            "FA478 requires exact FA477 evidence head "
            f"{REQUIRED_UPSTREAM_EVIDENCE_HEAD_SHA}, got {upstream_head_sha!r}"
        )
    upstream_artifact_id = os.environ.get("FA477_EVIDENCE_ARTIFACT_ID")
    upstream_artifact_name = os.environ.get("FA477_EVIDENCE_ARTIFACT_NAME")
    upstream_artifact_size = os.environ.get("FA477_EVIDENCE_ARTIFACT_SIZE")
    upstream_artifact_digest = os.environ.get("FA477_EVIDENCE_ARTIFACT_DIGEST")
    if upstream_artifact_id != REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_ID:
        raise RuntimeError(
            "FA478 requires the exact post-run FA477 artifact ID, got "
            f"{upstream_artifact_id!r}"
        )
    if upstream_artifact_name != REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_NAME:
        raise RuntimeError(
            "FA478 requires the exact FA477 artifact name, got "
            f"{upstream_artifact_name!r}"
        )
    if upstream_artifact_size != REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_SIZE:
        raise RuntimeError(
            "FA478 requires the exact FA477 artifact size, got "
            f"{upstream_artifact_size!r}"
        )
    if upstream_artifact_digest != REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_DIGEST:
        raise RuntimeError(
            "FA478 requires the exact post-run FA477 artifact digest, got "
            f"{upstream_artifact_digest!r}"
        )
    variant = os.environ.get("FA478_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported or missing FA478_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target_only(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "fa477_variant": fa477_variant,
            "required_upstream_evidence_run_id": int(upstream_run_id),
            "required_upstream_evidence_job_id": int(upstream_job_id),
            "required_upstream_evidence_head_sha": upstream_head_sha,
            "required_upstream_evidence_artifact_id": int(upstream_artifact_id),
            "required_upstream_evidence_artifact_name": upstream_artifact_name,
            "required_upstream_evidence_artifact_size": int(upstream_artifact_size),
            "required_upstream_evidence_artifact_digest": (
                upstream_artifact_digest
            ),
            "upstream_idx2793_closure_must_precede": True,
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA478 strict-frontier matrix",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "fa477_variant": fa477_variant,
            "required_upstream_evidence_run_id": int(upstream_run_id),
            "required_upstream_evidence_job_id": int(upstream_job_id),
            "required_upstream_evidence_head_sha": upstream_head_sha,
            "required_upstream_evidence_artifact_id": int(upstream_artifact_id),
            "required_upstream_evidence_artifact_name": upstream_artifact_name,
            "required_upstream_evidence_artifact_size": int(upstream_artifact_size),
            "required_upstream_evidence_artifact_digest": (
                upstream_artifact_digest
            ),
            "upstream_idx2793_closure_must_precede": True,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
