#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa507_prepare_frontier_2840_2888_cumulative.py"
REQUIRED_BASE_SHA256 = (
    "d824501a7428c72b64153d1ccb090edf5b6ff413c582c13644121f4308d4234e"
)
base_payload = BASE.read_bytes()
base_sha256 = hashlib.sha256(base_payload).hexdigest()
if base_sha256 != REQUIRED_BASE_SHA256:
    raise RuntimeError(
        f"FA506-r2 locked FA507 helper drift: {base_sha256}; "
        f"expected {REQUIRED_BASE_SHA256}"
    )
spec = importlib.util.spec_from_file_location("fa507fragmentbase", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa507 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa507
spec.loader.exec_module(fa507)

fa466 = fa507.fa466
orig_norm_repairs = fa507.orig_norm_repairs

EXACT_FA506_VARIANT = "explicit_upper_half_plane_coe_projections"
VARIANTS = {
    "membership_only": {
        "sha256": "59bc2a484f508d23f03c9d92920b3746f62754e35a814cc4d3eec7be3ed12088",
        "bytes": 2_700_282,
        "lines": 60_541,
        "indices": [2_839],
    },
    "membership_plus_frontier_batch": {
        "sha256": "d0a3decee1c0a7a781d14fdf122e235d71d8f210bb65a894dc4e518821bf03ec",
        "bytes": 2_702_252,
        "lines": 60_573,
        "indices": [
            2_839,
            2_840,
            2_847,
            2_849,
            2_856,
            2_866,
            2_867,
            2_868,
            2_869,
            2_870,
            2_873,
            2_883,
            2_888,
        ],
    },
}

FA505_SOURCE_SHA256 = (
    "c56e320e31dbb4c2d80a7b6c05e3417b9683fe982a9f006bbd6166add95ea9e7"
)
FA505_SOURCE_BYTES = 2_700_162
FA505_SOURCE_LINES = 60_539
FA506_SOURCE_SHA256 = (
    "fbf76ffa75885c76492c6795ac907d47693d964d30043fd8cced93ca71719611"
)
FA506_SOURCE_BYTES = 2_700_268
FA506_SOURCE_LINES = 60_541
EXPECTED_DECLARATION_COUNT = 4_397

PREVIOUS_FRONTIER = "integral_selectedHeightGraphDensity_stripTail_eq_iterated"
PREVIOUS_FRONTIER_INDEX = 2_835
FIRST_ERROR = "complex_image_heightStrip_eq_coe_image_selectedBaseCuspStrip"
FIRST_ERROR_INDEX = 2_839
TARGET_DECLARATION = FIRST_ERROR
TARGET_INDEX = FIRST_ERROR_INDEX

OLD_MEMBERSHIP = """    simpa only [z, Complex.measurableEquivRealProd_symm_apply,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hp"""
NEW_MEMBERSHIP = """    simpa only [Set.mem_prod, z, Complex.measurableEquivRealProd_symm_apply,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hp"""


def require_live_attestation(
    evidence: dict[str, dict[str, object]],
) -> dict[str, object]:
    fa507.require_env(
        "FA506R2_UPSTREAM_ATTESTATION_PATH",
        "/tmp/fa506r2-upstream-attestation.json",
    )
    path = Path("/tmp/fa506r2-upstream-attestation.json")
    if not path.is_file():
        raise RuntimeError(f"FA506-r2 live attestation is missing: {path}")
    expected_sha = fa507.require_sha("FA506R2_UPSTREAM_ATTESTATION_SHA256", 64)
    data = path.read_bytes()
    actual_sha = fa507.sha256_bytes(data)
    if actual_sha != expected_sha:
        raise RuntimeError(
            f"FA506-r2 attestation SHA mismatch: {actual_sha}; "
            f"expected {expected_sha}"
        )
    payload = json.loads(data)
    if payload.get("schema") != "fa506r2-upstream-evidence-v1":
        raise RuntimeError("FA506-r2 attestation schema mismatch")
    if payload.get("all_checks_passed") is not True:
        raise RuntimeError("FA506-r2 attestation checks did not all pass")
    for prefix in ("FA505", "FA506"):
        item = payload.get(prefix.lower(), {})
        required = evidence[prefix]
        for field in ("run_id", "job_id", "head_sha", "artifact_id"):
            if item.get(field) != required[field]:
                raise RuntimeError(
                    f"FA506-r2 attestation {prefix.lower()}.{field} mismatch"
                )
        if item.get("all_checks_passed") is not True:
            raise RuntimeError(f"FA506-r2 {prefix} live checks did not all pass")
    return {
        "path": str(path),
        "sha256": actual_sha,
        "schema": payload["schema"],
        "all_checks_passed": True,
    }


def declaration_regions(text: str) -> tuple[list[str], list[str]]:
    starts = fa507.declarations(text)
    names = [match.group("name") for match in starts]
    regions = [
        text[match.start() : starts[i + 1].start() if i + 1 < len(starts) else len(text)]
        for i, match in enumerate(starts)
    ]
    return names, regions


def apply_variant(text: str, variant: str) -> tuple[str, dict[str, object]]:
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA506R2_VARIANT={variant!r}")
    source_sha = fa507.sha256_text(text)
    source_bytes = len(text.encode("utf-8"))
    source_lines = len(text.splitlines())
    if (
        source_sha != FA506_SOURCE_SHA256
        or source_bytes != FA506_SOURCE_BYTES
        or source_lines != FA506_SOURCE_LINES
    ):
        raise RuntimeError(
            "FA506-r2 exact FA506 input mismatch: "
            f"sha={source_sha}, bytes={source_bytes}, lines={source_lines}"
        )

    before_names, before_regions = declaration_regions(text)
    if len(before_names) != EXPECTED_DECLARATION_COUNT:
        raise RuntimeError("FA506-r2 declaration-count drift")
    if before_names[TARGET_INDEX] != TARGET_DECLARATION:
        raise RuntimeError("FA506-r2 target declaration/index drift")

    abc_audit = None
    if variant == "membership_plus_frontier_batch":
        working, abc_audit = fa507.apply_cumulative_repairs(text)
    else:
        working = text

    start, end, actual_index = fa507.bounds(working, TARGET_DECLARATION)
    region = working[start:end]
    if actual_index != TARGET_INDEX:
        raise RuntimeError("FA506-r2 membership target index drift")
    if region.count(OLD_MEMBERSHIP) != 1 or region.count(NEW_MEMBERSHIP) != 0:
        raise RuntimeError("FA506-r2 membership fragment count drift")
    candidate = (
        working[:start]
        + region.replace(OLD_MEMBERSHIP, NEW_MEMBERSHIP, 1)
        + working[end:]
    )

    after_names, after_regions = declaration_regions(candidate)
    if before_names != after_names:
        raise RuntimeError("FA506-r2 declaration sequence drift")
    changed_indices = [
        i
        for i, (before, after) in enumerate(
            zip(before_regions, after_regions, strict=True)
        )
        if before != after
    ]
    expected_indices = VARIANTS[variant]["indices"]
    if changed_indices != expected_indices:
        raise RuntimeError(
            f"FA506-r2 changed indices {changed_indices}; expected {expected_indices}"
        )

    replacements: list[tuple[str, int, str, str]] = [
        (TARGET_DECLARATION, TARGET_INDEX, OLD_MEMBERSHIP, NEW_MEMBERSHIP)
    ]
    if variant == "membership_plus_frontier_batch":
        replacements.extend(
            (declaration, fa507.TARGET_INDEX[declaration], old, new)
            for declaration, _group, old, new in fa507.REPLACEMENTS
        )

    before_skeleton_regions = list(before_regions)
    after_skeleton_regions = list(after_regions)
    header_audit: dict[str, dict[str, object]] = {}
    replacement_audit: list[dict[str, object]] = []
    for number, (declaration, index, old, new) in enumerate(replacements):
        if before_names[index] != declaration:
            raise RuntimeError(f"FA506-r2 replacement index drift: {declaration}")
        before_region = before_skeleton_regions[index]
        after_region = after_skeleton_regions[index]
        if before_region.count(old) != 1 or after_region.count(new) != 1:
            raise RuntimeError(f"FA506-r2 skeleton fragment drift: {declaration}")
        before_header = fa507.header(before_regions[index])
        after_header = fa507.header(after_regions[index])
        if before_header != after_header:
            raise RuntimeError(f"FA506-r2 header drift: {declaration}")
        marker = f"\x00FA506R2_REPLACEMENT_{number:02d}\x00"
        before_skeleton_regions[index] = before_region.replace(old, marker, 1)
        after_skeleton_regions[index] = after_region.replace(new, marker, 1)
        header_audit[declaration] = {
            "index": index,
            "sha256": fa507.sha256_text(before_header),
            "preserved": True,
        }
        replacement_audit.append(
            {
                "declaration": declaration,
                "index": index,
                "old_sha256": fa507.sha256_text(old),
                "new_sha256": fa507.sha256_text(new),
                "mode": "checked_fragment",
            }
        )
    before_skeleton = "".join(before_skeleton_regions)
    after_skeleton = "".join(after_skeleton_regions)
    if before_skeleton != after_skeleton:
        raise RuntimeError("FA506-r2 immutable source skeleton drift")

    before_forbidden = fa507.forbidden_counts(text)
    after_forbidden = fa507.forbidden_counts(candidate)
    before_executable = fa507.executable_forbidden_counts(text)
    after_executable = fa507.executable_forbidden_counts(candidate)
    if before_forbidden != after_forbidden or before_executable != after_executable:
        raise RuntimeError("FA506-r2 forbidden-token drift")
    if any(before_executable.values()):
        raise RuntimeError(
            f"FA506-r2 executable forbidden code is not clean: {before_executable}"
        )

    earliest_old = replacements[0][2]
    latest_old = replacements[-1][2]
    earliest_new = replacements[0][3]
    latest_new = replacements[-1][3]
    prefix = text[: text.find(earliest_old)]
    suffix = text[text.find(latest_old) + len(latest_old) :]
    if candidate[: candidate.find(earliest_new)] != prefix:
        raise RuntimeError("FA506-r2 prefix drift")
    if candidate[candidate.find(latest_new) + len(latest_new) :] != suffix:
        raise RuntimeError("FA506-r2 suffix drift")

    expected = VARIANTS[variant]
    candidate_sha = fa507.sha256_text(candidate)
    candidate_bytes = len(candidate.encode("utf-8"))
    candidate_lines = len(candidate.splitlines())
    if (
        candidate_sha != expected["sha256"]
        or candidate_bytes != expected["bytes"]
        or candidate_lines != expected["lines"]
    ):
        raise RuntimeError(
            "FA506-r2 candidate identity drift: "
            f"sha={candidate_sha}, bytes={candidate_bytes}, lines={candidate_lines}"
        )

    return candidate, {
        "variant": variant,
        "input_source_sha256": source_sha,
        "input_source_bytes": source_bytes,
        "input_source_lines": source_lines,
        "candidate_source_sha256": candidate_sha,
        "candidate_source_bytes": candidate_bytes,
        "candidate_source_lines": candidate_lines,
        "declaration_count": len(before_names),
        "declaration_sequence_sha256": fa507.sha256_text("\n".join(before_names)),
        "declaration_sequence_preserved": True,
        "changed_indices": changed_indices,
        "changed_declarations": [before_names[i] for i in changed_indices],
        "replacement_audit": replacement_audit,
        "target_headers": header_audit,
        "headers_and_claims_preserved": True,
        "immutable_source_skeleton_sha256": fa507.sha256_text(before_skeleton),
        "immutable_source_skeleton_bytes": len(before_skeleton.encode("utf-8")),
        "immutable_source_skeleton_preserved": True,
        "documentation_comments_preserved": True,
        "attributes_preserved": True,
        "source_prefix_sha256": fa507.sha256_text(prefix),
        "source_prefix_bytes": len(prefix.encode("utf-8")),
        "source_prefix_preserved": True,
        "source_suffix_sha256": fa507.sha256_text(suffix),
        "source_suffix_bytes": len(suffix.encode("utf-8")),
        "source_suffix_preserved": True,
        "lexical_forbidden_counts_before": before_forbidden,
        "lexical_forbidden_counts_after": after_forbidden,
        "executable_forbidden_counts_before": before_executable,
        "executable_forbidden_counts_after": after_executable,
        "executable_forbidden_six_zero": True,
        "fa507_fragment_batch_audit": abc_audit,
    }


def norm_repairs(text: str):
    fa507.require_env("FA506_VARIANT", EXACT_FA506_VARIANT)
    variant = os.environ.get("FA506R2_VARIANT", "")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported FA506R2_VARIANT={variant!r}")
    expected = VARIANTS[variant]
    fa507.require_env("FA506R2_EXPECTED_SHA256", str(expected["sha256"]))
    fa507.require_env("FA506R2_EXPECTED_BYTES", str(expected["bytes"]))
    fa507.require_env("FA506R2_EXPECTED_LINES", str(expected["lines"]))

    evidence = {
        "FA505": fa507.require_direct_evidence(
            "FA505",
            FA505_SOURCE_SHA256,
            FA505_SOURCE_BYTES,
            FA505_SOURCE_LINES,
            PREVIOUS_FRONTIER,
            PREVIOUS_FRONTIER_INDEX,
            FIRST_ERROR,
            FIRST_ERROR_INDEX,
        ),
        "FA506": fa507.require_direct_evidence(
            "FA506",
            FA506_SOURCE_SHA256,
            FA506_SOURCE_BYTES,
            FA506_SOURCE_LINES,
            PREVIOUS_FRONTIER,
            PREVIOUS_FRONTIER_INDEX,
            FIRST_ERROR,
            FIRST_ERROR_INDEX,
        ),
    }
    attestation = require_live_attestation(evidence)
    text, repairs = orig_norm_repairs(text)
    candidate, audit = apply_variant(text, variant)
    return candidate, repairs + [
        {
            "declaration": "FA506-r2 forward membership matrix",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_INDEX,
            "required_fa505_evidence": evidence["FA505"],
            "required_fa506_evidence": evidence["FA506"],
            "live_attestation": attestation,
            "max_errors": 32,
            **audit,
        }
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
