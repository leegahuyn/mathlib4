#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path


ROOT = Path.cwd()
BASE = ROOT / "scripts/fa476r3_prepare_logheight_norm.py"
spec = importlib.util.spec_from_file_location("fa476r3base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa476r3 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa476r3
spec.loader.exec_module(fa476r3)

fa466 = fa476r3.fa466
orig_norm_repairs = fa476r3.norm_repairs


EXACT_FA475_WINNER = "clean_semicolon"
EXACT_FA476_R2_VARIANT = "explicit_exp_nonneg"
EXACT_FA476_R3_VARIANT = "minimal_simpa"
REQUIRED_UPSTREAM_EVIDENCE_RUN_ID = "31407777360"
REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_ID = "9070636218"
REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_DIGEST = (
    "sha256:343607e51bea29fd2878bf6ebfcc0c1c8b1daf9826733b0cd3729e63fbbea3ca"
)
TARGET_DECLARATION = "selectedCosetUnitaryPullback_log_cuspLevel"
TARGET_DECLARATION_INDEX = 2793
EXPECTED_INTERMEDIATE_SOURCE_SHA256 = (
    "5d96377b3b4895f7f48a847105ae1f077677c794df6bc6b9fa1cd81a1f6e3ad0"
)
EXPECTED_CANDIDATE_SHA256 = (
    "1436e87661def2f8a70bd5c864bbe1a037474ba7df9e6d6222294c507394bcab"
)
EXPECTED_INTERMEDIATE_SOURCE_BYTES = 2697512
EXPECTED_CANDIDATE_BYTES = 2697522
EXPECTED_LINE_COUNT = 60535
EXPECTED_TARGET_HEADER_SHA256 = (
    "445719549ce79918a2f6cf953321db8ca2bf485cda0689dde2ff3dee3d5c3240"
)
EXPECTED_TARGET_REGION_SHA256 = (
    "7bc3b85b5048cb2c42df1f026a1261abcf4010bdcc5a38623ec74946f22aebfa"
)
EXPECTED_TARGET_REGION_AFTER_SHA256 = (
    "d839e9345714136fecf1a5c47fe07b0c44808c9392d55db0d4759be54a919cb9"
)
EXPECTED_SOURCE_PREFIX_SHA256 = (
    "4182e0526409b787b3763f40ac3cc599911459be2fd389d89ad25484e3c3d8d3"
)
EXPECTED_SOURCE_PREFIX_BYTES = 1501556
EXPECTED_SOURCE_SUFFIX_SHA256 = (
    "1def5e74ae100ea11b97431b4e723dd020ec97bc4972f66caab17372a05f275c"
)
EXPECTED_SOURCE_SUFFIX_BYTES = 1194946
EXPECTED_DECLARATION_SEQUENCE_SHA256 = (
    "c997317cd459891eea590671da4aa9941e5c083cbd5dffe91ee96601b12cc4f2"
)

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)

OLD_EXT = """    apply Subtype.ext
    simp only [logHeightBasePoint, H, Real.exp_log hH]"""

NEW_EXT = """    apply UpperHalfPlane.ext
    simp only [logHeightBasePoint, H, Real.exp_log hH]"""

OLD_FINAL_SIMP = """  simp only [heightC, logHeightBasePoint_im, Real.exp_log hH,
    Complex.ofReal_div]"""

NEW_FINAL_SIMP = """  simp only [heightC, logHeightBasePoint_im, Real.exp_log hH,
    Complex.ofReal_div, H]"""

VARIANTS = {
    "upper_ext_h_simp_only": (
        (
            (OLD_EXT, NEW_EXT),
            (OLD_FINAL_SIMP, NEW_FINAL_SIMP),
        ),
        (
            "use UpperHalfPlane.ext for the base-point equality and unfold the "
            "local cusp-height abbreviation H in the final simp-only step"
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
            "FA477 requires the exact authoritative FA476-r3 minimal_simpa "
            "candidate source; got "
            f"{intermediate_sha256}, expected {EXPECTED_INTERMEDIATE_SOURCE_SHA256}"
        )
    intermediate_bytes = len(text.encode("utf-8"))
    if intermediate_bytes != EXPECTED_INTERMEDIATE_SOURCE_BYTES:
        raise RuntimeError(
            "FA477 intermediate byte-count drift: "
            f"{intermediate_bytes} != {EXPECTED_INTERMEDIATE_SOURCE_BYTES}"
        )
    line_count = len(text.splitlines())
    if line_count != EXPECTED_LINE_COUNT:
        raise RuntimeError(
            f"FA477 line-count drift: {line_count} != {EXPECTED_LINE_COUNT}"
        )

    start, end = declaration_bounds(text, TARGET_DECLARATION)
    # The simple declaration scanner stops at the next theorem header, while
    # its doc comment lexically precedes that header.  Treat the doc comment as
    # part of the untouched post-2793 suffix, not as part of the target body.
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
        old_count = region.count(old)
        new_count_before = region.count(new)
        if old_count != 1 or new_count_before != 0:
            raise RuntimeError(
                f"{TARGET_DECLARATION}: expected old/new counts 1/0, got "
                f"{old_count}/{new_count_before}"
            )
        region = region.replace(old, new, 1)
        replacement_audit.append(
            {
                "old_count_before": old_count,
                "new_count_before": new_count_before,
                "old_sha256": sha256_text(old),
                "new_sha256": sha256_text(new),
                "old_bytes": len(old.encode("utf-8")),
                "new_bytes": len(new.encode("utf-8")),
            }
        )

    if region == original_region:
        raise RuntimeError(f"{TARGET_DECLARATION}: replacement produced no change")
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
    after_sequence = [match.group("name") for match in _DECL_START.finditer(candidate)]
    declaration_sequence_preserved = before_sequence == after_sequence
    if not declaration_sequence_preserved:
        raise RuntimeError(f"{TARGET_DECLARATION}: declaration sequence drift")
    declaration_sequence_sha256 = sha256_text("\n".join(before_sequence))
    if declaration_sequence_sha256 != EXPECTED_DECLARATION_SEQUENCE_SHA256:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: declaration sequence hash drift: "
            f"{declaration_sequence_sha256} != "
            f"{EXPECTED_DECLARATION_SEQUENCE_SHA256}"
        )
    candidate_sha256 = sha256_text(candidate)
    if candidate_sha256 != EXPECTED_CANDIDATE_SHA256:
        raise RuntimeError(
            f"FA477 candidate hash drift: {candidate_sha256} != "
            f"{EXPECTED_CANDIDATE_SHA256}"
        )
    candidate_bytes = len(candidate.encode("utf-8"))
    if candidate_bytes != EXPECTED_CANDIDATE_BYTES:
        raise RuntimeError(
            f"FA477 candidate byte-count drift: {candidate_bytes} != "
            f"{EXPECTED_CANDIDATE_BYTES}"
        )

    return candidate, {
        "fa476_r3_intermediate_source_sha256": intermediate_sha256,
        "fa476_r3_intermediate_source_bytes": intermediate_bytes,
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
    fa475_winner = os.environ.get("FA475_WINNER")
    if fa475_winner != EXACT_FA475_WINNER:
        raise RuntimeError(
            "FA477 requires FA475_WINNER=clean_semicolon, got "
            f"{fa475_winner!r}"
        )
    fa476_r2_variant = os.environ.get("FA476_R2_VARIANT")
    if fa476_r2_variant != EXACT_FA476_R2_VARIANT:
        raise RuntimeError(
            "FA477 requires FA476_R2_VARIANT=explicit_exp_nonneg, got "
            f"{fa476_r2_variant!r}"
        )
    fa476_r3_variant = os.environ.get("FA476_R3_VARIANT")
    if fa476_r3_variant != EXACT_FA476_R3_VARIANT:
        raise RuntimeError(
            "FA477 requires FA476_R3_VARIANT=minimal_simpa, got "
            f"{fa476_r3_variant!r}"
        )
    upstream_run_id = os.environ.get("FA476_R3_EVIDENCE_RUN_ID")
    if upstream_run_id != REQUIRED_UPSTREAM_EVIDENCE_RUN_ID:
        raise RuntimeError(
            "FA477 requires prior FA476-r3 closure evidence from run "
            f"{REQUIRED_UPSTREAM_EVIDENCE_RUN_ID}, got {upstream_run_id!r}"
        )
    upstream_artifact_id = os.environ.get("FA476_R3_EVIDENCE_ARTIFACT_ID")
    if upstream_artifact_id != REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_ID:
        raise RuntimeError(
            "FA477 requires exact FA476-r3 evidence artifact "
            f"{REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_ID}, got "
            f"{upstream_artifact_id!r}"
        )
    upstream_artifact_digest = os.environ.get(
        "FA476_R3_EVIDENCE_ARTIFACT_DIGEST"
    )
    if upstream_artifact_digest != REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_DIGEST:
        raise RuntimeError(
            "FA477 requires exact FA476-r3 evidence artifact digest "
            f"{REQUIRED_UPSTREAM_EVIDENCE_ARTIFACT_DIGEST}, got "
            f"{upstream_artifact_digest!r}"
        )
    variant = os.environ.get("FA477_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(f"unsupported or missing FA477_VARIANT={variant!r}")

    text, repairs = orig_norm_repairs(text)
    replacements, strategy = VARIANTS[variant]
    text, audit = replace_target_only(text, replacements)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "fa475_winner": fa475_winner,
            "fa476_r2_variant": fa476_r2_variant,
            "fa476_r3_variant": fa476_r3_variant,
            "required_upstream_evidence_run_id": int(upstream_run_id),
            "required_upstream_evidence_artifact_id": int(upstream_artifact_id),
            "required_upstream_evidence_artifact_digest": (
                upstream_artifact_digest
            ),
            "upstream_idx2792_closure_must_precede": True,
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA477 strict-frontier matrix",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "fa476_r2_variant": fa476_r2_variant,
            "fa476_r3_variant": fa476_r3_variant,
            "required_upstream_evidence_run_id": int(upstream_run_id),
            "required_upstream_evidence_artifact_id": int(upstream_artifact_id),
            "required_upstream_evidence_artifact_digest": (
                upstream_artifact_digest
            ),
            "upstream_idx2792_closure_must_precede": True,
        },
    ]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
