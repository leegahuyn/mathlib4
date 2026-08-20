#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path


ROOT = Path.cwd()
BASE = ROOT / "scripts/fa476_prepare_logheight_norm.py"
spec = importlib.util.spec_from_file_location("fa476base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa476 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa476
spec.loader.exec_module(fa476)

fa466 = fa476.fa466
orig_norm_repairs = fa476.norm_repairs


EXACT_FA475_WINNER = "clean_semicolon"
TARGET_DECLARATION = "norm_deriv_selectedLogHeightNaturalGauge_le_graph"
TARGET_DECLARATION_INDEX = 2792
EXACT_FA476_EVIDENCE_ARTIFACT_ID = 9069198424
EXACT_FA476_EVIDENCE_SOURCE_SHA256 = (
    "9b4c42180dfcbdb3b2c7977c225776902986c310eae9a55b0d92d9985c416efe"
)
EXPECTED_CANDIDATE_SHA256 = (
    "a389e62137cf93e33fd432282f4b3e66762e8a4750e26fccf229a256b88fb469"
)
EXPECTED_TARGET_HEADER_SHA256 = (
    "1df5f5385c167d772dd6c874de939e71983d80a58e301c7425887bfa6d02a656"
)
EXPECTED_TARGET_REGION_SHA256 = (
    "0d5232548a9eab10c01760dc6054a43858bee2dcf3a9a65bb76bbd44078f0fcf"
)
EXPECTED_TARGET_REGION_AFTER_SHA256 = (
    "ba2723bc065f721dc4e00bb319df3a887710522c544dd031d1f9b0d32034fd9e"
)
EXPECTED_SOURCE_PREFIX_SHA256 = (
    "c5ead146a8e578dc26ec980fb83f067f7875b629b8ef04199b3d304fd34e30ee"
)
EXPECTED_SOURCE_PREFIX_BYTES = 1499209
EXPECTED_SOURCE_SUFFIX_SHA256 = (
    "9cc10afb2a5d5e430f7b76193e7d31c1779ea771ee28366c751429649c45e04f"
)
EXPECTED_SOURCE_SUFFIX_BYTES = 1195956
EXPECTED_LINE_COUNT = 60535

OLD_NONNEG = "(Real.exp_pos _).le"
NEW_NONNEG = "(Real.exp_pos (r / 2)).le"

VARIANTS = {
    "explicit_exp_nonneg": (
        OLD_NONNEG,
        NEW_NONNEG,
        (
            "instantiate the exponential positivity proof at the exact outer "
            "factor r / 2 instead of leaving its argument metavariable implicit"
        ),
    ),
}

_DECL_START = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)


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
    text: str, old: str, new: str
) -> tuple[str, dict[str, object]]:
    intermediate_sha256 = sha256_text(text)
    if intermediate_sha256 != EXACT_FA476_EVIDENCE_SOURCE_SHA256:
        raise RuntimeError(
            "FA476-r2 requires the exact valid FA476 materialization from "
            f"artifact {EXACT_FA476_EVIDENCE_ARTIFACT_ID}; got "
            f"{intermediate_sha256}, expected {EXACT_FA476_EVIDENCE_SOURCE_SHA256}"
        )
    if len(text.splitlines()) != EXPECTED_LINE_COUNT:
        raise RuntimeError(
            f"FA476-r2 line-count drift: {len(text.splitlines())} != "
            f"{EXPECTED_LINE_COUNT}"
        )

    start, end = declaration_bounds(text, TARGET_DECLARATION)
    prefix = text[:start]
    original_region = text[start:end]
    suffix = text[end:]
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
            f"{TARGET_DECLARATION}: exact prefix/target/suffix guard mismatch: "
            f"{observed_guard!r} != {expected_guard!r}"
        )
    old_count = original_region.count(old)
    new_count_before = original_region.count(new)
    if old_count != 1 or new_count_before != 0:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: expected old/new counts 1/0, got "
            f"{old_count}/{new_count_before}"
        )

    region = original_region.replace(old, new, 1)
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
    candidate_sha256 = sha256_text(candidate)
    if candidate_sha256 != EXPECTED_CANDIDATE_SHA256:
        raise RuntimeError(
            f"FA476-r2 candidate hash drift: {candidate_sha256} != "
            f"{EXPECTED_CANDIDATE_SHA256}"
        )

    return candidate, {
        "exact_fa476_evidence_artifact_id": EXACT_FA476_EVIDENCE_ARTIFACT_ID,
        "exact_fa476_evidence_source_sha256": intermediate_sha256,
        "candidate_source_sha256": candidate_sha256,
        "replacement_count": 1,
        "old_fragment_sha256": sha256_text(old),
        "new_fragment_sha256": sha256_text(new),
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
        "declaration_sequence_preserved": declaration_sequence_preserved,
    }


def norm_repairs(text: str):
    fa475_winner = os.environ.get("FA475_WINNER")
    if fa475_winner != EXACT_FA475_WINNER:
        raise RuntimeError(
            "FA476-r2 requires FA475_WINNER=clean_semicolon, got "
            f"{fa475_winner!r}"
        )
    variant = os.environ.get("FA476_R2_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(
            f"unsupported or missing FA476_R2_VARIANT={variant!r}"
        )

    text, repairs = orig_norm_repairs(text)
    old, new, strategy = VARIANTS[variant]
    text, audit = replace_target_only(text, old, new)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": strategy,
            "matrix_variant": variant,
            "fa475_winner": fa475_winner,
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA476-r2 strict-frontier matrix",
            "strategy": variant,
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
