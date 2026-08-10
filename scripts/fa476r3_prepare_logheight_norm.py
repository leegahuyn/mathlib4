#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import os
import re
import sys
from pathlib import Path


ROOT = Path.cwd()
BASE = ROOT / "scripts/fa476r2_prepare_logheight_norm.py"
spec = importlib.util.spec_from_file_location("fa476r2base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa476r2 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa476r2
spec.loader.exec_module(fa476r2)

fa466 = fa476r2.fa466
orig_norm_repairs = fa476r2.norm_repairs


EXACT_FA475_WINNER = "clean_semicolon"
EXACT_FA476_R2_VARIANT = "explicit_exp_nonneg"
TARGET_DECLARATION = "norm_deriv_selectedLogHeightNaturalGauge_le_graph"
TARGET_DECLARATION_INDEX = 2792
EXACT_FA476_R2_EVIDENCE_ARTIFACT_ID = 9069711014
EXACT_FA476_R2_EVIDENCE_ARTIFACT_DIGEST_SHA256 = (
    "df4aa67dbc8af84a59480feca9c2874ec28ec6d958967fe3e7b849537c44b973"
)
EXACT_FA476_R2_EVIDENCE_REPOSITORY_HEAD = (
    "a878f45b6e22b63b5426cf7d55c1c13486923ece"
)
EXACT_FA476_R2_EVIDENCE_SOURCE_SHA256 = (
    "a389e62137cf93e33fd432282f4b3e66762e8a4750e26fccf229a256b88fb469"
)
EXACT_FA476_R2_EVIDENCE_SOURCE_BYTES = 2697469
EXPECTED_LINE_COUNT = 60535
EXPECTED_DECLARATION_COUNT = 4382
EXPECTED_DECLARATION_SEQUENCE_SHA256 = (
    "c997317cd459891eea590671da4aa9941e5c083cbd5dffe91ee96601b12cc4f2"
)
EXPECTED_TARGET_HEADER_SHA256 = (
    "1df5f5385c167d772dd6c874de939e71983d80a58e301c7425887bfa6d02a656"
)
EXPECTED_TARGET_REGION_SHA256 = (
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

OLD_FINAL = (
    "  exact mul_le_mul_of_nonneg_left hOuter "
    "(Real.exp_pos (r / 2)).le\n"
)

VARIANTS = {
    "minimal_simpa": {
        "role": "A-minimal",
        "new": (
            "  simpa only [z, f, S, F, R, L, mul_assoc] using "
            "(mul_le_mul_of_nonneg_left hOuter "
            "(Real.exp_pos (r / 2)).le)\n"
        ),
        "strategy": (
            "close the final local-let mismatch with one minimal simpa-only "
            "line over z, f, S, F, R, L, and mul_assoc"
        ),
        "candidate_sha256": (
            "5d96377b3b4895f7f48a847105ae1f077677c794df6bc6b9fa1cd81a1f6e3ad0"
        ),
        "candidate_bytes": 2697512,
        "candidate_line_count": 60535,
        "target_region_after_sha256": (
            "bf09ebf555b9ae95fe3ed67a0df711b896cafcdefd98d23abc7d7336badfa232"
        ),
        "new_fragment_sha256": (
            "37b3f453bf6527151bcdc9aa7a5dae910fa0e45791e6d8aa84b8c5976de4b6e2"
        ),
    },
    "explicit_dsimp": {
        "role": "B-explicit",
        "new": (
            "  dsimp only [z, f, S, F, R, L] at hOuter ⊢\n"
            "  simpa only [mul_assoc] using "
            "(mul_le_mul_of_nonneg_left hOuter "
            "(Real.exp_pos (r / 2)).le)\n"
        ),
        "strategy": (
            "explicitly dsimp z, f, S, F, R, and L in hOuter and the goal, "
            "then close the remaining association mismatch with simpa only"
        ),
        "candidate_sha256": (
            "add83f552b03177261ffce5bd84112e99afe025dff2b46a46c98ece7cc9eb174"
        ),
        "candidate_bytes": 2697540,
        "candidate_line_count": 60536,
        "target_region_after_sha256": (
            "811f6633db19ea8196ee395a4863b4a901ea80d685f1a40e2532462bb6c171a9"
        ),
        "new_fragment_sha256": (
            "fbd2c9a4fa9338f928489a5d0819d4540c000a63c385e14537d1baaf96b0bcd6"
        ),
    },
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
    text: str, variant: str
) -> tuple[str, dict[str, object]]:
    variant_spec = VARIANTS[variant]
    new = str(variant_spec["new"])
    intermediate_sha256 = sha256_text(text)
    if intermediate_sha256 != EXACT_FA476_R2_EVIDENCE_SOURCE_SHA256:
        raise RuntimeError(
            "FA476-r3 requires the exact valid FA476-r2 materialization from "
            f"artifact {EXACT_FA476_R2_EVIDENCE_ARTIFACT_ID}; got "
            f"{intermediate_sha256}, expected "
            f"{EXACT_FA476_R2_EVIDENCE_SOURCE_SHA256}"
        )
    intermediate_bytes = len(text.encode("utf-8"))
    if intermediate_bytes != EXACT_FA476_R2_EVIDENCE_SOURCE_BYTES:
        raise RuntimeError(
            f"FA476-r3 byte-count drift: {intermediate_bytes} != "
            f"{EXACT_FA476_R2_EVIDENCE_SOURCE_BYTES}"
        )
    line_count = len(text.splitlines())
    if line_count != EXPECTED_LINE_COUNT:
        raise RuntimeError(
            f"FA476-r3 line-count drift: {line_count} != {EXPECTED_LINE_COUNT}"
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

    old_count_in_target = original_region.count(OLD_FINAL)
    old_count_global = text.count(OLD_FINAL)
    new_counts_before = {
        name: original_region.count(str(specification["new"]))
        for name, specification in VARIANTS.items()
    }
    if old_count_in_target != 1 or old_count_global != 1:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: expected exact final line once in target "
            f"and source, got {old_count_in_target}/{old_count_global}"
        )
    if any(new_counts_before.values()):
        raise RuntimeError(
            f"{TARGET_DECLARATION}: an FA476-r3 replacement already exists: "
            f"{new_counts_before!r}"
        )

    region = original_region.replace(OLD_FINAL, new, 1)
    if sha256_text(region) != variant_spec["target_region_after_sha256"]:
        raise RuntimeError(
            f"{TARGET_DECLARATION}: {variant} target-region hash drift"
        )
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
    if len(before_sequence) != EXPECTED_DECLARATION_COUNT:
        raise RuntimeError(
            f"FA476-r3 declaration-count drift: {len(before_sequence)} != "
            f"{EXPECTED_DECLARATION_COUNT}"
        )
    before_sequence_sha256 = sha256_text("\n".join(before_sequence))
    if before_sequence_sha256 != EXPECTED_DECLARATION_SEQUENCE_SHA256:
        raise RuntimeError("FA476-r3 declaration-sequence hash drift")
    declaration_sequence_preserved = before_sequence == after_sequence
    if not declaration_sequence_preserved:
        raise RuntimeError(f"{TARGET_DECLARATION}: declaration sequence drift")

    candidate_sha256 = sha256_text(candidate)
    candidate_bytes = len(candidate.encode("utf-8"))
    candidate_line_count = len(candidate.splitlines())
    expected_candidate = str(variant_spec["candidate_sha256"])
    if candidate_sha256 != expected_candidate:
        raise RuntimeError(
            f"FA476-r3 {variant} candidate hash drift: {candidate_sha256} != "
            f"{expected_candidate}"
        )
    if candidate_bytes != variant_spec["candidate_bytes"]:
        raise RuntimeError(f"FA476-r3 {variant} candidate byte-count drift")
    if candidate_line_count != variant_spec["candidate_line_count"]:
        raise RuntimeError(f"FA476-r3 {variant} candidate line-count drift")
    if region.count(OLD_FINAL) != 0 or region.count(new) != 1:
        raise RuntimeError(f"FA476-r3 {variant} post-edit count drift")

    return candidate, {
        "exact_fa476_r2_evidence_artifact_id": (
            EXACT_FA476_R2_EVIDENCE_ARTIFACT_ID
        ),
        "exact_fa476_r2_evidence_artifact_digest_sha256": (
            EXACT_FA476_R2_EVIDENCE_ARTIFACT_DIGEST_SHA256
        ),
        "exact_fa476_r2_evidence_repository_head": (
            EXACT_FA476_R2_EVIDENCE_REPOSITORY_HEAD
        ),
        "exact_fa476_r2_evidence_source_sha256": intermediate_sha256,
        "exact_fa476_r2_evidence_source_bytes": intermediate_bytes,
        "candidate_source_sha256": candidate_sha256,
        "candidate_source_bytes": candidate_bytes,
        "source_line_count": line_count,
        "candidate_line_count": candidate_line_count,
        "replacement_count": 1,
        "old_fragment_sha256": sha256_text(OLD_FINAL),
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
        "declaration_count": len(before_sequence),
        "declaration_sequence_sha256": before_sequence_sha256,
        "declaration_sequence_preserved": declaration_sequence_preserved,
        "old_fragment_count_before": old_count_in_target,
        "old_fragment_count_after": region.count(OLD_FINAL),
        "new_fragment_count_before": new_counts_before[variant],
        "new_fragment_count_after": region.count(new),
        "variant_role": variant_spec["role"],
    }


def norm_repairs(text: str):
    fa475_winner = os.environ.get("FA475_WINNER")
    if fa475_winner != EXACT_FA475_WINNER:
        raise RuntimeError(
            "FA476-r3 requires FA475_WINNER=clean_semicolon, got "
            f"{fa475_winner!r}"
        )
    r2_variant = os.environ.get("FA476_R2_VARIANT")
    if r2_variant != EXACT_FA476_R2_VARIANT:
        raise RuntimeError(
            "FA476-r3 requires FA476_R2_VARIANT=explicit_exp_nonneg, got "
            f"{r2_variant!r}"
        )
    variant = os.environ.get("FA476_R3_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(
            f"unsupported or missing FA476_R3_VARIANT={variant!r}"
        )

    text, repairs = orig_norm_repairs(text)
    text, audit = replace_target_only(text, variant)
    return text, repairs + [
        {
            "declaration": TARGET_DECLARATION,
            "declaration_index": TARGET_DECLARATION_INDEX,
            "strategy": VARIANTS[variant]["strategy"],
            "matrix_variant": variant,
            "fa475_winner": fa475_winner,
            "fa476_r2_variant": r2_variant,
            "frontier_declaration_index": TARGET_DECLARATION_INDEX,
            "later_repair_count": 0,
            "max_errors": 32,
            **audit,
        },
        {
            "declaration": "FA476-r3 strict-frontier matrix",
            "strategy": variant,
            "variant_role": VARIANTS[variant]["role"],
            "target_declaration": TARGET_DECLARATION,
            "target_declaration_index": TARGET_DECLARATION_INDEX,
            "fa476_r2_variant": r2_variant,
            "later_repair_count": 0,
        },
    ]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
