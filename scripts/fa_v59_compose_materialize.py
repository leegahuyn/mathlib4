#!/usr/bin/env python3
"""Fail-closed exact-manifest composer/materializer for the FA v59 matrix.

The script is deliberately static: it reads one SHA-locked selection index,
the exact v58 core_base authority source, and exact declaration-local repair
manifests.  It never invokes Lean, Lake, git, GitHub, a shell, or the network.
No output is published until source identity, manifest identity, owner-local
replacement counts, the expected candidate identity, declaration order and
headers, comments, attributes, and executable trust-six invariants all pass.

A PENDING index exits 2 and emits no candidate.  ``--validate-pending-index``
exists only to audit a scaffold without activating materialization.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path
from typing import Any


INDEX_SCHEMA = "fa-v59-independent-matrix-selection-v1"
AUDIT_SCHEMA = "fa-v59-independent-matrix-owner-local-static-audit-v1"
EVIDENCE_SCHEMA = "fa-v59-independent-matrix-materialization-evidence-v1"
READY_STATUS = "READY"
EXIT_PENDING = 2
DECLARATION_COUNT = 4416
GROUP_KEYS = (
    "F3930",
    "F3933",
    "F3939",
    "W4017",
    "W4018P1",
    "W4019",
    "R4198",
)
VARIANT_ORDER = (
    "M_promoted_without_idx3933",
    "F_fourier_full",
    "W_weighted_structural",
    "R_reduced_inline_isolated",
    "A_all",
    "A_no_idx3933",
)
ALLOWED_SELECTION_MAP = {
    "M_promoted_without_idx3933": ("F3930", "F3939", "W4019"),
    "F_fourier_full": ("F3930", "F3933", "F3939"),
    "W_weighted_structural": ("W4017", "W4018P1", "W4019"),
    "R_reduced_inline_isolated": ("R4198",),
    "A_all": GROUP_KEYS,
    "A_no_idx3933": (
        "F3930", "F3939", "W4017", "W4018P1", "W4019", "R4198",
    ),
}
REPAIR_ID_BY_GROUP = {
    "F3930": "V58-FOURIER-IDX3930-INVERSE-FIRST-REAL-COORDINATE",
    "F3933": "V58-FOURIER-IDX3933-DETERMINISTIC-INNER-STAR-REWRITE",
    "F3939": "V58-FOURIER-IDX3939-RING-NORMALIZE-CASTED-SQUARE",
    "W4017": "V58-WEIGHTED-IDX4017-explicit-two-level-clm-ext",
    "W4018P1": "V58-IDX4018-P01-EXPLICIT-MKCONTINUOUS2-EVALUATION",
    "W4019": "V58-WEIGHTED-IDX4019-use-exact-norm-neg-term",
    "R4198": "V58-IDX4198-INLINE-EFFECTIVE-FREENESS-BODY-ONLY",
}
EXPECTED_CANDIDATES = {
    "M_promoted_without_idx3933": {
        "sha256": "c3311de418db700651ca9fd9b0e34f069c11e47e4eaa8171768fa722d8bc0c2a",
        "bytes": 2807131,
        "lines": 62813,
    },
    "F_fourier_full": {
        "sha256": "25f1b28103e99dc3b7c70457d9ade2f137063c100878e73fd9bb3c50e8ff9b44",
        "bytes": 2807136,
        "lines": 62814,
    },
    "W_weighted_structural": {
        "sha256": "aae300cb43942895c02be3ca4da3a85276ef70c8af7fd8eec543be35a120810c",
        "bytes": 2807262,
        "lines": 62818,
    },
    "R_reduced_inline_isolated": {
        "sha256": "5a231db840bc576a365fa3f9cd9aeaccab5ec98683834edb20d41e4ec5eaf5eb",
        "bytes": 2812354,
        "lines": 62931,
    },
    "A_all": {
        "sha256": "dedbf67b514b3838c743c3eabe2bdf6b5482cdfd232556fc9acc4ab0138b68f8",
        "bytes": 2812426,
        "lines": 62933,
    },
    "A_no_idx3933": {
        "sha256": "84e0a7843de9bcf99a25e51db95d48e9d5feceffe4e1b94f315b11d166792e5a",
        "bytes": 2812433,
        "lines": 62933,
    },
}
TRUST_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)
DIRECT_COMPILE_CHAIN = (
    ("Mock2", 1),
    ("Mock2_Advanced", 1),
    ("Mock2_FunctionalAnalysis", 2000),
)
AUTHORITY = {
    "workflow_run_id": 31803223990,
    "head_sha": "14e3e3f5e85f3c3ca7a1381eb88522552ffe29dc",
    "head_branch": "codex/fa-exclusive-focus-20260814",
    "artifact_id": 9220688452,
    "artifact_name": (
        "codex-fa-v58-core_base-highcap2000-"
        "14e3e3f5e85f3c3ca7a1381eb88522552ffe29dc"
    ),
    "artifact_size_in_bytes": 619491,
    "artifact_digest":
        "sha256:269100960a5e7ecd8b35e39cdde2c774f244b49c269e992aec00203bd2288ab4",
    "variant": "core_base",
    "source_sha256":
        "013f64cf5eaaab544629ad02fc2e33e63f90916e9b1e1581d73f2af2e7ba34ba",
    "source_bytes": 2807163,
    "source_lines": 62815,
    "declaration_count": DECLARATION_COUNT,
    "diagnostics_sha256":
        "a9ec828f9bbe0226b2bc694f26911cfd84fce016adca411f9bb8df52c6833db1",
    "fa_log_sha256":
        "8395ab207c12ad32483166ec9a118b4fe1d82a1c772d5cd79d9237563efc9127",
    "patch_audit_sha256":
        "372037c8eee8ce1a030e5085b831b5f04c9bfaaa9e8f707767ed48ecbe630b9a",
}
MAX_HEARTBEAT_COUNTS = {
    "token_count": 8,
    "set_option_count": 8,
}
BASE_RUNNER = {
    "runtime_path": "scripts/fa_v42_direct_compile_ci.sh",
    "sha256": "2459f0a2cd44f6a3716de1ed2934c7588ba1a1e27ef443947d9e6089af196514",
    "bytes": 2554,
}
BASE_COLLECTOR = {
    "runtime_path": "scripts/fa_v42_collect_full_diagnostics.py",
    "sha256": "7de7bc92e4e2735c0d25706d70777ea67340d8afcf67434e43b051d5cb8c90c6",
    "bytes": 12932,
}
PROMOTION_INPUTS = {
    "fourier_manifest": {
        "registry_path": "work/v58-workers/fourier/fourier-repair-manifest.json",
        "runtime_path": "scripts/fa_v59_source_fourier_manifest.json",
        "evidence_path": "work/v58-workers/fourier/fourier-repair-manifest.json",
        "sha256": "243e6879937108ff21c4fa676745d00e3d1c90530508a00729d375297ecda934",
        "bytes": 9318,
    },
    "weighted_staged_manifest": {
        "registry_path": "work/v58-workers/weighted/staged-manifest.json",
        "runtime_path": "scripts/fa_v59_source_weighted_staged_manifest.json",
        "evidence_path": "work/v58-workers/weighted/staged-manifest.json",
        "sha256": "24fc203adb4bdc3ac00ec06f0039c0f5a0e5456a9ba8be3e26e5a9efb0a4ca44",
        "bytes": 3864,
    },
    "weighted_promoted_manifest": {
        "registry_path": "work/v58-workers/weighted/promoted-manifest.json",
        "runtime_path": "scripts/fa_v59_source_weighted_promoted_manifest.json",
        "evidence_path": "work/v58-workers/weighted/promoted-manifest.json",
        "sha256": "50b1f57b6c973a6314dc726e65a80b2787bf8dd068f32b69a6bc1aaa82d7fcee",
        "bytes": 4116,
    },
    "weighted_result_index": {
        "registry_path": "work/v58-workers/weighted/result-index.json",
        "runtime_path": "scripts/fa_v59_source_weighted_result_index.json",
        "evidence_path": "work/v58-workers/weighted/result-index.json",
        "sha256": "239a3c7a65815a05ac8e462ec5a5bdf244eaefde80b2417cd5ca73113439585c",
        "bytes": 2572,
    },
    "idx4018_p01_manifest": {
        "registry_path": (
            "work/v58-workers/weighted-idx4018/"
            "probe-01-mkcontinuous2-manifest.json"
        ),
        "runtime_path": "scripts/fa_v59_source_idx4018_p01_manifest.json",
        "evidence_path": (
            "work/v58-workers/weighted-idx4018/"
            "probe-01-mkcontinuous2-manifest.json"
        ),
        "sha256": "5674c746d28595cfaa492f7b116e4ee685f0b225bd2e50faf09c8f461970f5c9",
        "bytes": 5319,
    },
    "idx4018_result_index": {
        "registry_path": "work/v58-workers/weighted-idx4018/result-index.json",
        "runtime_path": "scripts/fa_v59_source_idx4018_result_index.json",
        "evidence_path": "work/v58-workers/weighted-idx4018/result-index.json",
        "sha256": "5c80df46f3f4dee2a17298a9e3d4fabc4cda12585ea01b04e181ea8b5c369b3a",
        "bytes": 5217,
    },
    "reduced_manifest": {
        "registry_path": (
            "work/v58-workers/reduced-chart/"
            "V58_IDX4198_STAGED_BODY_ONLY_MANIFEST.json"
        ),
        "runtime_path": "scripts/fa_v59_source_reduced_manifest.json",
        "evidence_path": (
            "work/v58-workers/reduced-chart/"
            "V58_IDX4198_STAGED_BODY_ONLY_MANIFEST.json"
        ),
        "sha256": "c9acdee76dc90a6104a920d85ca70980f0debb44f0116936f7243be4ab875add",
        "bytes": 7095,
    },
    "reduced_preview": {
        "registry_path": "work/v58-workers/reduced-chart/idx4198-body-only-preview.lean",
        "runtime_path": "scripts/fa_v59_source_reduced_preview.lean",
        "evidence_path": "work/v58-workers/reduced-chart/idx4198-body-only-preview.lean",
        "sha256": "8cebb44101b712d121aef1795cf626d47c3bcce72eb4a0bd16cc1a8771a7370c",
        "bytes": 5821,
    },
}
REPAIR_REGISTRY_LOCK = {
    "status": "LOCKED",
    "runtime_path": "scripts/fa_v59_normalized_repair_groups.json",
    "evidence_path": "work/v59-cross-audit/normalized-repair-groups.json",
    "sha256": "dd181f279be61ac4b77aff843989ac407ce29fe85d79b496479645128f025eec",
    "bytes": 16106,
    "schema": "fa-v59-cross-normalized-repair-groups-v1",
    "payload_status": "LOCKED_STATIC_GROUPS_DIRECT_LEAN_UNVERIFIED",
    "group_count": 7,
}
MATRIX_CROSS_AUDIT_LOCK = {
    "status": "LOCKED",
    "runtime_path": "scripts/fa_v59_variant_matrix_cross_audit.json",
    "evidence_path": "work/v59-cross-audit/variant-matrix.json",
    "sha256": "b1ed4d57f9932567005247923ce27a91b1c291f4e814fb2b1a691f67c87a5d3f",
    "bytes": 10639,
    "schema": "fa-v59-cross-variant-matrix-v1",
    "payload_status": "STATIC_MATERIALIZATION_LOCKS_COMPLETE_DIRECT_LEAN_REQUIRED",
}
CROSS_AUDIT_SUPPORT = {
    "static_audit": {
        "runtime_path": "scripts/fa_v59_cross_manifest_static_audit.json",
        "evidence_path": "work/v59-cross-audit/cross-manifest-static-audit.json",
        "sha256": "809035f32feaa18edebdafa04c2cd787813724a1e980c7b680487c92b8eec003",
        "bytes": 18637,
    },
    "hash_ledger": {
        "runtime_path": "scripts/fa_v59_cross_hashes.sha256",
        "evidence_path": "work/v59-cross-audit/HASHES.sha256",
        "sha256": "439bc01717c27799990ef1df893cf2f8d1710102f01c931b25d3cd753e1a4717",
        "bytes": 2029,
    },
    "composition_recommendation": {
        "runtime_path": "scripts/fa_v59_composition_recommendation.md",
        "evidence_path": "work/v59-cross-audit/composition-recommendation.md",
        "sha256": "13a03cccf0a877431410ecef0f9c820b5df885e5cac2b129fda343059d0175f9",
        "bytes": 5493,
    },
}
HEX_RE = re.compile(r"[0-9a-f]{64}")
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def require_sha(value: Any, label: str) -> str:
    text = str(value)
    require(HEX_RE.fullmatch(text) is not None, f"{label}: invalid SHA-256")
    require(text != "0" * 64, f"{label}: zero/pending SHA-256")
    return text


def canonical(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def load_json_bytes(path: Path) -> tuple[bytes, dict[str, Any]]:
    payload = path.read_bytes()
    value = json.loads(payload)
    require(isinstance(value, dict), f"{path}: top level must be an object")
    return payload, value


def regions(text: str) -> list[dict[str, Any]]:
    matches = list(DECL_RE.finditer(text))
    return [
        {
            "index": index,
            "name": match.group(1),
            "start": match.start(),
            "end": matches[index + 1].start()
            if index + 1 < len(matches)
            else len(text),
        }
        for index, match in enumerate(matches)
    ]


def raw_headers(text: str) -> list[tuple[str, str]]:
    result: list[tuple[str, str]] = []
    for region in regions(text):
        block = text[region["start"] : region["end"]]
        cuts = [
            point
            for point in (
                block.find(":= by"),
                block.find(":="),
                block.find(" where\n"),
            )
            if point >= 0
        ]
        header = block if not cuts else block[: min(cuts)]
        result.append((region["name"], header))
    return result


def comments_and_attributes(text: str) -> tuple[list[str], list[str]]:
    comments: list[str] = []
    attributes: list[str] = []
    index = 0
    while index < len(text):
        if text.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while depth:
                require(index < len(text), "unterminated block comment")
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            comments.append(text[start:index])
            continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                end = len(text)
            comments.append(text[index:end])
            index = end
            continue
        if text.startswith("@[", index):
            end = text.find("]", index + 2)
            require(end >= 0, "unterminated attribute")
            attributes.append(text[index : end + 1])
            index = end + 1
            continue
        index += 1
    return comments, attributes


def strip_noncode(text: str) -> str:
    chars = list(text)
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(chars):
        if depth:
            if text.startswith("/-", index):
                chars[index] = chars[index + 1] = " "
                depth += 1
                index += 2
                continue
            if text.startswith("-/", index):
                chars[index] = chars[index + 1] = " "
                depth -= 1
                index += 2
                continue
            if chars[index] != "\n":
                chars[index] = " "
            index += 1
            continue
        if in_string:
            original = chars[index]
            if original != "\n":
                chars[index] = " "
            if escaped:
                escaped = False
            elif original == "\\":
                escaped = True
            elif original == '"':
                in_string = False
            index += 1
            continue
        if text.startswith("/-", index):
            chars[index] = chars[index + 1] = " "
            depth = 1
            index += 2
            continue
        if text.startswith("--", index):
            while index < len(chars) and chars[index] != "\n":
                chars[index] = " "
                index += 1
            continue
        if chars[index] == '"':
            chars[index] = " "
            in_string = True
        index += 1
    require(depth == 0 and not in_string, "unterminated non-code region")
    return "".join(chars)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        token: len(
            re.findall(
                r"(?<![A-Za-z0-9_])"
                + re.escape(token)
                + r"(?![A-Za-z0-9_])",
                code,
            )
        )
        for token in TRUST_TOKENS
    }


def max_heartbeat_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        "token_count": len(re.findall(r"\bmaxHeartbeats\b", code)),
        "set_option_count": len(
            re.findall(r"\bset_option\s+maxHeartbeats\b", code)
        ),
    }


def resolve_record_path(
    root: Path,
    record: dict[str, Any],
    *,
    allow_evidence_path_fallback: bool,
) -> tuple[Path, bool]:
    runtime = root / str(record["runtime_path"])
    if runtime.is_file():
        return runtime, False
    if allow_evidence_path_fallback:
        evidence_value = record.get("evidence_path") or record.get("source_path")
        if evidence_value:
            evidence = root / str(evidence_value)
            if evidence.is_file():
                return evidence, True
    raise SystemExit(f"locked runtime input missing: {runtime}")


def verify_file_record(path: Path, record: dict[str, Any], label: str) -> bytes:
    payload = path.read_bytes()
    expected_sha = require_sha(record.get("sha256"), label)
    require(sha256(payload) == expected_sha, f"{label}: SHA mismatch")
    require(len(payload) == int(record["bytes"]), f"{label}: byte mismatch")
    return payload


def authority_projection(value: dict[str, Any]) -> dict[str, Any]:
    require(isinstance(value, dict), "authority must be an object")
    require(value == AUTHORITY, "full canonical authority mismatch")
    return dict(value)


def validate_common_index(
    index: dict[str, Any],
    index_payload: bytes,
    root: Path,
    *,
    allow_evidence_path_fallback: bool,
) -> dict[str, Any]:
    require(index.get("schema") == INDEX_SCHEMA, "selection schema mismatch")
    require(index.get("direct_lean_verified") is False,
            "selection claims direct Lean verification")
    require(index.get("clean_build_claimed") is False,
            "selection claims clean build")
    require(index.get("source_moves") == [], "source moves are forbidden")
    require(index.get("runtime_evidence_fallback_allowed") is False,
            "selection metadata allows runtime evidence fallback")
    require(tuple(index.get("trust_tokens", [])) == TRUST_TOKENS,
            "trust-six contract drift")
    authority_projection(index.get("authority", {}))
    compile_chain = tuple(
        (row.get("source"), row.get("max_errors"))
        for row in index.get("direct_compile_chain", [])
    )
    require(compile_chain == DIRECT_COMPILE_CHAIN,
            "direct compile chain mismatch")
    require(tuple(index.get("variant_order", [])) == VARIANT_ORDER,
            "variant order mismatch")
    require(tuple(index.get("group_order", [])) == GROUP_KEYS,
            "repair group order mismatch")
    group_repair_ids = index.get("group_repair_ids")
    require(isinstance(group_repair_ids, dict), "group repair ID map missing")
    require(tuple(group_repair_ids) == GROUP_KEYS,
            "group repair ID map order mismatch")
    require(group_repair_ids == REPAIR_ID_BY_GROUP,
            "group repair ID map mismatch")
    variants = index.get("variants")
    require(isinstance(variants, list), "variants must be a list")
    require(tuple(row.get("name") for row in variants) == VARIANT_ORDER,
            "variant list/order mismatch")
    allowed = index.get("allowed_selection_map")
    require(isinstance(allowed, dict), "allowed selection map missing")
    require(tuple(allowed) == VARIANT_ORDER,
            "allowed selection map variant order mismatch")
    for variant in VARIANT_ORDER:
        keys = allowed.get(variant)
        require(isinstance(keys, list),
                f"{variant}: allowed group selection must be a list")
        require(tuple(keys) == ALLOWED_SELECTION_MAP[variant],
                f"{variant}: allowed group selection mismatch")
        require(len(keys) == len(set(keys)),
                f"{variant}: duplicate allowed group key")
        require(set(keys) <= set(GROUP_KEYS),
                f"{variant}: unknown allowed group key")
    for row in variants:
        keys = row.get("selected_group_keys")
        require(isinstance(keys, list),
                f"{row.get('name')}: selected group keys must be a list")
        require(keys == allowed[row["name"]],
                f"{row['name']}: selection differs from allowed map")
        require(len(keys) == len(set(keys)),
                f"{row['name']}: duplicate group key")

    locks = index.get("locks")
    require(isinstance(locks, dict), "script locks missing")
    require(
        {
            key: locks["base_runner"].get(key) for key in BASE_RUNNER
        } == BASE_RUNNER,
        "base runner lock drift",
    )
    require(
        {
            key: locks["base_collector"].get(key) for key in BASE_COLLECTOR
        } == BASE_COLLECTOR,
        "base collector lock drift",
    )
    script_payload = Path(__file__).resolve().read_bytes()
    composer_lock = locks.get("composer_materializer", {})
    require(sha256(script_payload) == require_sha(
        composer_lock.get("sha256"), "composer/materializer"
    ), "composer/materializer self SHA mismatch")
    require(len(script_payload) == int(composer_lock.get("bytes", -1)),
            "composer/materializer self byte mismatch")

    verified_locks: dict[str, Any] = {}
    for key, record in locks.items():
        require(isinstance(record, dict), f"lock {key}: record missing")
        path, fallback = resolve_record_path(
            root,
            record,
            allow_evidence_path_fallback=allow_evidence_path_fallback,
        )
        payload = verify_file_record(path, record, f"lock {key}")
        verified_locks[key] = {
            "path": path.as_posix(),
            "used_evidence_path_fallback": fallback,
            "sha256": sha256(payload),
            "bytes": len(payload),
        }

    promotion_inputs = index.get("promotion_inputs")
    require(isinstance(promotion_inputs, dict), "promotion input map missing")
    require(promotion_inputs == PROMOTION_INPUTS,
            "promotion input path/hash/byte map mismatch")
    verified_promotion_inputs: dict[str, Any] = {}
    for key, record in promotion_inputs.items():
        path, fallback = resolve_record_path(
            root,
            record,
            allow_evidence_path_fallback=allow_evidence_path_fallback,
        )
        payload = verify_file_record(path, record, f"promotion input {key}")
        verified_promotion_inputs[key] = {
            "path": path.as_posix(),
            "used_evidence_path_fallback": fallback,
            "sha256": sha256(payload),
            "bytes": len(payload),
        }

    cross_support = index.get("cross_audit_support")
    require(isinstance(cross_support, dict), "cross-audit support map missing")
    require(cross_support == CROSS_AUDIT_SUPPORT,
            "cross-audit support path/hash/byte map mismatch")
    verified_cross_support: dict[str, Any] = {}
    for key, record in cross_support.items():
        path, fallback = resolve_record_path(
            root,
            record,
            allow_evidence_path_fallback=allow_evidence_path_fallback,
        )
        payload = verify_file_record(path, record, f"cross-audit support {key}")
        verified_cross_support[key] = {
            "path": path.as_posix(),
            "used_evidence_path_fallback": fallback,
            "sha256": sha256(payload),
            "bytes": len(payload),
        }

    require(index.get("index_sha256") is None,
            "selection must not self-claim an impossible recursive hash")
    require(
        index.get("index_identity_contract")
        == "EXTERNAL_SHA256_LOCK_ONLY_NO_RECURSIVE_SELF_HASH",
        "selection external index-identity contract mismatch",
    )
    return {
        "schema": "fa-v59-index-validation-v1",
        "status": index.get("status"),
        "index_sha256": sha256(index_payload),
        "index_bytes": len(index_payload),
        "authority": AUTHORITY,
        "verified_locks": verified_locks,
        "verified_promotion_inputs": verified_promotion_inputs,
        "verified_cross_audit_support": verified_cross_support,
        "variant_order": list(VARIANT_ORDER),
    }


def validate_pending_index(index: dict[str, Any]) -> None:
    require(str(index.get("status", "")).startswith("PENDING"),
            "pending validation requires PENDING status")
    activation = index.get("activation", {})
    for key in (
        "materialization_allowed",
        "workflow_matrix_allowed",
        "direct_compile_allowed",
    ):
        require(activation.get(key) is False,
                f"pending activation must be false: {key}")
    pending = index.get("pending_inputs")
    require(isinstance(pending, dict), "pending input map missing")
    require(set(pending) == {
        "normalized_registry_final", "variant_matrix_cross_audit",
    }, "pending input map mismatch")
    for key, record in pending.items():
        require(str(record.get("status", "")).startswith("PENDING"),
                f"{key}: pending status missing")
        require(record.get("sha256") is None,
                f"{key}: SHA must remain null until arrival")

    registry = index.get("repair_registry")
    require(isinstance(registry, dict), "normalized repair registry missing")
    require(str(registry.get("status", "")).startswith("PENDING"),
            "normalized repair registry must remain pending")
    require(registry.get("runtime_path")
            == "scripts/fa_v59_normalized_repair_groups.json",
            "normalized repair registry runtime path mismatch")
    require(registry.get("evidence_path")
            == "work/v59-cross-audit/normalized-repair-groups.json",
            "normalized repair registry evidence path mismatch")
    require(registry.get("sha256") is None and registry.get("bytes") is None,
            "pending repair registry identity must remain null")
    matrix_audit = index.get("matrix_cross_audit")
    require(isinstance(matrix_audit, dict), "matrix cross-audit record missing")
    require(str(matrix_audit.get("status", "")).startswith("PENDING"),
            "matrix cross-audit must remain pending")
    require(matrix_audit.get("sha256") is None
            and matrix_audit.get("bytes") is None,
            "pending matrix cross-audit identity must remain null")

    for row in index["variants"]:
        require(row.get("lock_finalized") is False,
                f"{row.get('name')}: variant lock finalized while pending")
        require(str(row.get("status", "")).startswith("PENDING"),
                f"{row.get('name')}: pending variant status missing")
        require(row.get("selected_repair_ids") is None,
                f"{row.get('name')}: repair IDs finalized while pending")
        expected_ids = [REPAIR_ID_BY_GROUP[key]
                        for key in row["selected_group_keys"]]
        require(row.get("provisional_selected_repair_ids") == expected_ids,
                f"{row.get('name')}: provisional repair IDs mismatch")
        require(row.get("provisional_expected_candidate")
                == EXPECTED_CANDIDATES[row["name"]],
                f"{row.get('name')}: provisional candidate identity mismatch")
        require(row.get("expected_candidate") is None,
                f"{row.get('name')}: final candidate lock must remain null")


def validate_ready_index(index: dict[str, Any]) -> None:
    require(index.get("status") == READY_STATUS, "selection is not READY")
    activation = index.get("activation", {})
    require(all(activation.get(key) is True for key in (
        "materialization_allowed",
        "workflow_matrix_allowed",
        "direct_compile_allowed",
    )), "READY activation gate is incomplete")
    require(index.get("pending_inputs") == {}, "READY index retains pending inputs")
    require(index.get("repair_registry") == REPAIR_REGISTRY_LOCK,
            "normalized repair registry lock mismatch")
    require(index.get("matrix_cross_audit") == MATRIX_CROSS_AUDIT_LOCK,
            "matrix cross-audit lock mismatch")
    for row in index["variants"]:
        require(row.get("lock_finalized") is True,
                f"{row['name']}: final lock missing")
        require(row.get("status") == "LOCKED", f"{row['name']}: not locked")
        group_keys = row.get("selected_group_keys")
        require(group_keys == index["allowed_selection_map"][row["name"]],
                f"{row['name']}: exact independent group selection mismatch")
        require(len(group_keys) == len(set(group_keys)),
                f"{row['name']}: duplicate selected group key")
        repair_ids = row.get("selected_repair_ids")
        expected_repair_ids = [REPAIR_ID_BY_GROUP[key] for key in group_keys]
        require(repair_ids == expected_repair_ids,
                f"{row['name']}: exact selected repair ID/order mismatch")
        require(len(repair_ids) == len(set(repair_ids)),
                f"{row['name']}: duplicate selected repair ID")
        require(row.get("provisional_selected_repair_ids")
                == expected_repair_ids,
                f"{row['name']}: provisional repair ID/order drift")
        expected = row.get("expected_candidate")
        require(isinstance(expected, dict),
                f"{row['name']}: expected candidate lock missing")
        require(expected == EXPECTED_CANDIDATES[row["name"]],
                f"{row['name']}: candidate identity differs from six-way lock")
        require(row.get("provisional_expected_candidate") == expected,
                f"{row['name']}: provisional/final candidate lock mismatch")


def verify_manifest_authority(authority: dict[str, Any], label: str) -> None:
    require(isinstance(authority, dict) and authority == AUTHORITY,
            f"{label}: full canonical authority mismatch")


def json_pointer(value: Any, pointer: str, label: str) -> Any:
    require(isinstance(pointer, str) and pointer.startswith("/"),
            f"{label}: invalid JSON pointer")
    current = value
    for raw_token in pointer[1:].split("/"):
        token = raw_token.replace("~1", "/").replace("~0", "~")
        if isinstance(current, dict):
            require(token in current, f"{label}: missing object key {token!r}")
            current = current[token]
        elif isinstance(current, list):
            require(re.fullmatch(r"0|[1-9][0-9]*", token) is not None,
                    f"{label}: invalid list index {token!r}")
            position = int(token)
            require(position < len(current),
                    f"{label}: list index out of bounds: {position}")
            current = current[position]
        else:
            raise SystemExit(f"{label}: pointer traverses a scalar")
    return current


def promoted_payloads(
    root: Path,
    index: dict[str, Any],
    *,
    allow_evidence_path_fallback: bool,
) -> tuple[dict[str, bytes], list[dict[str, Any]]]:
    payload_by_registry_path: dict[str, bytes] = {}
    records: list[dict[str, Any]] = []
    for key, record in index["promotion_inputs"].items():
        path, fallback = resolve_record_path(
            root,
            record,
            allow_evidence_path_fallback=allow_evidence_path_fallback,
        )
        payload = verify_file_record(path, record, f"promotion input {key}")
        registry_path = str(record["registry_path"])
        require(registry_path not in payload_by_registry_path,
                f"duplicate promoted registry path: {registry_path}")
        payload_by_registry_path[registry_path] = payload
        records.append({
            "key": key,
            "registry_path": registry_path,
            "resolved_path": path.as_posix(),
            "runtime_path": record["runtime_path"],
            "used_evidence_path_fallback": fallback,
            "sha256": sha256(payload),
            "bytes": len(payload),
        })
    return payload_by_registry_path, records


def parse_promoted_json(
    payload_by_registry_path: dict[str, bytes],
    source: dict[str, Any],
    *,
    label: str,
) -> Any:
    source_path = str(source.get("path"))
    require(source_path in payload_by_registry_path,
            f"{label}: source path is not in the promotion map")
    payload = payload_by_registry_path[source_path]
    require(sha256(payload) == require_sha(source.get("sha256"), label),
            f"{label}: registry/source SHA mismatch")
    try:
        return json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SystemExit(f"{label}: invalid promoted JSON: {error}") from error


def extract_reduced_preview(payload: bytes, label: str) -> str:
    text = payload.decode("utf-8")
    require("\r" not in text, f"{label}: preview is not locked LF text")
    require(text.endswith("\n"), f"{label}: preview terminal LF missing")
    lines = text.splitlines(keepends=True)
    positions = [position for position, line in enumerate(lines) if line == "by\n"]
    require(len(positions) == 1,
            f"{label}: expected exactly one line equal to `by`")
    fragment = "".join(lines[positions[0]:])
    require(fragment.endswith("\n"), f"{label}: extracted terminal LF missing")
    return fragment[:-1]


def repair_from_group(
    group: dict[str, Any],
    payload_by_registry_path: dict[str, bytes],
) -> dict[str, Any]:
    key = str(group.get("group_key"))
    label = f"repair group {key}"
    require(key in GROUP_KEYS, f"{label}: unknown group key")
    require(group.get("repair_id") == REPAIR_ID_BY_GROUP[key],
            f"{label}: repair ID mismatch")
    fragment_source = group.get("fragment_source")
    require(isinstance(fragment_source, dict),
            f"{label}: fragment source missing")
    if "path" in fragment_source:
        producer = parse_promoted_json(
            payload_by_registry_path,
            fragment_source,
            label=f"{label} producer",
        )
        old = json_pointer(
            producer, str(fragment_source.get("old_json_pointer")),
            f"{label} old fragment",
        )
        new = json_pointer(
            producer, str(fragment_source.get("new_json_pointer")),
            f"{label} new fragment",
        )
    else:
        old_source = fragment_source.get("old")
        new_source = fragment_source.get("new")
        require(isinstance(old_source, dict) and isinstance(new_source, dict),
                f"{label}: split fragment sources missing")
        old_producer = parse_promoted_json(
            payload_by_registry_path,
            old_source,
            label=f"{label} old producer",
        )
        old = json_pointer(
            old_producer, str(old_source.get("json_pointer")),
            f"{label} old fragment",
        )
        new_path = str(new_source.get("path"))
        require(new_path in payload_by_registry_path,
                f"{label}: new preview is not in the promotion map")
        new_payload = payload_by_registry_path[new_path]
        require(sha256(new_payload) == require_sha(
            new_source.get("sha256"), f"{label} new preview"
        ), f"{label}: new preview SHA mismatch")
        require(
            new_source.get("extraction")
            == ("take from the first line exactly equal to `by` through EOF, "
                "then remove the single terminal LF"),
            f"{label}: unsupported preview extraction contract",
        )
        new = extract_reduced_preview(new_payload, f"{label} new preview")
    require(isinstance(old, str) and isinstance(new, str),
            f"{label}: resolved fragments are not strings")
    for side, fragment in (("old", old), ("new", new)):
        require(sha256(fragment.encode("utf-8")) == require_sha(
            group.get(f"{side}_sha256"), f"{label} {side} fragment"
        ), f"{label}: {side} fragment SHA mismatch")
        require(len(fragment.encode("utf-8")) == int(group[f"{side}_bytes"]),
                f"{label}: {side} fragment byte mismatch")
        require(len(fragment.splitlines()) == int(group[f"{side}_lines"]),
                f"{label}: {side} fragment line mismatch")
        require(max_heartbeat_counts(fragment)
                == {"token_count": 0, "set_option_count": 0},
                f"{label}: {side} fragment contains maxHeartbeats")
    repair = {
        "id": group["repair_id"],
        "group_key": key,
        "owner": group["owner"],
        "declaration_index": group["declaration_index"],
        "kind": "body",
        "old": old,
        "new": new,
        "old_sha256": group["old_sha256"],
        "old_bytes": group["old_bytes"],
        "new_sha256": group["new_sha256"],
        "new_bytes": group["new_bytes"],
        "expected_count_in_owner": group["expected_owner_old_count"],
        "expected_global_count": group["expected_global_old_count"],
        "expected_global_new_count_before": group[
            "expected_global_new_count_before"
        ],
        "owner_header_sha256": group["owner_header_sha256"],
        "owner_header_line": group["owner_header_line"],
        "owner_region_sha256": group["owner_region_sha256"],
        "owner_region_bytes": group["owner_region_bytes"],
        "owner_region_byte_span_half_open": group[
            "owner_region_byte_span_half_open"
        ],
        "transform_dependencies": group.get("transform_dependencies", []),
    }
    validate_repair(repair, label)
    return repair


def load_normalized_repairs(
    root: Path,
    index: dict[str, Any],
    *,
    allow_evidence_path_fallback: bool,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    registry_record = index["repair_registry"]
    registry_path, registry_fallback = resolve_record_path(
        root,
        registry_record,
        allow_evidence_path_fallback=allow_evidence_path_fallback,
    )
    registry_payload = verify_file_record(
        registry_path, registry_record, "normalized repair registry"
    )
    registry = json.loads(registry_payload)
    require(registry.get("schema") == registry_record.get("schema"),
            "normalized repair registry schema mismatch")
    require(registry.get("status") == registry_record.get("payload_status"),
            "normalized repair registry payload status mismatch")
    verify_manifest_authority(
        registry.get("authority"), "normalized repair registry"
    )
    require(registry.get("direct_lean_verified") is False,
            "normalized registry claims direct Lean verification")
    require(registry.get("clean_build_claimed") is False,
            "normalized registry claims a clean build")
    groups = registry.get("groups")
    require(isinstance(groups, list), "normalized repair groups must be a list")
    require([group.get("group_key") for group in groups] == list(GROUP_KEYS),
            "normalized repair group key/order mismatch")
    require(len({group.get("repair_id") for group in groups}) == len(GROUP_KEYS),
            "normalized repair IDs are not unique")

    payload_by_registry_path, promoted_records = promoted_payloads(
        root,
        index,
        allow_evidence_path_fallback=allow_evidence_path_fallback,
    )
    source_locks = registry.get("source_package_locks")
    require(isinstance(source_locks, list),
            "normalized registry source-package locks missing")
    observed_source_locks = [
        {
            "path": lock.get("path"),
            "sha256": lock.get("sha256"),
            "bytes": lock.get("bytes"),
        }
        for lock in source_locks
    ]
    expected_source_locks = [
        {
            "path": record["registry_path"],
            "sha256": record["sha256"],
            "bytes": record["bytes"],
        }
        for record in PROMOTION_INPUTS.values()
    ]
    require(observed_source_locks == expected_source_locks,
            "normalized registry source-package lock/order mismatch")

    repairs_by_group = {
        group["group_key"]: repair_from_group(group, payload_by_registry_path)
        for group in groups
    }
    require(tuple(repairs_by_group) == GROUP_KEYS,
            "resolved repair group order mismatch")
    excluded = registry.get("excluded_serial_idx4018_fallbacks")
    require(isinstance(excluded, list) and len(excluded) == 2,
            "idx4018 serial fallback exclusion list mismatch")
    require(
        [row.get("repair_id") for row in excluded]
        == [
            "V58-IDX4018-P02-EXPLICIT-TWO-LEVEL-CLM-EXT",
            "V58-IDX4018-P03-TYPED-INNER-CONGRARG",
        ]
        and all(row.get("standalone_selection_forbidden") is True
                for row in excluded),
        "idx4018 P02/P03 exclusion contract mismatch",
    )
    evidence = {
        "path": registry_path.as_posix(),
        "runtime_path": registry_record["runtime_path"],
        "used_evidence_path_fallback": registry_fallback,
        "sha256": sha256(registry_payload),
        "bytes": len(registry_payload),
        "schema": registry["schema"],
        "payload_status": registry["status"],
        "group_order": list(repairs_by_group),
        "repair_ids": [repairs_by_group[key]["id"] for key in GROUP_KEYS],
        "promotion_inputs": promoted_records,
        "idx4018_serial_p02_p03_excluded": True,
    }
    return repairs_by_group, evidence


def load_matrix_cross_audit(
    root: Path,
    index: dict[str, Any],
    repairs_by_group: dict[str, dict[str, Any]],
    *,
    allow_evidence_path_fallback: bool,
) -> dict[str, Any]:
    record = index["matrix_cross_audit"]
    path, fallback = resolve_record_path(
        root,
        record,
        allow_evidence_path_fallback=allow_evidence_path_fallback,
    )
    payload = verify_file_record(path, record, "variant matrix cross-audit")
    matrix = json.loads(payload)
    require(matrix.get("schema") == record.get("schema"),
            "variant matrix cross-audit schema mismatch")
    require(matrix.get("status") == record.get("payload_status"),
            "variant matrix cross-audit payload status mismatch")
    verify_manifest_authority(matrix.get("authority"), "variant matrix cross-audit")
    require(matrix.get("recommended_execution_order") == list(VARIANT_ORDER),
            "variant matrix execution order mismatch")
    common = matrix.get("common_static_postconditions")
    require(isinstance(common, dict), "matrix common postconditions missing")
    require(common.get("declaration_count") == DECLARATION_COUNT,
            "matrix declaration-count postcondition mismatch")
    require(common.get("declaration_name_order_identical") is True,
            "matrix declaration-order postcondition missing")
    require(common.get("all_raw_declaration_headers_byte_identical") is True,
            "matrix header postcondition missing")
    require(common.get("comments_identical") is True
            and common.get("attributes_identical") is True,
            "matrix comment/attribute postcondition missing")
    require(common.get("trust_counts") == {token: 0 for token in TRUST_TOKENS},
            "matrix trust-six postcondition mismatch")
    require(common.get("maxHeartbeats_token_count")
            == MAX_HEARTBEAT_COUNTS["token_count"],
            "matrix maxHeartbeats token-count mismatch")
    require(common.get("set_option_maxHeartbeats_count")
            == MAX_HEARTBEAT_COUNTS["set_option_count"],
            "matrix maxHeartbeats option-count mismatch")
    variants = matrix.get("variants")
    require(isinstance(variants, list), "matrix variant rows missing")
    require([row.get("variant_id") for row in variants] == list(VARIANT_ORDER),
            "matrix variant row order mismatch")
    for row in variants:
        variant = row["variant_id"]
        keys = list(ALLOWED_SELECTION_MAP[variant])
        repair_ids = [REPAIR_ID_BY_GROUP[key] for key in keys]
        declaration_indices = [
            int(repairs_by_group[key]["declaration_index"]) for key in keys
        ]
        expected = EXPECTED_CANDIDATES[variant]
        require(row.get("group_keys_in_application_order") == keys,
                f"matrix {variant}: group selection mismatch")
        require(row.get("repair_ids_in_application_order") == repair_ids,
                f"matrix {variant}: repair ID/order mismatch")
        require(row.get("declaration_indices_in_application_order")
                == declaration_indices,
                f"matrix {variant}: declaration index/order mismatch")
        require({
            "sha256": row.get("candidate_sha256"),
            "bytes": row.get("candidate_bytes"),
            "lines": row.get("candidate_lines"),
        } == expected, f"matrix {variant}: candidate identity mismatch")
        require(row.get("static_postconditions_match_common") is True,
                f"matrix {variant}: static postconditions are not locked")
        require(row.get("ready_for_direct_lean_probe") is True,
                f"matrix {variant}: direct probe readiness missing")
        require(row.get("promotion_ready") is False,
                f"matrix {variant}: unsupported promotion claim")
    require(matrix.get("direct_lean_verified") is False,
            "matrix claims direct Lean verification")
    require(matrix.get("clean_build_claimed") is False,
            "matrix claims a clean build")
    require(matrix.get("promotion_ready") is False,
            "matrix claims promotion readiness")
    return {
        "path": path.as_posix(),
        "runtime_path": record["runtime_path"],
        "used_evidence_path_fallback": fallback,
        "sha256": sha256(payload),
        "bytes": len(payload),
        "schema": matrix["schema"],
        "payload_status": matrix["status"],
        "variant_order": list(VARIANT_ORDER),
        "candidate_locks_reconciled": True,
        "direct_lean_verified": False,
    }


def validate_repair(repair: dict[str, Any], label: str) -> None:
    for key in ("id", "owner", "declaration_index", "old", "new"):
        require(key in repair, f"{label}: repair field missing: {key}")
    require(repair.get("kind") == "body", f"{label}: only body repairs allowed")
    old = repair["old"]
    new = repair["new"]
    require(isinstance(old, str) and isinstance(new, str),
            f"{label}: fragments must be strings")
    require(old and old != new, f"{label}: empty or no-op fragment")
    require("\r" not in old and "\r" not in new,
            f"{label}: fragments must use locked LF newlines")
    require(sha256(old.encode("utf-8")) == require_sha(
        repair.get("old_sha256"), f"{label} old fragment"
    ), f"{label}: old fragment SHA mismatch")
    require(sha256(new.encode("utf-8")) == require_sha(
        repair.get("new_sha256"), f"{label} new fragment"
    ), f"{label}: new fragment SHA mismatch")
    require(len(old.encode("utf-8")) == int(repair.get("old_bytes", -1)),
            f"{label}: old fragment byte mismatch")
    require(len(new.encode("utf-8")) == int(repair.get("new_bytes", -1)),
            f"{label}: new fragment byte mismatch")
    require(int(repair.get("expected_count_in_owner", 1)) > 0,
            f"{label}: invalid owner count")
    require(not any(line.startswith(("+", "-")) for line in new.splitlines()),
            f"{label}: diff-prefix contamination")
    zero_heartbeat = {"token_count": 0, "set_option_count": 0}
    require(max_heartbeat_counts(old) == zero_heartbeat,
            f"{label}: OLD fragment contains maxHeartbeats")
    require(max_heartbeat_counts(new) == zero_heartbeat,
            f"{label}: NEW fragment contains maxHeartbeats")


def validate_authority_owner_lock(text: str, repair: dict[str, Any]) -> None:
    declaration_regions = regions(text)
    declaration_index = int(repair["declaration_index"])
    require(0 <= declaration_index < len(declaration_regions),
            f"{repair['id']}: authority declaration index out of range")
    owner = declaration_regions[declaration_index]
    require(owner["name"] == repair["owner"],
            f"{repair['id']}: authority owner mismatch")
    block = text[owner["start"] : owner["end"]]
    header_line = text.count("\n", 0, owner["start"]) + 1
    require(header_line == int(repair["owner_header_line"]),
            f"{repair['id']}: authority owner header line mismatch")
    byte_start = len(text[: owner["start"]].encode("utf-8"))
    byte_end = byte_start + len(block.encode("utf-8"))
    require([byte_start, byte_end] == repair["owner_region_byte_span_half_open"],
            f"{repair['id']}: authority owner byte-span mismatch")
    require(sha256(block.encode("utf-8")) == repair["owner_region_sha256"],
            f"{repair['id']}: authority owner region SHA mismatch")
    require(len(block.encode("utf-8")) == int(repair["owner_region_bytes"]),
            f"{repair['id']}: authority owner region byte mismatch")
    header = dict(raw_headers(text))[owner["name"]]
    require(sha256(header.encode("utf-8")) == repair["owner_header_sha256"],
            f"{repair['id']}: authority owner header SHA mismatch")


def replace_in_owner(
    text: str, repair: dict[str, Any]
) -> tuple[str, dict[str, Any]]:
    declaration_regions = regions(text)
    declaration_index = int(repair["declaration_index"])
    require(0 <= declaration_index < len(declaration_regions),
            f"{repair['id']}: declaration index out of range")
    owner = declaration_regions[declaration_index]
    require(owner["name"] == repair["owner"],
            f"{repair['id']}: owner mismatch at index {declaration_index}")
    block = text[owner["start"] : owner["end"]]
    if "owner_region_sha256" in repair:
        require(sha256(block.encode("utf-8")) == repair["owner_region_sha256"],
                f"{repair['id']}: owner region SHA mismatch")
        require(len(block.encode("utf-8")) == int(repair["owner_region_bytes"]),
                f"{repair['id']}: owner region byte mismatch")
    if "owner_header_sha256" in repair:
        header = dict(raw_headers(text))[owner["name"]]
        require(sha256(header.encode("utf-8")) == repair["owner_header_sha256"],
                f"{repair['id']}: owner header SHA mismatch")
    old = repair["old"]
    new = repair["new"]
    expected_owner = int(repair.get("expected_count_in_owner", 1))
    owner_count = block.count(old)
    global_count = text.count(old)
    require(owner_count == expected_owner,
            f"{repair['id']}: owner-local old count {owner_count} != {expected_owner}")
    if "expected_global_count" in repair:
        require(global_count == int(repair["expected_global_count"]),
                f"{repair['id']}: global old count mismatch")
    if "expected_global_new_count_before" in repair:
        require(text.count(new)
                == int(repair["expected_global_new_count_before"]),
                f"{repair['id']}: global new count-before mismatch")
    first_occurrence = block.find(old)
    cuts = [point for point in (
        block.find(":= by"), block.find(":="), block.find(" where\n")
    ) if point >= 0]
    require(cuts and first_occurrence > min(cuts),
            f"{repair['id']}: replacement is not strictly body-local")
    replaced = block.replace(old, new)
    require(replaced.count(old) == 0,
            f"{repair['id']}: old fragment remains in owner")
    result = text[: owner["start"]] + replaced + text[owner["end"] :]
    return result, {
        "id": repair["id"],
        "owner": repair["owner"],
        "declaration_index": declaration_index,
        "owner_old_count": owner_count,
        "global_old_count": global_count,
        "old_sha256": repair["old_sha256"],
        "new_sha256": repair["new_sha256"],
        "changed_region_maxHeartbeats_before": max_heartbeat_counts(old),
        "changed_region_maxHeartbeats_after": max_heartbeat_counts(new),
    }


def atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".v59-tmp")
    require(not temporary.exists(), f"temporary output already exists: {temporary}")
    temporary.write_bytes(payload)
    os.replace(temporary, path)


def materialize(
    args: argparse.Namespace,
    root: Path,
    index_payload: bytes,
    index: dict[str, Any],
) -> int:
    require(args.variant in VARIANT_ORDER, f"unknown variant: {args.variant}")
    require(not args.allow_evidence_path_fallback,
            "READY materialization forbids evidence-path fallback")
    destinations = (args.output, args.audit, args.evidence)
    require(all(path is not None for path in destinations),
            "output, audit, and evidence paths are required")
    resolved_destinations = [Path(path).resolve() for path in destinations]
    require(len(set(resolved_destinations)) == 3,
            "output, audit, and evidence paths must be distinct")
    for path in resolved_destinations:
        require(not path.exists(), f"refusing to overwrite existing output: {path}")

    authority_path = Path(args.authority_source)
    authority_payload = authority_path.read_bytes()
    require(sha256(authority_payload) == AUTHORITY["source_sha256"],
            "authority source SHA mismatch")
    require(len(authority_payload) == AUTHORITY["source_bytes"],
            "authority source byte mismatch")
    source = authority_payload.decode("utf-8")
    require(len(source.splitlines()) == AUTHORITY["source_lines"],
            "authority source line mismatch")
    before_regions = regions(source)
    require(len(before_regions) == DECLARATION_COUNT,
            "authority declaration count mismatch")
    before_names = [row["name"] for row in before_regions]
    before_headers = raw_headers(source)
    before_comments, before_attributes = comments_and_attributes(source)
    before_trust = trust_counts(source)
    require(all(value == 0 for value in before_trust.values()),
            f"authority executable trust-six nonzero: {before_trust}")
    before_heartbeats = max_heartbeat_counts(source)
    require(before_heartbeats == MAX_HEARTBEAT_COUNTS,
            f"authority maxHeartbeats count mismatch: {before_heartbeats}")

    variant = next(row for row in index["variants"] if row["name"] == args.variant)
    repairs_by_group, registry_evidence = load_normalized_repairs(
        root,
        index,
        allow_evidence_path_fallback=False,
    )
    matrix_evidence = load_matrix_cross_audit(
        root,
        index,
        repairs_by_group,
        allow_evidence_path_fallback=False,
    )
    selected_group_keys = variant["selected_group_keys"]
    require(selected_group_keys == list(ALLOWED_SELECTION_MAP[args.variant]),
            "variant selection differs from exact allowed group map")
    require(len(selected_group_keys) == len(set(selected_group_keys)),
            "duplicate selected repair group")
    repairs = [repairs_by_group[key] for key in selected_group_keys]

    repair_ids = [repair["id"] for repair in repairs]
    require(repair_ids == variant["selected_repair_ids"],
            "variant repair order differs from exact group selection")
    declaration_indices = [int(repair["declaration_index"]) for repair in repairs]
    require(declaration_indices == sorted(set(declaration_indices)),
            "variant repairs are not unique and strictly source-ordered")
    for repair in repairs:
        require(set(repair["transform_dependencies"]) <= set(selected_group_keys),
                f"{repair['id']}: missing transform dependency")
        validate_authority_owner_lock(source, repair)

    current = source
    applied: list[dict[str, Any]] = []
    for repair in repairs:
        current, record = replace_in_owner(current, repair)
        applied.append(record)

    after_regions = regions(current)
    after_names = [row["name"] for row in after_regions]
    after_headers = raw_headers(current)
    after_comments, after_attributes = comments_and_attributes(current)
    after_trust = trust_counts(current)
    after_heartbeats = max_heartbeat_counts(current)
    require(after_names == before_names, "declaration sequence changed")
    require(after_headers == before_headers, "declaration headers changed")
    require(after_comments == before_comments, "comments changed")
    require(after_attributes == before_attributes, "attributes changed")
    require(after_trust == before_trust and all(value == 0 for value in after_trust.values()),
            f"executable trust-six changed: {before_trust} -> {after_trust}")
    require(after_heartbeats == before_heartbeats == MAX_HEARTBEAT_COUNTS,
            f"global maxHeartbeats changed: {before_heartbeats} -> {after_heartbeats}")
    require(len(after_regions) == DECLARATION_COUNT,
            "candidate declaration count mismatch")

    candidate_payload = current.encode("utf-8")
    expected = variant["expected_candidate"]
    require(sha256(candidate_payload) == require_sha(
        expected["sha256"], f"variant {args.variant} candidate"
    ), "candidate SHA mismatch")
    require(len(candidate_payload) == int(expected["bytes"]),
            "candidate byte mismatch")
    require(len(current.splitlines()) == int(expected["lines"]),
            "candidate line mismatch")

    index_sha = sha256(index_payload)
    output_status = "STATIC_PASS_RUNTIME_PROMOTION_LOCKS_DIRECT_LEAN_UNVERIFIED"
    changed_region_heartbeats_before = {
        "token_count": sum(
            row["changed_region_maxHeartbeats_before"]["token_count"]
            for row in applied
        ),
        "set_option_count": sum(
            row["changed_region_maxHeartbeats_before"]["set_option_count"]
            for row in applied
        ),
    }
    changed_region_heartbeats_after = {
        "token_count": sum(
            row["changed_region_maxHeartbeats_after"]["token_count"]
            for row in applied
        ),
        "set_option_count": sum(
            row["changed_region_maxHeartbeats_after"]["set_option_count"]
            for row in applied
        ),
    }
    require(changed_region_heartbeats_before
            == changed_region_heartbeats_after
            == {"token_count": 0, "set_option_count": 0},
            "changed-region maxHeartbeats count is nonzero")
    audit = {
        "schema": AUDIT_SCHEMA,
        "status": output_status,
        "variant": args.variant,
        "selection_index_sha256": index_sha,
        "authority": AUTHORITY,
        "authority_source_path": authority_path.as_posix(),
        "authority_source_sha256": sha256(authority_payload),
        "normalized_repair_registry": registry_evidence,
        "matrix_cross_audit": matrix_evidence,
        "selected_group_keys": selected_group_keys,
        "selected_repair_ids": repair_ids,
        "selected_repair_count": len(repairs),
        "selected_owner_count": len({repair["owner"] for repair in repairs}),
        "applied": applied,
        "candidate_sha256": sha256(candidate_payload),
        "candidate_bytes": len(candidate_payload),
        "candidate_lines": len(current.splitlines()),
        "declaration_count": len(after_regions),
        "declaration_sequence_identical": True,
        "all_declaration_headers_byte_identical": True,
        "theorem_statements_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "source_moves": [],
        "helpers_added": 0,
        "diff_prefix_contamination_rejected": True,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "global_maxHeartbeats_before": before_heartbeats,
        "global_maxHeartbeats_after": after_heartbeats,
        "changed_region_maxHeartbeats_before": changed_region_heartbeats_before,
        "changed_region_maxHeartbeats_after": changed_region_heartbeats_after,
        "runtime_evidence_fallback_used": False,
        "direct_lean_verified": False,
        "lean_lake_git_github_network_invoked": False,
    }
    audit_payload = canonical(audit)
    evidence = {
        "schema": EVIDENCE_SCHEMA,
        "status": output_status,
        "variant": args.variant,
        "selection_index_sha256": index_sha,
        "selection_index_bytes": len(index_payload),
        "composer_materializer_sha256": sha256(Path(__file__).resolve().read_bytes()),
        "authority": AUTHORITY,
        "authority_source_sha256": sha256(authority_payload),
        "normalized_repair_registry": registry_evidence,
        "matrix_cross_audit": matrix_evidence,
        "selected_group_keys": selected_group_keys,
        "selected_repair_count": len(repairs),
        "selected_owner_count": audit["selected_owner_count"],
        "candidate_sha256": sha256(candidate_payload),
        "candidate_bytes": len(candidate_payload),
        "candidate_lines": len(current.splitlines()),
        "audit_sha256": sha256(audit_payload),
        "audit_bytes": len(audit_payload),
        "declaration_count": DECLARATION_COUNT,
        "headers_comments_attributes_preserved": True,
        "source_moves": [],
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "global_maxHeartbeats_before": before_heartbeats,
        "global_maxHeartbeats_after": after_heartbeats,
        "changed_region_maxHeartbeats_before": changed_region_heartbeats_before,
        "changed_region_maxHeartbeats_after": changed_region_heartbeats_after,
        "runtime_evidence_fallback_used": False,
        "direct_lean_verified": False,
        "lean_lake_git_github_network_invoked_by_materializer": False,
    }
    evidence_payload = canonical(evidence)
    for path, payload in zip(
        resolved_destinations,
        (candidate_payload, audit_payload, evidence_payload),
        strict=True,
    ):
        atomic_write(path, payload)
    print(evidence_payload.decode("utf-8"), end="")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--expected-index-sha256", required=True)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--variant")
    parser.add_argument("--authority-source", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--audit", type=Path)
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--validate-pending-index", action="store_true")
    parser.add_argument("--allow-evidence-path-fallback", action="store_true")
    args = parser.parse_args()

    root = args.repo_root.resolve()
    index_payload, index = load_json_bytes(args.index)
    expected_index = require_sha(args.expected_index_sha256, "selection index")
    require(sha256(index_payload) == expected_index, "selection index SHA mismatch")
    validation = validate_common_index(
        index,
        index_payload,
        root,
        allow_evidence_path_fallback=args.allow_evidence_path_fallback,
    )
    if index.get("status") != READY_STATUS:
        validate_pending_index(index)
        if args.validate_pending_index:
            validation["status"] = "PENDING_SCAFFOLD_VALIDATED_FAIL_CLOSED"
            validation["activation"] = index["activation"]
            validation["pending_inputs"] = index["pending_inputs"]
            print(canonical(validation).decode("utf-8"), end="")
            return 0
        print("v59 selection is pending; refusing materialization", file=sys.stderr)
        return EXIT_PENDING

    require(not args.validate_pending_index,
            "pending-only validation flag is forbidden for READY selection")
    require(not args.allow_evidence_path_fallback,
            "READY selection forbids evidence-path fallback")
    validate_ready_index(index)
    require(args.variant is not None, "variant is required")
    require(args.authority_source is not None, "authority source is required")
    return materialize(args, root, index_payload, index)


if __name__ == "__main__":
    raise SystemExit(main())
