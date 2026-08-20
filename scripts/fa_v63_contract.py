#!/usr/bin/env python3
"""Shared fail-closed contract for the v63 noncumulative direct matrix.

The public READY loader deliberately examines the selection status before it
opens authority or manifest inputs.  A missing or PENDING selection therefore
returns the distinguished pending condition and cannot fall back to workspace
or artifact-local metadata.  Static scaffold validation is a separate,
read-only operation and never authorizes materialization or compilation.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path, PurePosixPath
from typing import Any


SELECTION_SCHEMA = "fa-v63-direct-bounded-selection-v1"
MANIFEST_SCHEMA = "fa-v63-body-only-repair-manifest-v1"
AUTHORITY_SCHEMA = "fa-v63-v62-winner-authority-lock-v1"
SOURCE_SHA256 = "1badac1451e11708114eb5438616063379558bcf0579dc82a01c2200b501d365"
SOURCE_BYTES = 2812442
SOURCE_LINES = 62933
DECLARATION_COUNT = 4416
READY_INDEX_SHA256 = "8a7f65766baf2d20713b7cfa29c7edbb0a5cff0d670256adebfb57646ce2ab51"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
TRUST_TOKENS = (
    "sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool",
)

# A successful v63 lane has one exact, flat 48-member result artifact.  Six
# members are immutable copies from the re-proved v62 authority ZIP; the other
# 42 describe the current v63 candidate and direct execution.  Keeping the
# authority ZIP inventory (also 48 members) separate from this result inventory
# avoids silently treating two different 48-member contracts as interchangeable.
BASE_AUTHORITY_COPIES = (
    ("BASE_FINAL_GATE.json", "FINAL_GATE.json"),
    ("BASE_FULL_DIAGNOSTICS.json", "FULL_DIAGNOSTICS.json"),
    ("BASE_MATERIALIZATION.json", "MATERIALIZATION.json"),
    ("BASE_Mock2_FunctionalAnalysis-candidate.lean",
     "Mock2_FunctionalAnalysis-candidate.lean"),
    ("BASE_Mock2_FunctionalAnalysis.log", "Mock2_FunctionalAnalysis.log"),
    ("BASE_TOOLCHAIN_PIN.json", "TOOLCHAIN_PIN.json"),
)

RESULT_ARTIFACT_MEMBERS = tuple(sorted({
    "AUTHORITY_REPROOF.json",
    "AUTHORITY_REPROOF.stdout.json",
    *(result for result, _ in BASE_AUTHORITY_COPIES),
    "COLLECTOR_AUTHORITY_ATTESTATION.json",
    "DIAGNOSTIC_DECLARATION_COUNTS.json",
    "FINAL_GATE.json",
    "FINAL_GATE.stdout.json",
    "FULL_DIAGNOSTICS.json",
    "FULL_WARNINGS.json",
    "MATERIALIZATION.json",
    "MATERIALIZATION.stdout.json",
    "METRIC.json",
    "Mock2.command",
    "Mock2.executed",
    "Mock2.exit",
    "Mock2.log",
    "Mock2_Advanced.command",
    "Mock2_Advanced.executed",
    "Mock2_Advanced.exit",
    "Mock2_Advanced.log",
    "Mock2_FunctionalAnalysis-candidate.lean",
    "Mock2_FunctionalAnalysis-observed.lean",
    "Mock2_FunctionalAnalysis.command",
    "Mock2_FunctionalAnalysis.executed",
    "Mock2_FunctionalAnalysis.exit",
    "Mock2_FunctionalAnalysis.log",
    "PATCH_AUDIT.json",
    "SCAFFOLD_GATE.json",
    "SYNTHETIC_SORRY_WARNINGS.json",
    "TOOLCHAIN_PIN.json",
    "V61_ARTIFACT.json",
    "V61_JOBS.json",
    "V61_RUN.json",
    "VARIANT_INDEX.json",
    "cache.log",
    "candidate.after.sha256",
    "candidate.before-fa.sha256",
    "candidate.before.sha256",
    "candidate.sha256",
    "elan.log",
    "lean-version.txt",
    "metric-console.log",
    "toolchain.log",
}))

INDEPENDENT_CROSS_AUDIT_FILES = {
    "audit": (
        "work/v63-cross-audit/audit.json",
        "fa-v63-independent-cross-audit-v1",
        "9a7c3c1be73630b2bc75d78954bf811154a95d03a8ccf64ded46c4e50c631cd9",
        99593,
    ),
    "candidate_registry": (
        "work/v63-cross-audit/candidate-registry.json",
        "fa-v63-independent-candidate-registry-v1",
        "f246fe711f54fa695497c5dc66c5fd321c7dee2d4c3e6aac33e0ecbabcf05ca3",
        32979,
    ),
    "matrix_lock": (
        "work/v63-cross-audit/matrix-lock.json",
        "fa-v63-independent-11-lane-matrix-lock-v1",
        "5f0abeebf12688c3385f40614e5b670b3b030f4e45f89a2c42e884432c47b90d",
        22014,
    ),
}

F30 = "V63-F3930-PI-NEG-APPLY-RING"
F33G = "V63-F3933-PROGRESSION"
F33E = "V63-F3933-EXPLICIT-CANCEL"
F33T = "V63-F3933-FIELDSIMP"
W17R = "V63-W4017-R17-BASE"
W17P = "V63-W4017-P"
W17Z = "V63-W4017-Z"
W17W = "V63-W4017-W"

VARIANT_ORDER = [
    "core",
    "f3930",
    "f3933_preferred",
    "f3933_fallback",
    "f3930_f3933_preferred",
    "f3930_f3933_fallback",
    "w4017_p",
    "w4017_pz",
    "w4017_pw",
    "w4017_full",
    "combined_best",
]

VARIANT_REPAIRS = {
    "core": [],
    "f3930": [F30],
    "f3933_preferred": [F33G, F33E],
    "f3933_fallback": [F33G, F33T],
    "f3930_f3933_preferred": [F30, F33G, F33E],
    "f3930_f3933_fallback": [F30, F33G, F33T],
    "w4017_p": [W17R, W17P],
    "w4017_pz": [W17R, W17P, W17Z],
    "w4017_pw": [W17R, W17P, W17W],
    "w4017_full": [W17R, W17P, W17Z, W17W],
    "combined_best": [F30, F33G, F33E, W17R, W17P, W17Z, W17W],
}

VARIANT_ROOTS = {
    "core": [],
    "f3930": ["F3930"],
    "f3933_preferred": ["F3933"],
    "f3933_fallback": ["F3933"],
    "f3930_f3933_preferred": ["F3930", "F3933"],
    "f3930_f3933_fallback": ["F3930", "F3933"],
    "w4017_p": ["W4017-BOUNDARY", "W4017-TYPECLASS"],
    "w4017_pz": ["W4017-BOUNDARY", "W4017-TYPECLASS", "W4017-ZERO-WEIGHT"],
    "w4017_pw": ["W4017-BOUNDARY", "W4017-POINTWISE-SMUL", "W4017-TYPECLASS"],
    "w4017_full": [
        "W4017-BOUNDARY", "W4017-POINTWISE-SMUL", "W4017-TYPECLASS",
        "W4017-ZERO-WEIGHT",
    ],
    "combined_best": [
        "F3930", "F3933", "W4017-BOUNDARY", "W4017-POINTWISE-SMUL",
        "W4017-TYPECLASS", "W4017-ZERO-WEIGHT",
    ],
}

VARIANT_LOCKS = {
    "core": (SOURCE_SHA256, SOURCE_BYTES, SOURCE_LINES),
    "f3930": ("9f57a361ce5ae99cbcaca5e7c4a4a8eb3eafbbbed69b79568a0347130d304de8", 2812421, 62934),
    "f3933_preferred": ("2ae97aea7e838b08b4951ac499a5591d1e8eca87233b65863e92ec330f6aef7a", 2813475, 62955),
    "f3933_fallback": ("059c988b4cdc3c67983ee38f270a2dcc907b97a24862dc7d723f2a2a61d00efe", 2813077, 62946),
    "f3930_f3933_preferred": ("90e85b036bc61627270afca3105f03b088779af0a0e7a503fb872a1957ffb42b", 2813454, 62956),
    "f3930_f3933_fallback": ("0b58272e04b80d84047edb9641a61d36ca6fbbb3d787e8139346b4e41eeb6101", 2813056, 62947),
    "w4017_p": ("ee4fd072acbded035aeb7cf81a49db1a14f73a2f9f4ad5baab623a32f8cb0e2d", 2812938, 62943),
    "w4017_pz": ("d0ddccad25b3173ade4b9fd8600c5ee3b90e747a35171e83391f55703cdafde0", 2812951, 62944),
    "w4017_pw": ("1abcc43c7416538a9b3ab470abecaa31410e4a82b86101bc60e452c98de64435", 2813008, 62943),
    "w4017_full": ("20ad5b01e774f1c388d2d16991e34840fdafe0f9d033038652311b29d84ae3f5", 2813021, 62944),
    "combined_best": ("07e698419184a58b0e99bf8e6b3900782cb4a83b1471ab79ba7d4f45240068e6", 2814033, 62967),
}

MANIFEST_RECORDS = {
    "f3930": (
        "scripts/fa_v63_f3930-manifest.json",
        "work/v63-ci/fa_v63_f3930-manifest.READY.json",
        "cd408eeeab5be791525fc6d24b1402577e95830243c64a0c36edbcbca19e64c5",
        3114,
        [F30],
    ),
    "f3933": (
        "scripts/fa_v63_f3933-manifest.json",
        "work/v63-ci/fa_v63_f3933-manifest.READY.json",
        "b95091f2140afaf36e60e26b4b09b482d32b4cd7d409751e8859384fcfca03ce",
        8647,
        [F33G, F33E, F33T],
    ),
    "w4017": (
        "scripts/fa_v63_w4017-manifest.json",
        "work/v63-ci/fa_v63_w4017-manifest.READY.json",
        "0285c92f68d6c4222105dfcb6c8c4483cf4f87cf67832fe9ae076698a7cae01f",
        11395,
        [W17R, W17P, W17Z, W17W],
    ),
}

REPAIR_METADATA = {
    F30: (0, 0, [], [], 3930, "inner_planeWave_ambientTestCore_eq_scale_mul_mFourierCoeff", "38d3843c45871a6218e9b2857967181b20ba6c7de71bce9b82cadc5e9909fe6d", ["F3930"]),
    F33G: (10, 0, [], [], 3933, "inner_literalStagePlaneWave", "74b180d55166924f3fe81667c8e1c578a0852dccf65dbc23cd1c227596b4d6f9", ["F3933"]),
    F33E: (11, 1, [F33G], [F33T], 3933, "inner_literalStagePlaneWave", "74b180d55166924f3fe81667c8e1c578a0852dccf65dbc23cd1c227596b4d6f9", ["F3933"]),
    F33T: (12, 1, [F33G], [F33E], 3933, "inner_literalStagePlaneWave", "74b180d55166924f3fe81667c8e1c578a0852dccf65dbc23cd1c227596b4d6f9", ["F3933"]),
    W17R: (20, 0, [], [], 4017, "discriminantHardStageOperator_eq_weightedHard", "cec5e99e9ca1e3b9ad8f2374ac985284f80dfcccac09bbae48106a7b40606f6d", ["W4017-BOUNDARY"]),
    W17P: (21, 1, [W17R], [], 4017, "discriminantHardStageOperator_eq_weightedHard", "cec5e99e9ca1e3b9ad8f2374ac985284f80dfcccac09bbae48106a7b40606f6d", ["W4017-TYPECLASS"]),
    W17Z: (22, 2, [W17P], [], 4017, "discriminantHardStageOperator_eq_weightedHard", "cec5e99e9ca1e3b9ad8f2374ac985284f80dfcccac09bbae48106a7b40606f6d", ["W4017-ZERO-WEIGHT"]),
    W17W: (23, 2, [W17P], [], 4017, "discriminantHardStageOperator_eq_weightedHard", "cec5e99e9ca1e3b9ad8f2374ac985284f80dfcccac09bbae48106a7b40606f6d", ["W4017-POINTWISE-SMUL"]),
}


class PendingInput(RuntimeError):
    """A required selection is missing or intentionally not activated."""


class ContractError(RuntimeError):
    """A present input violates an exact fail-closed lock."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def read_json(path: Path, *, pending_if_missing: bool = False) -> tuple[dict[str, Any], bytes]:
    if not path.is_file():
        if pending_if_missing:
            raise PendingInput(f"missing PENDING input: {path}")
        raise ContractError(f"missing required input: {path}")
    payload = path.read_bytes()
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"invalid JSON in {path}: {exc}") from exc
    require(isinstance(value, dict), f"JSON root must be object: {path}")
    return value, payload


def contains_pending(value: Any) -> bool:
    if isinstance(value, str):
        return value == "PENDING" or value.startswith("PENDING_")
    if isinstance(value, list):
        return any(contains_pending(item) for item in value)
    if isinstance(value, dict):
        return any(contains_pending(item) for item in value.values())
    return False


def exact_keys(value: Any, expected: set[str], label: str) -> dict[str, Any]:
    require(isinstance(value, dict), f"{label} must be object")
    require(set(value) == expected, f"{label} key set mismatch")
    return value


def exact_runtime_path(value: Any, repo_root: Path, expected: str) -> Path:
    require(value == expected, f"runtime path mismatch: {value!r}")
    pure = PurePosixPath(expected)
    require(not pure.is_absolute() and ".." not in pure.parts and "." not in pure.parts,
            f"unsafe runtime path: {expected}")
    require(len(pure.parts) == 2 and pure.parts[0] == "scripts"
            and pure.parts[1].startswith("fa_v63_"),
            f"runtime path outside scripts/fa_v63_*: {expected}")
    root = repo_root.resolve()
    path = (root / Path(*pure.parts)).resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise ContractError(f"runtime path escapes repository: {expected}") from exc
    return path


def exact_static_path(value: Any, repo_root: Path, expected: str) -> Path:
    require(value == expected, f"static source path mismatch: {value!r}")
    pure = PurePosixPath(expected)
    require(tuple(pure.parts[:2]) == ("work", "v63-ci") and ".." not in pure.parts,
            f"static source path outside work/v63-ci: {expected}")
    root = repo_root.resolve()
    path = (root / Path(*pure.parts)).resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise ContractError(f"static path escapes repository: {expected}") from exc
    return path


def validate_authority(path: Path, expected_sha: str, expected_bytes: int) -> dict[str, Any]:
    authority, payload = read_json(path)
    require(sha256(payload) == expected_sha, "authority SHA-256 mismatch")
    require(len(payload) == expected_bytes, "authority byte mismatch")
    require(authority.get("schema") == AUTHORITY_SCHEMA, "authority schema mismatch")
    require(authority.get("status") == "EXACT_LOCAL_EVIDENCE_LOCKED", "authority status mismatch")
    require(not contains_pending(authority), "authority contains PENDING")
    workflow = authority.get("workflow", {})
    artifact = authority.get("artifact", {})
    source = authority.get("source", {})
    require(workflow.get("run_id") == 31863434345, "authority run drift")
    require(workflow.get("head_sha") == "3a503721ec899f6c1c92758eeb5facc49e0d59b4", "authority head drift")
    require(workflow.get("job_id") == 94960572977, "authority job drift")
    require(artifact.get("id") == 9241529792, "authority artifact drift")
    require(artifact.get("variant") == "fourier_pair", "authority variant drift")
    require(artifact.get("zip_sha256") == "799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333", "authority ZIP drift")
    require(artifact.get("zip_bytes") == 1684227 and artifact.get("member_count") == 48,
            "authority ZIP size/member drift")
    require(source.get("sha256") == SOURCE_SHA256 and source.get("bytes") == SOURCE_BYTES
            and source.get("lines") == SOURCE_LINES
            and source.get("declaration_count") == DECLARATION_COUNT,
            "authority source lock drift")
    require(source.get("global_maxHeartbeats") == {"token_count": 8, "set_option_count": 8},
            "authority heartbeat drift")
    require(source.get("trust_six") == {token: 0 for token in TRUST_TOKENS},
            "authority trust-six drift")
    members = authority.get("expected_flat_members")
    require(isinstance(members, list) and len(members) == 48
            and len(set(members)) == 48 and members == sorted(members),
            "authority flat member set drift")
    ready = authority.get("official_v62_ready", {})
    require(ready.get("sha256") == READY_INDEX_SHA256 and ready.get("bytes") == 160559
            and ready.get("winner_variant") == "fourier_pair"
            and ready.get("winner_clean") is False,
            "official v62 READY authority drift")
    direct = authority.get("direct_chain", {})
    require(direct.get("Mock2_exit") == 0 and direct.get("Mock2_Advanced_exit") == 0
            and direct.get("Mock2_FunctionalAnalysis_exit") == 1
            and direct.get("FA_max_errors") == 2000
            and direct.get("cap_sentinel_present") is False
            and direct.get("full_inventory_complete") is True,
            "authority direct-chain drift")
    require(authority.get("runtime_evidence_fallback_allowed") is False,
            "authority permits runtime fallback")
    require(authority.get("source_moves_allowed") is False, "authority permits source moves")
    require(authority.get("heartbeat_increases_allowed") is False,
            "authority permits heartbeat increase")
    require(authority.get("clean_claim_permitted_from_authority") is False,
            "authority permits stale clean claim")
    return authority


def canonical_authority_projection(authority: dict[str, Any]) -> dict[str, Any]:
    workflow = authority["workflow"]
    artifact = authority["artifact"]
    source = authority["source"]
    members = authority["member_locks"]
    return {
        "workflow_run_id": workflow["run_id"],
        "head_sha": workflow["head_sha"],
        "head_branch": workflow["head_branch"],
        "job_id": workflow["job_id"],
        "artifact_id": artifact["id"],
        "artifact_name": artifact["name"],
        "artifact_size_in_bytes": artifact["size_in_bytes"],
        "artifact_digest": artifact["digest"],
        "variant": artifact["variant"],
        "source_sha256": source["sha256"],
        "source_bytes": source["bytes"],
        "source_lines": source["lines"],
        "declaration_count": source["declaration_count"],
        "diagnostics_sha256": members["FULL_DIAGNOSTICS.json"]["sha256"],
        "fa_log_sha256": members["Mock2_FunctionalAnalysis.log"]["sha256"],
        "patch_audit_sha256": members["PATCH_AUDIT.json"]["sha256"],
        "toolchain_pin_sha256": members["TOOLCHAIN_PIN.json"]["sha256"],
        "official_v62_ready_sha256": authority["official_v62_ready"]["sha256"],
    }


def validate_manifest(payload: dict[str, Any], expected_id: str) -> dict[str, dict[str, Any]]:
    exact_keys(payload, {"schema", "status", "manifest_id", "authority_source",
                         "source_package", "repairs", "constraints"},
               f"manifest {expected_id}")
    require(payload["schema"] == MANIFEST_SCHEMA, f"manifest schema drift: {expected_id}")
    require(payload["status"] == "READY", f"manifest not READY: {expected_id}")
    require(payload["manifest_id"] == expected_id, f"manifest ID drift: {expected_id}")
    authority = exact_keys(payload["authority_source"],
                           {"sha256", "bytes", "lines", "declaration_count"},
                           f"manifest authority {expected_id}")
    require(authority == {"sha256": SOURCE_SHA256, "bytes": SOURCE_BYTES,
                          "lines": SOURCE_LINES, "declaration_count": DECLARATION_COUNT},
            f"manifest authority drift: {expected_id}")
    source_package = exact_keys(payload["source_package"],
                                {"path", "sha256", "bytes", "result_index_path",
                                 "result_index_sha256", "direct_lean_verified"},
                                f"manifest source package {expected_id}")
    require(source_package["direct_lean_verified"] is False,
            f"manifest improperly claims direct Lean: {expected_id}")
    for key in ("sha256", "result_index_sha256"):
        require(SHA256_RE.fullmatch(source_package[key]) is not None,
                f"manifest source package hash invalid: {expected_id}/{key}")
    require(isinstance(source_package["bytes"], int) and source_package["bytes"] > 0,
            f"manifest source package bytes invalid: {expected_id}")
    constraints = exact_keys(payload["constraints"],
                             {"body_only", "source_moves", "maxHeartbeats_delta",
                              "trust_six_delta", "runtime_fallback_allowed", "composition"},
                             f"manifest constraints {expected_id}")
    require(constraints == {
        "body_only": True,
        "source_moves": 0,
        "maxHeartbeats_delta": 0,
        "trust_six_delta": 0,
        "runtime_fallback_allowed": False,
        "composition": "EXACT_FROM_AUTHORITY_NONCUMULATIVE",
    }, f"manifest constraints drift: {expected_id}")
    repairs = payload["repairs"]
    require(isinstance(repairs, list), f"manifest repairs must be array: {expected_id}")
    expected_ids = MANIFEST_RECORDS[expected_id][4]
    require([row.get("id") for row in repairs if isinstance(row, dict)] == expected_ids,
            f"manifest repair order/IDs drift: {expected_id}")
    result: dict[str, dict[str, Any]] = {}
    operation_ids: set[str] = set()
    for repair in repairs:
        exact_keys(repair, {"id", "sequence", "stage", "depends_on", "conflicts_with",
                            "owner", "operations", "diagnostic_roots", "constraints"},
                   f"repair {expected_id}")
        repair_id = repair["id"]
        require(repair_id not in result, f"duplicate repair ID: {repair_id}")
        require(repair_id in REPAIR_METADATA, f"unknown repair ID: {repair_id}")
        sequence, stage, dependencies, conflicts, owner_index, owner_name, owner_region, roots = REPAIR_METADATA[repair_id]
        require((repair["sequence"], repair["stage"], repair["depends_on"],
                 repair["conflicts_with"], repair["diagnostic_roots"]) ==
                (sequence, stage, dependencies, conflicts, roots),
                f"repair metadata drift: {repair_id}")
        owner = exact_keys(repair["owner"],
                           {"declaration_index", "declaration_name", "expected_header",
                            "expected_header_sha256", "expected_authority_region_sha256"},
                           f"owner {repair_id}")
        require(owner["declaration_index"] == owner_index
                and owner["declaration_name"] == owner_name
                and owner["expected_authority_region_sha256"] == owner_region,
                f"owner metadata drift: {repair_id}")
        require(sha256(owner["expected_header"].encode("utf-8")) ==
                owner["expected_header_sha256"], f"owner header hash drift: {repair_id}")
        repair_constraints = exact_keys(
            repair["constraints"],
            {"body_only", "header_unchanged", "statement_unchanged", "comments_unchanged",
             "attributes_unchanged", "source_move", "maxHeartbeats_unchanged",
             "trust_six_unchanged"}, f"repair constraints {repair_id}")
        require(repair_constraints == {
            "body_only": True, "header_unchanged": True, "statement_unchanged": True,
            "comments_unchanged": True, "attributes_unchanged": True,
            "source_move": False, "maxHeartbeats_unchanged": True,
            "trust_six_unchanged": True,
        }, f"repair constraints drift: {repair_id}")
        operations = repair["operations"]
        require(isinstance(operations, list) and operations,
                f"repair operations empty: {repair_id}")
        for operation in operations:
            exact_keys(operation, {"id", "old", "new", "old_sha256", "new_sha256",
                                   "old_bytes", "new_bytes", "counts"},
                       f"operation {repair_id}")
            operation_id = operation["id"]
            require(isinstance(operation_id, str) and operation_id not in operation_ids,
                    f"duplicate/invalid operation ID: {operation_id}")
            operation_ids.add(operation_id)
            old = operation["old"]
            new = operation["new"]
            require(isinstance(old, str) and isinstance(new, str) and old and new and old != new,
                    f"invalid OLD/NEW: {repair_id}/{operation_id}")
            require(sha256(old.encode("utf-8")) == operation["old_sha256"]
                    and len(old.encode("utf-8")) == operation["old_bytes"],
                    f"OLD hash/byte drift: {repair_id}/{operation_id}")
            require(sha256(new.encode("utf-8")) == operation["new_sha256"]
                    and len(new.encode("utf-8")) == operation["new_bytes"],
                    f"NEW hash/byte drift: {repair_id}/{operation_id}")
            counts = exact_keys(operation["counts"],
                                {"old_global_before", "old_owner_before",
                                 "new_global_before", "new_owner_before",
                                 "old_global_after", "old_owner_after",
                                 "new_global_after", "new_owner_after"},
                                f"counts {repair_id}/{operation_id}")
            require(counts == {
                "old_global_before": 1, "old_owner_before": 1,
                "new_global_before": 0, "new_owner_before": 0,
                "old_global_after": 0, "old_owner_after": 0,
                "new_global_after": 1, "new_owner_after": 1,
            }, f"operation count contract drift: {repair_id}/{operation_id}")
        result[repair_id] = repair
    return result


def validate_selection_structure(selection: dict[str, Any], *, ready: bool) -> None:
    allowed_keys = {"schema", "status", "note", "authority", "manifest_schema",
                    "activation", "blockers", "manifests", "composition_mode",
                    "variant_order", "variants", "final_decision", "constraints",
                    "artifact_contract", "independent_cross_audit"}
    exact_keys(selection, allowed_keys, "selection")
    require(selection["schema"] == SELECTION_SCHEMA, "selection schema mismatch")
    require(selection["status"] == ("READY" if ready else "PENDING"),
            "selection status mismatch")
    activation = selection["activation"]
    expected_activation = {
        "materialization_allowed": ready,
        "workflow_matrix_allowed": ready,
        "direct_compile_allowed": ready,
        "ready_selection_emitted": ready,
        "workflow_last_emitted": ready,
    }
    require(activation == expected_activation, "selection activation mismatch")
    if ready:
        require(selection["blockers"] == [], "READY selection retains blockers")
        require(not contains_pending(selection), "READY selection contains PENDING data")
    else:
        require(isinstance(selection["blockers"], list) and selection["blockers"],
                "PENDING selection lacks blockers")
    authority = selection["authority"]
    require(authority.get("runtime_path") == "scripts/fa_v63_authority-lock.json"
            and authority.get("source_sha256") == SOURCE_SHA256
            and authority.get("source_bytes") == SOURCE_BYTES
            and authority.get("source_lines") == SOURCE_LINES
            and authority.get("declaration_count") == DECLARATION_COUNT
            and authority.get("official_v62_ready_sha256") == READY_INDEX_SHA256,
            "selection authority projection drift")
    schema = selection["manifest_schema"]
    require(schema.get("runtime_path") == "scripts/fa_v63_body-only-manifest.schema.json"
            and schema.get("schema") == MANIFEST_SCHEMA,
            "selection manifest-schema projection drift")
    artifact_contract = exact_keys(
        selection["artifact_contract"],
        {"schema", "status", "member_count", "flat_members_only",
         "duplicate_members_allowed", "member_names", "v62_authority_zip",
         "result_inventory_enforced_by_final_gate",
         "runtime_evidence_fallback_allowed"},
        "result artifact contract",
    )
    require(artifact_contract["schema"] == "fa-v63-exact-result-artifact-v1"
            and artifact_contract["status"] == "EXACT_STATIC_LOCK"
            and artifact_contract["member_count"] == 48
            and artifact_contract["flat_members_only"] is True
            and artifact_contract["duplicate_members_allowed"] is False
            and artifact_contract["member_names"] == list(RESULT_ARTIFACT_MEMBERS)
            and len(set(artifact_contract["member_names"])) == 48
            and artifact_contract["result_inventory_enforced_by_final_gate"] is True
            and artifact_contract["runtime_evidence_fallback_allowed"] is False,
            "result artifact exact inventory drift")
    require(all(NAME_RE.fullmatch(name) is not None
                and "/" not in name and "\\" not in name
                for name in artifact_contract["member_names"]),
            "result artifact member is non-flat or unsafe")
    authority_zip = exact_keys(
        artifact_contract["v62_authority_zip"],
        {"zip_sha256", "zip_bytes", "member_count", "all_members_reproved",
         "declared_member_lock_count",
         "all_48_member_hashes_emitted_by_reproof",
         "all_member_hashes_derived_only_after_exact_zip_reproof",
         "copy_count", "copies"},
        "result artifact v62 authority projection",
    )
    require(authority_zip["zip_sha256"] ==
            "799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333"
            and authority_zip["zip_bytes"] == 1684227
            and authority_zip["member_count"] == 48
            and authority_zip["all_members_reproved"] is True
            and authority_zip["declared_member_lock_count"] == 12
            and authority_zip["all_48_member_hashes_emitted_by_reproof"] is True
            and authority_zip[
                "all_member_hashes_derived_only_after_exact_zip_reproof"] is True
            and authority_zip["copy_count"] == len(BASE_AUTHORITY_COPIES),
            "result artifact v62 authority projection drift")
    expected_copy_locks = {
        "FINAL_GATE.json": (
            "2537e5bbc28e11dfdbcb5cc6bc7d2adbac5d571b37393087863b1215b88b9b95", 1905),
        "FULL_DIAGNOSTICS.json": (
            "31370de532745411bd9acdc258cf5d90c9d0bb5b08b23870b00b55300000f383", 5807),
        "MATERIALIZATION.json": (
            "a3467b09c65eab27f539c0eed1c78dfc260b2bdcf1aedb971ac74d526984d781", 2675),
        "Mock2_FunctionalAnalysis-candidate.lean": (SOURCE_SHA256, SOURCE_BYTES),
        "Mock2_FunctionalAnalysis.log": (
            "8e27a4dcc8be79a091b8b1c2f61197fdb7c9e4d995f3e158327442969c1de60a", 290901),
        "TOOLCHAIN_PIN.json": (
            "8f54d5486b82a5fc11bc52199c89265b7e9e8eed5a3ff4131f86251894bcff07", 393),
    }
    expected_copies = []
    for result_member, authority_member in BASE_AUTHORITY_COPIES:
        digest, size = expected_copy_locks[authority_member]
        expected_copies.append({
            "result_member": result_member,
            "authority_member": authority_member,
            "sha256": digest,
            "bytes": size,
        })
    require(authority_zip["copies"] == expected_copies,
            "result artifact authority-copy locks drift")
    cross_audit = exact_keys(
        selection["independent_cross_audit"],
        {"status", "checks_passed", "checks_failed", "lane_count",
         "direct_lean_verified", "clean_claimed", "files"},
        "independent cross-audit",
    )
    require(cross_audit["status"] ==
            "PASS_STATIC_EXACT_V63_MATRIX_DIRECT_LEAN_UNVERIFIED"
            and cross_audit["checks_passed"] == 877
            and cross_audit["checks_failed"] == 0
            and cross_audit["lane_count"] == 11
            and cross_audit["direct_lean_verified"] is False
            and cross_audit["clean_claimed"] is False,
            "independent cross-audit summary drift")
    expected_cross_files = []
    for file_id, (path, file_schema, digest, size) in INDEPENDENT_CROSS_AUDIT_FILES.items():
        expected_cross_files.append({
            "id": file_id, "source_path": path, "schema": file_schema,
            "sha256": digest, "bytes": size,
        })
    require(cross_audit["files"] == expected_cross_files,
            "independent cross-audit file locks drift")
    require(selection["composition_mode"] == "EXACT_FROM_AUTHORITY_NONCUMULATIVE",
            "selection composition mode drift")
    require(selection["variant_order"] == VARIANT_ORDER, "variant order drift")
    variants = selection["variants"]
    require(isinstance(variants, list) and len(variants) == len(VARIANT_ORDER),
            "variant count drift")
    require([row.get("name") for row in variants if isinstance(row, dict)] == VARIANT_ORDER,
            "variant row order drift")
    candidate_shas: list[str] = []
    for row in variants:
        exact_keys(row, {"name", "status", "selected_repair_ids",
                         "expected_diagnostic_roots", "expected_candidate"},
                   "variant row")
        name = row["name"]
        expected_status = "READY" if ready else "STATIC_LOCKED_DIRECT_LEAN_REQUIRED"
        require(row["status"] == expected_status, f"variant status drift: {name}")
        require(row["selected_repair_ids"] == VARIANT_REPAIRS[name],
                f"variant repair set/order drift: {name}")
        require(row["expected_diagnostic_roots"] == VARIANT_ROOTS[name],
                f"variant diagnostic roots drift: {name}")
        candidate = exact_keys(row["expected_candidate"],
                               {"sha256", "bytes", "lines", "declaration_count"},
                               f"candidate lock {name}")
        expected_sha, expected_bytes, expected_lines = VARIANT_LOCKS[name]
        require(candidate == {"sha256": expected_sha, "bytes": expected_bytes,
                              "lines": expected_lines,
                              "declaration_count": DECLARATION_COUNT},
                f"candidate lock drift: {name}")
        candidate_shas.append(candidate["sha256"])
    require(len(set(candidate_shas)) == len(candidate_shas),
            "candidate outputs are not distinct")
    decision = selection["final_decision"]
    require(decision == {
        "f3933_primary": F33E,
        "f3933_fallback": F33T,
        "alternatives_must_not_be_combined": True,
        "combined_best_repair_ids": VARIANT_REPAIRS["combined_best"],
        "direct_lean_verified": False,
        "clean_claimed": False,
    }, "final decision drift")
    constraints = selection["constraints"]
    require(constraints == {
        "bounded_variant_count": 11,
        "all_variants_from_exact_authority": True,
        "hidden_cumulative_parentage": False,
        "distinct_candidate_outputs": True,
        "body_only": True,
        "declaration_count": DECLARATION_COUNT,
        "source_moves": 0,
        "maxHeartbeats_delta": 0,
        "trust_six_delta": 0,
        "runtime_evidence_fallback_allowed": False,
        "pending_exit_code": 2,
        "contract_violation_exit_code": 86,
        "FA_maxErrors": 2000,
    }, "selection constraints drift")


def load_manifest_records(selection: dict[str, Any], repo_root: Path, *, static: bool) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    records = selection["manifests"]
    require(isinstance(records, list) and [row.get("id") for row in records] ==
            list(MANIFEST_RECORDS), "manifest record order/IDs drift")
    manifests: dict[str, dict[str, Any]] = {}
    all_repairs: dict[str, dict[str, Any]] = {}
    for record in records:
        exact_keys(record, {"id", "runtime_path", "sha256", "bytes", "status",
                            "source_path"}, "manifest record")
        manifest_id = record["id"]
        runtime_path, static_path, expected_sha, expected_bytes, _ = MANIFEST_RECORDS[manifest_id]
        require(record["runtime_path"] == runtime_path
                and record["source_path"] == static_path
                and record["sha256"] == expected_sha
                and record["bytes"] == expected_bytes,
                f"manifest record lock drift: {manifest_id}")
        expected_status = "READY" if not static else "STATIC_READY_DIRECT_LEAN_UNVERIFIED"
        require(record["status"] == expected_status,
                f"manifest record status drift: {manifest_id}")
        path = (exact_static_path(record["source_path"], repo_root, static_path)
                if static else exact_runtime_path(record["runtime_path"], repo_root,
                                                  runtime_path))
        manifest, payload = read_json(path)
        require(sha256(payload) == expected_sha and len(payload) == expected_bytes,
                f"manifest file lock mismatch: {manifest_id}")
        repairs = validate_manifest(manifest, manifest_id)
        require(not set(all_repairs).intersection(repairs), "duplicate cross-manifest repair ID")
        all_repairs.update(repairs)
        manifests[manifest_id] = manifest
    require(set(all_repairs) == set(REPAIR_METADATA), "repair universe drift")
    return manifests, all_repairs


def validate_graph_and_variants(all_repairs: dict[str, dict[str, Any]]) -> None:
    for repair_id, repair in all_repairs.items():
        for dependency in repair["depends_on"]:
            require(dependency in all_repairs, f"missing dependency: {repair_id}/{dependency}")
            require(all_repairs[dependency]["sequence"] < repair["sequence"],
                    f"dependency sequence not earlier: {repair_id}/{dependency}")
        for conflict in repair["conflicts_with"]:
            require(conflict in all_repairs, f"unknown conflict: {repair_id}/{conflict}")
            require(repair_id in all_repairs[conflict]["conflicts_with"],
                    f"asymmetric conflict: {repair_id}/{conflict}")
    for name in VARIANT_ORDER:
        selected = VARIANT_REPAIRS[name]
        selected_set = set(selected)
        sequences = [all_repairs[repair_id]["sequence"] for repair_id in selected]
        require(sequences == sorted(sequences), f"variant repair sequence drift: {name}")
        for repair_id in selected:
            require(set(all_repairs[repair_id]["depends_on"]).issubset(selected_set),
                    f"variant dependency closure missing: {name}/{repair_id}")
            require(not set(all_repairs[repair_id]["conflicts_with"]).intersection(selected_set),
                    f"variant selects conflicting repairs: {name}/{repair_id}")


def load_selection_first(selection_path: Path, expected_selection_sha256: str | None) -> tuple[dict[str, Any], bytes, str]:
    selection, payload = read_json(selection_path, pending_if_missing=True)
    digest = sha256(payload)
    if expected_selection_sha256 is not None:
        require(SHA256_RE.fullmatch(expected_selection_sha256) is not None,
                "configured selection SHA invalid")
        require(digest == expected_selection_sha256, "selection SHA-256 mismatch")
    status = selection.get("status")
    if status == "PENDING":
        raise PendingInput("selection status is PENDING")
    require(status == "READY", "selection status is neither READY nor PENDING")
    return selection, payload, digest


def load_ready_contract(*, selection_path: Path, authority_lock_path: Path,
                        manifest_schema_path: Path,
                        expected_selection_sha256: str | None,
                        repo_root: Path = Path(".")) -> dict[str, Any]:
    selection, _, selection_sha = load_selection_first(
        selection_path, expected_selection_sha256)
    validate_selection_structure(selection, ready=True)
    authority_record = selection["authority"]
    schema_record = selection["manifest_schema"]
    exact_runtime_path(authority_record["runtime_path"], repo_root,
                       "scripts/fa_v63_authority-lock.json")
    exact_runtime_path(schema_record["runtime_path"], repo_root,
                       "scripts/fa_v63_body-only-manifest.schema.json")
    require(authority_lock_path.resolve() ==
            (repo_root.resolve() / "scripts/fa_v63_authority-lock.json").resolve(),
            "authority argument is not exact runtime path")
    require(manifest_schema_path.resolve() ==
            (repo_root.resolve() / "scripts/fa_v63_body-only-manifest.schema.json").resolve(),
            "schema argument is not exact runtime path")
    authority = validate_authority(authority_lock_path, authority_record["sha256"],
                                   authority_record["bytes"])
    schema_payload = manifest_schema_path.read_bytes() if manifest_schema_path.is_file() else b""
    require(sha256(schema_payload) == schema_record["sha256"]
            and len(schema_payload) == schema_record["bytes"],
            "manifest schema file lock mismatch")
    try:
        schema_json = json.loads(schema_payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"invalid manifest schema JSON: {exc}") from exc
    require(schema_json.get("$id") ==
            "https://local.invalid/fa-v63-body-only-repair-manifest-v1.schema.json",
            "manifest schema identity drift")
    manifests, all_repairs = load_manifest_records(selection, repo_root, static=False)
    validate_graph_and_variants(all_repairs)
    return {
        "selection": selection,
        "selection_sha256": selection_sha,
        "authority": authority,
        "manifests": manifests,
        "all_repairs": all_repairs,
    }


def validate_pending_scaffold(*, selection_path: Path, authority_lock_path: Path,
                              manifest_schema_path: Path,
                              expected_selection_sha256: str | None,
                              repo_root: Path = Path(".")) -> dict[str, Any]:
    selection, payload = read_json(selection_path)
    digest = sha256(payload)
    if expected_selection_sha256 is not None:
        require(digest == expected_selection_sha256, "PENDING selection SHA mismatch")
    validate_selection_structure(selection, ready=False)
    authority_record = selection["authority"]
    schema_record = selection["manifest_schema"]
    authority = validate_authority(authority_lock_path, authority_record["sha256"],
                                   authority_record["bytes"])
    schema_payload = manifest_schema_path.read_bytes() if manifest_schema_path.is_file() else b""
    require(sha256(schema_payload) == schema_record["sha256"]
            and len(schema_payload) == schema_record["bytes"],
            "PENDING manifest schema lock mismatch")
    manifests, all_repairs = load_manifest_records(selection, repo_root, static=True)
    validate_graph_and_variants(all_repairs)
    return {
        "selection": selection,
        "selection_sha256": digest,
        "authority": authority,
        "manifests": manifests,
        "all_repairs": all_repairs,
        "activation_allowed": False,
    }
