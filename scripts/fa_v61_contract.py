#!/usr/bin/env python3
"""Shared fail-closed contract validation for the v61 direct Lean matrix."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path, PurePosixPath
from typing import Any


SELECTION_SCHEMA = "fa-v61-direct-eight-way-selection-v1"
MANIFEST_SCHEMA = "fa-v61-body-only-repair-manifest-v1"
AUTHORITY_SCHEMA = "fa-v61-v60-winner-authority-lock-v1"
AUTHORITY_LOCK_SHA256 = "74f045cf41b955a7b319254cf1bd9c3207d16145c2e4fc2cb6ceb490eaeeccf5"
MANIFEST_SCHEMA_SHA256 = "5c99bce6b27d05df2b57b929277bf13fcd57f06842b5221a9cb3844a0a25ea0a"
MANIFEST_SCHEMA_BYTES = 4375
CROSS_AUDIT_SHA256 = "5229162586ebb6e1bc1108dcfd1f67e84116ce7b4921e1ad93cd0c7d98ef9514"
CROSS_AUDIT_BYTES = 15978
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
TRUST_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)
F3930 = "V61-FOURIER-IDX3930-RING-ALL-FIELDSIMP-GOALS"
F3933 = "V61-FOURIER-IDX3933-STAR-MUL-ISOLATED-PROBE"
F3939 = "V61-FOURIER-IDX3939-AC-RFL-AFTER-RING-NF"
R17 = "V61-IDX4017-WRAPPER-EVAL-THEN-TYPED-INNER-CHANGE"
R18E = "V61-IDX4018-EXPLICIT-TWO-LEVEL-CLM-EXT"
R18T = "V61-IDX4018-TYPED-INNER-CONGRARG"
EXACT_REPAIR_IDS_BY_MANIFEST = {
    "fourier": [F3930, F3933, F3939],
    "weighted": [R17, R18E, R18T],
}
# Per-repair metadata is part of the authority contract, not merely manifest
# metadata.  This prevents a self-consistent manifest/index rehash from moving
# diagnostic ownership, reordering stages, or substituting a different body.
EXACT_REPAIR_METADATA = {
    F3930: (0, 0, [], "F3930", [1], 3930,
            "inner_planeWave_ambientTestCore_eq_scale_mul_mFourierCoeff",
            "c111b6309213a91e5e9173084a786363594990a54a0a9a5d3549bc1aea255ad4",
            "9bb2b8f834fcf921662ca829d782ff59a1a3f104275609f1df60e366dfc7d4fc",
            "d05296934247aa5f4c19f2ba0220632a8ea77d70439b7bd548d1ff40bdc40846",
            "762b740dc64acc1b05ac65a4ec05db96a02dcf94ba9a178bd88906f41096a948"),
    F3933: (1, 0, [], "F3933", [2], 3933,
            "inner_literalStagePlaneWave",
            "74b180d55166924f3fe81667c8e1c578a0852dccf65dbc23cd1c227596b4d6f9",
            "a2b27930d6539bf6d2bf6ead73ab957bfc8c265b06d2c17f99e8d4d486d25220",
            "dd7b6af07cd37cd68cc3c0e4cd011cae2c8def73d977c98fdb13242b3dfee627",
            "07e618ac2899b2dbcd839d00c456a26cf6b96f30ef05ba2407ef75ca881e4c2d"),
    F3939: (2, 0, [], "F3939", [3], 3939,
            "norm_planeFourierRemainder_eq_scale_mul_torusRemainder",
            "5e205423d64abefee46c707bcd6ce257b480ea09d92b1d441240da249fa02ee0",
            "bb9886a7fe948c390550de053e06a36b3aa4bdddf28f614f4c028bc1f55395c7",
            "6565d26c8f2a90e4991f554433a6fdee6c0cdefdc5c703a3589f26a7a353cc6c",
            "632a04b1e592d2f8db8cbb66cf76abda5f0fd8ced7846be8818b24fcc1df6d21"),
    R17: (3, 0, [], "W4017", [4], 4017,
          "discriminantHardStageOperator_eq_weightedHard",
          "cec5e99e9ca1e3b9ad8f2374ac985284f80dfcccac09bbae48106a7b40606f6d",
          "3034bc9bb0773d78681bd92d2295b06de1ff46d7658d21d904e18fc87553121e",
          "a6cb438373a967c65de82016f32d919e20c7b17e6ce79f86c6b78d442ca7fcd7",
          "0bac3b416c945c5b3914b89f69b39a1c398f2b6993f857e4beaa8fb6984ddfad"),
    R18E: (4, 1, [R17], "W4018", [5], 4018,
           "weightedFull_sub_weightedHard_eq_weightedTail",
           "38c29a93b7dc39ee0ea0dbabb6cbd38552c4e3c64b2e51d3ad387c4665faba99",
           "5fe2aa90853fad0d65dafbf8f43a69f3c4362248577b3df5dc52046ee23479a2",
           "4b10676419c6498ee420f53ce6e1476987b1460fa0c802e409209ad2294f1b88",
           "c4dd97090632edd0135c5487ccc9a5716f7f87f5e475d9216126c4b681b06494"),
    R18T: (5, 2, [R18E], "W4018", [5], 4018,
           "weightedFull_sub_weightedHard_eq_weightedTail",
           "764b91736270160912ea2044ced91b1aca5d8084440fe25500436d8b7832e73a",
           "5fe2aa90853fad0d65dafbf8f43a69f3c4362248577b3df5dc52046ee23479a2",
           "af1e4a62ee81c185dd3dec3eaf70aef479781eee14e572a1aef473ca490efcfa",
           "3b451e3ce81e6454e4feae90e2ab419fdb86bd2f888de81fe5a48b570a4f50eb"),
}
EXACT_SELECTION_MAP = {
    "core": [],
    "fourier_pair": [F3930, F3939],
    "fourier_3933_isolated": [F3933],
    "weighted_r17": [R17],
    "weighted_r17_r18e": [R17, R18E],
    "weighted_r17_r18e_r18t": [R17, R18E, R18T],
    "all_no_3933": [F3930, F3939, R17, R18E, R18T],
    "all_full": [F3930, F3933, F3939, R17, R18E, R18T],
}
EXACT_CANDIDATE_LOCKS = {
    "core": ("84e0a7843de9bcf99a25e51db95d48e9d5feceffe4e1b94f315b11d166792e5a", 2812433, 62933),
    "fourier_pair": ("1badac1451e11708114eb5438616063379558bcf0579dc82a01c2200b501d365", 2812442, 62933),
    "fourier_3933_isolated": ("c118058341d4cadecb73dea395d5fcc7c59a07d9173dd503202e15825e60527d", 2812457, 62934),
    "weighted_r17": ("6b9e3232af984882528a1945788047a8037d42885df00387bae401be79237c5d", 2812871, 62943),
    "weighted_r17_r18e": ("0a54b13dc941892e12f5397c2a7975fa7129ffb1cfd1170c2ddc84edb5925707", 2812945, 62946),
    "weighted_r17_r18e_r18t": ("99f4c65980d223bfcee493f8912e98a9790b75a0faaa7f0826b2c898d11e2057", 2813026, 62947),
    "all_no_3933": ("c8720767c6041481ab8c742db46002c4aae738f213c30d70622ae055fcd3ed94", 2813035, 62947),
    "all_full": ("0b5b6553a3979efa48dac95436e61c559abcd8235d13de90eb5acdeed26b9ec8", 2813059, 62948),
}


class PendingInput(RuntimeError):
    """An expected v61 input is absent or explicitly PENDING."""


class ContractError(RuntimeError):
    """A present input violates the fail-closed contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


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
    require(isinstance(value, dict), f"JSON root must be an object: {path}")
    return value, payload


def contains_pending(value: Any) -> bool:
    if isinstance(value, str):
        return value == "PENDING" or value.startswith("PENDING_")
    if isinstance(value, list):
        return any(contains_pending(item) for item in value)
    if isinstance(value, dict):
        return any(contains_pending(item) for item in value.values())
    return False


def validate_authority_lock(path: Path, expected_sha256: str | None = None) -> dict[str, Any]:
    authority, payload = read_json(path)
    require(sha256(payload) == AUTHORITY_LOCK_SHA256,
            "authority-lock canonical SHA-256 mismatch")
    if expected_sha256 is not None:
        require(SHA256_RE.fullmatch(expected_sha256) is not None,
                "invalid configured authority-lock SHA-256")
        require(sha256(payload) == expected_sha256, "authority-lock SHA-256 mismatch")
    require(authority.get("schema") == AUTHORITY_SCHEMA, "authority schema mismatch")
    require(authority.get("status") == "EXACT_LOCAL_EVIDENCE_LOCKED",
            "authority is not exact-locked")
    require(contains_pending(authority) is False, "authority contains PENDING data")
    workflow = authority.get("workflow")
    artifact = authority.get("artifact")
    source = authority.get("source")
    require(isinstance(workflow, dict) and isinstance(artifact, dict)
            and isinstance(source, dict), "authority sections missing")
    require(workflow.get("run_id") == 31857051709, "authority run drift")
    require(workflow.get("head_sha") ==
            "21f3bd08703a2d3e73375d69cd2474a7366a4497", "authority head drift")
    require(workflow.get("job_id") == 94943712491, "authority job drift")
    require(artifact.get("id") == 9239620079, "authority artifact drift")
    require(artifact.get("variant") == "A_no_idx3933", "authority variant drift")
    require(source.get("sha256") ==
            "84e0a7843de9bcf99a25e51db95d48e9d5feceffe4e1b94f315b11d166792e5a",
            "authority source drift")
    require(source.get("declaration_count") == 4416, "authority declaration drift")
    require(authority.get("runtime_evidence_fallback_allowed") is False,
            "authority permits evidence fallback")
    require(authority.get("source_moves_allowed") is False,
            "authority permits source moves")
    require(authority.get("heartbeat_increases_allowed") is False,
            "authority permits heartbeat increases")
    local_evidence = authority.get("local_evidence")
    require(isinstance(local_evidence, dict), "authority local evidence missing")
    independent_audit = local_evidence.get("independent_audit")
    ready_index = local_evidence.get("ready_index")
    require(isinstance(independent_audit, dict)
            and independent_audit.get("status") ==
            "PASS_EXACT_LOCAL_EVIDENCE_AUDIT_AND_POST_HYDRATION_CONSERVATION",
            "independent audit status drift")
    require(isinstance(ready_index, dict)
            and ready_index.get("status") ==
            "READY_V59_SIX_ARTIFACTS_EXACT_LOCKED",
            "READY index status drift")
    return authority


def canonical_authority_projection(authority: dict[str, Any]) -> dict[str, Any]:
    """Return the one provenance projection used by every runtime stage."""
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
        "selection_sha256": authority["selection_lock"]["sha256"],
    }


def exact_runtime_path(value: Any, repo_root: Path, *, suffix: str | None = None) -> tuple[str, Path]:
    require(isinstance(value, str) and value, "runtime path missing")
    require("\\" not in value, f"runtime path contains backslash: {value}")
    pure = PurePosixPath(value)
    require(not pure.is_absolute() and ".." not in pure.parts and "." not in pure.parts,
            f"runtime path is not confined relative path: {value}")
    require(len(pure.parts) == 2 and pure.parts[0] == "scripts"
            and pure.parts[1].startswith("fa_v61_"),
            f"runtime path is outside exact scripts/fa_v61_* allowlist: {value}")
    if suffix is not None:
        require(value.endswith(suffix), f"runtime path suffix mismatch: {value}")
    root = repo_root.resolve()
    resolved = (root / Path(*pure.parts)).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ContractError(f"runtime path escapes repo root: {value}") from exc
    return value, resolved


def validate_repair(repair: Any, authority_source_sha256: str) -> dict[str, Any]:
    require(isinstance(repair, dict), "repair must be an object")
    required = {
        "id", "sequence", "stage", "depends_on", "owner", "old", "new", "counts",
        "diagnostic_coverage", "constraints",
    }
    require(set(repair) == required, f"repair key drift: {repair.get('id')}")
    repair_id = repair["id"]
    require(isinstance(repair_id, str) and repair_id, "repair id missing")
    require(isinstance(repair["sequence"], int) and repair["sequence"] >= 0,
            f"invalid repair sequence: {repair_id}")
    require(isinstance(repair["stage"], int) and repair["stage"] >= 0,
            f"invalid repair stage: {repair_id}")
    require(isinstance(repair["depends_on"], list)
            and all(isinstance(item, str) and item for item in repair["depends_on"])
            and len(repair["depends_on"]) == len(set(repair["depends_on"]))
            and repair_id not in repair["depends_on"],
            f"invalid repair dependency list: {repair_id}")
    owner = repair["owner"]
    require(isinstance(owner, dict), f"owner must be object: {repair_id}")
    require(set(owner) == {
        "declaration_index", "declaration_name", "expected_header",
        "expected_input_region_sha256",
    }, f"owner key drift: {repair_id}")
    require(isinstance(owner["declaration_index"], int)
            and owner["declaration_index"] >= 0, f"invalid owner index: {repair_id}")
    require(isinstance(owner["declaration_name"], str)
            and owner["declaration_name"], f"invalid owner name: {repair_id}")
    require(isinstance(owner["expected_header"], str)
            and owner["declaration_name"] in owner["expected_header"],
            f"owner header/name mismatch: {repair_id}")
    require(SHA256_RE.fullmatch(owner["expected_input_region_sha256"]) is not None,
            f"invalid owner region SHA-256: {repair_id}")
    old, new = repair["old"], repair["new"]
    require(isinstance(old, str) and isinstance(new, str) and old and new and old != new,
            f"invalid old/new transform: {repair_id}")
    for marker in ("maxHeartbeats", "sorry", "admit", "axiom", "unsafe",
                   "native_decide", "Lean.ofReduceBool", "/-", "-/", "--", "@["):
        require(marker not in old and marker not in new,
                f"forbidden body-only marker {marker!r}: {repair_id}")
    counts = repair["counts"]
    require(isinstance(counts, dict) and set(counts) == {
        "old_in_owner", "old_global", "new_in_owner_before", "new_in_owner_after",
        "new_global_before", "new_global_after",
    }, f"count contract drift: {repair_id}")
    for key, value in counts.items():
        require(isinstance(value, int) and value >= 0,
                f"invalid {key}: {repair_id}")
    require(counts["old_in_owner"] >= 1 and counts["old_global"] >= 1
            and counts["new_in_owner_after"] >= 1,
            f"non-positive required count: {repair_id}")
    coverage = repair["diagnostic_coverage"]
    require(isinstance(coverage, dict)
            and set(coverage) == {"root_key", "baseline_ordinals", "count"},
            f"diagnostic coverage drift: {repair_id}")
    require(isinstance(coverage["root_key"], str)
            and NAME_RE.fullmatch(coverage["root_key"]) is not None,
            f"invalid diagnostic root key: {repair_id}")
    ordinals = coverage["baseline_ordinals"]
    require(isinstance(ordinals, list) and ordinals
            and all(isinstance(item, int) and item >= 1 for item in ordinals)
            and len(set(ordinals)) == len(ordinals),
            f"invalid diagnostic coverage ordinals: {repair_id}")
    require(coverage["count"] == len(ordinals),
            f"diagnostic coverage count mismatch: {repair_id}")
    require(repair_id in EXACT_REPAIR_METADATA,
            f"repair ID is not in exact metadata registry: {repair_id}")
    (expected_sequence, expected_stage, expected_dependencies, expected_root,
     expected_ordinals, expected_owner_index, expected_owner_name,
     expected_owner_region_sha, expected_header_sha, expected_old_sha,
     expected_new_sha) = EXACT_REPAIR_METADATA[repair_id]
    require(repair["sequence"] == expected_sequence,
            f"exact repair sequence drift: {repair_id}")
    require(repair["stage"] == expected_stage,
            f"exact repair stage drift: {repair_id}")
    require(repair["depends_on"] == expected_dependencies,
            f"exact repair dependency drift: {repair_id}")
    require(coverage["root_key"] == expected_root
            and ordinals == expected_ordinals,
            f"exact repair diagnostic ownership drift: {repair_id}")
    require(owner["declaration_index"] == expected_owner_index
            and owner["declaration_name"] == expected_owner_name,
            f"exact repair declaration owner drift: {repair_id}")
    require(owner["expected_input_region_sha256"] == expected_owner_region_sha,
            f"exact repair owner region lock drift: {repair_id}")
    require(sha256(owner["expected_header"].encode("utf-8")) == expected_header_sha,
            f"exact repair owner header drift: {repair_id}")
    require(sha256(old.encode("utf-8")) == expected_old_sha
            and sha256(new.encode("utf-8")) == expected_new_sha,
            f"exact repair body transform drift: {repair_id}")
    require(counts == {
        "old_in_owner": 1,
        "old_global": 1,
        "new_in_owner_before": 0,
        "new_in_owner_after": 1,
        "new_global_before": 0,
        "new_global_after": 1,
    }, f"exact repair occurrence-count drift: {repair_id}")
    constraints = repair["constraints"]
    require(constraints == {
        "body_only": True,
        "header_unchanged": True,
        "statement_unchanged": True,
        "comments_unchanged": True,
        "attributes_unchanged": True,
        "source_move": False,
        "maxHeartbeats_unchanged": True,
        "trust_six_unchanged": True,
    }, f"repair constraints are not fail-closed: {repair_id}")
    return repair


def validate_manifest(payload: dict[str, Any], authority_source_sha256: str) -> list[dict[str, Any]]:
    require(set(payload) == {
        "schema", "status", "authority_source_sha256", "manifest_id",
        "repairs", "constraints",
    }, "manifest top-level key drift")
    require(payload.get("schema") == MANIFEST_SCHEMA, "manifest schema mismatch")
    status = payload.get("status")
    if isinstance(status, str) and status.startswith("PENDING"):
        raise PendingInput(f"manifest is PENDING: {payload.get('manifest_id')}")
    require(status == "READY", "manifest status is not READY")
    require(contains_pending(payload) is False, "READY manifest contains PENDING")
    require(payload.get("authority_source_sha256") == authority_source_sha256,
            "manifest authority source mismatch")
    require(isinstance(payload.get("manifest_id"), str)
            and NAME_RE.fullmatch(payload["manifest_id"]) is not None,
            "invalid manifest id")
    require(payload.get("constraints") == {
        "body_only": True,
        "source_moves": 0,
        "maxHeartbeats_delta": 0,
        "trust_six_delta": 0,
        "diagnostic_coverage_overlap": "SAME_OWNER_ROOT_ORDERED_ONLY",
    }, "manifest constraints are not fail-closed")
    repairs = payload.get("repairs")
    require(isinstance(repairs, list), "manifest repairs must be a list")
    validated = [validate_repair(item, authority_source_sha256) for item in repairs]
    ids = [item["id"] for item in validated]
    require(len(ids) == len(set(ids)), "duplicate repair id in manifest")
    sequences = [item["sequence"] for item in validated]
    require(len(sequences) == len(set(sequences)), "duplicate repair sequence")
    require(sequences == sorted(sequences), "manifest repair array is not sequence ordered")
    return validated


def dependency_ancestors(
    repair_id: str, repairs: dict[str, dict[str, Any]], cache: dict[str, set[str]],
    visiting: set[str] | None = None,
) -> set[str]:
    if repair_id in cache:
        return cache[repair_id]
    active = set() if visiting is None else set(visiting)
    require(repair_id not in active, f"repair dependency cycle at {repair_id}")
    active.add(repair_id)
    repair = repairs[repair_id]
    result: set[str] = set()
    for dependency in repair["depends_on"]:
        require(dependency in repairs,
                f"unknown repair dependency {dependency} from {repair_id}")
        require(repairs[dependency]["stage"] < repair["stage"],
                f"dependency stage is not strictly earlier: {dependency} -> {repair_id}")
        result.add(dependency)
        result.update(dependency_ancestors(dependency, repairs, cache, active))
    cache[repair_id] = result
    return result


def validate_dependency_and_overlap_graph(repairs: dict[str, dict[str, Any]]) -> dict[str, set[str]]:
    cache: dict[str, set[str]] = {}
    for repair_id in repairs:
        dependency_ancestors(repair_id, repairs, cache)
    rows = list(repairs.values())
    for index, left in enumerate(rows):
        left_ordinals = set(left["diagnostic_coverage"]["baseline_ordinals"])
        for right in rows[index + 1:]:
            overlap = left_ordinals.intersection(
                right["diagnostic_coverage"]["baseline_ordinals"]
            )
            if not overlap:
                continue
            same_owner = (
                left["owner"]["declaration_index"] == right["owner"]["declaration_index"]
                and left["owner"]["declaration_name"] == right["owner"]["declaration_name"]
            )
            same_root = (left["diagnostic_coverage"]["root_key"]
                         == right["diagnostic_coverage"]["root_key"])
            ordered = (left["id"] in cache[right["id"]]
                       or right["id"] in cache[left["id"]])
            require(same_owner and same_root and ordered,
                    "diagnostic overlap is not same-owner/root dependency-ordered: "
                    f"{left['id']} vs {right['id']} ordinals={sorted(overlap)}")
    return cache


def load_ready_contract(
    *, selection_path: Path, authority_lock_path: Path, manifest_schema_path: Path,
    cross_audit_path: Path,
    expected_selection_sha256: str | None = None, repo_root: Path = Path("."),
) -> dict[str, Any]:
    if not selection_path.is_file():
        raise PendingInput(f"missing PENDING selection: {selection_path}")
    selection, selection_bytes = read_json(selection_path)
    if selection.get("status") != "READY":
        if selection.get("status") == "PENDING" or contains_pending(selection):
            raise PendingInput("v61 selection is PENDING")
        raise ContractError("selection status is not READY")
    if expected_selection_sha256 is not None:
        if expected_selection_sha256 == "PENDING":
            raise PendingInput("configured selection SHA-256 is PENDING")
        require(SHA256_RE.fullmatch(expected_selection_sha256) is not None,
                "invalid configured selection SHA-256")
        require(sha256(selection_bytes) == expected_selection_sha256,
                "selection SHA-256 mismatch")
    require(selection.get("schema") == SELECTION_SCHEMA, "selection schema mismatch")
    require(set(selection) == {
        "schema", "status", "note", "authority", "manifest_schema",
        "cross_audit", "activation", "pending_inputs", "manifests",
        "variant_order", "variants", "constraints",
    }, "selection top-level key drift")
    require(contains_pending(selection) is False, "READY selection contains PENDING")
    root = repo_root.resolve()
    _, expected_selection_path = exact_runtime_path(
        "scripts/fa_v61_selection.json", root, suffix=".json"
    )
    require(selection_path.resolve() == expected_selection_path,
            "selection CLI path is not exact promoted runtime path")
    activation = selection.get("activation")
    require(activation == {
        "materialization_allowed": True,
        "workflow_matrix_allowed": True,
        "direct_compile_allowed": True,
    }, "selection activation is not fully READY")
    require(selection.get("pending_inputs") == {}, "READY selection has pending inputs")
    authority_ref = selection.get("authority")
    require(isinstance(authority_ref, dict), "selection authority missing")
    authority_runtime, expected_authority_path = exact_runtime_path(
        authority_ref.get("lock_path"), root, suffix=".json"
    )
    require(authority_runtime == "scripts/fa_v61_authority-lock.json",
            "authority runtime path is not canonical")
    require(authority_lock_path.resolve() == expected_authority_path,
            "authority CLI path differs from selection runtime path")
    authority = validate_authority_lock(
        authority_lock_path, authority_ref.get("lock_sha256")
    )
    source_lock = authority["source"]
    require(authority_ref.get("source_sha256") == source_lock["sha256"]
            and authority_ref.get("source_bytes") == source_lock["bytes"]
            and authority_ref.get("source_lines") == source_lock["lines"]
            and authority_ref.get("declaration_count") == source_lock["declaration_count"],
            "selection/source authority projection mismatch")
    schema_ref = selection.get("manifest_schema")
    require(isinstance(schema_ref, dict), "manifest schema lock missing")
    schema_runtime, expected_schema_path = exact_runtime_path(
        schema_ref.get("runtime_path"), root, suffix=".json"
    )
    require(schema_runtime == "scripts/fa_v61_body-only-manifest.schema.json",
            "manifest schema runtime path is not canonical")
    require(manifest_schema_path.resolve() == expected_schema_path,
            "manifest schema CLI path differs from selection runtime path")
    schema_payload = manifest_schema_path.read_bytes() if manifest_schema_path.is_file() else b""
    require(bool(schema_payload), "manifest schema file missing")
    require(schema_ref == {
        "runtime_path": "scripts/fa_v61_body-only-manifest.schema.json",
        "sha256": MANIFEST_SCHEMA_SHA256,
        "bytes": MANIFEST_SCHEMA_BYTES,
        "schema": MANIFEST_SCHEMA,
    }, "manifest schema selection projection drift")
    require(sha256(schema_payload) == MANIFEST_SCHEMA_SHA256
            and len(schema_payload) == MANIFEST_SCHEMA_BYTES,
            "manifest schema file lock mismatch")
    try:
        schema_document = json.loads(schema_payload)
    except json.JSONDecodeError as exc:
        raise ContractError("manifest schema file is invalid JSON") from exc
    require(schema_document.get("$id") ==
            "https://local.invalid/fa-v61-body-only-repair-manifest-v1.schema.json"
            and schema_document.get("additionalProperties") is False,
            "manifest schema canonical contract drift")
    cross_ref = selection.get("cross_audit")
    require(isinstance(cross_ref, dict), "cross-audit lock missing")
    cross_runtime, expected_cross_path = exact_runtime_path(
        cross_ref.get("runtime_path"), root, suffix=".json"
    )
    require(cross_runtime == "scripts/fa_v61_cross-audit.json",
            "cross-audit runtime path is not canonical")
    require(cross_audit_path.resolve() == expected_cross_path,
            "cross-audit CLI path differs from selection runtime path")
    require(cross_ref == {
        "runtime_path": "scripts/fa_v61_cross-audit.json",
        "sha256": CROSS_AUDIT_SHA256,
        "bytes": CROSS_AUDIT_BYTES,
        "schema": "fa-v61-independent-cross-manifest-audit-v1",
        "status": "PASS_STATIC_ONLY_DIRECT_LEAN_UNVERIFIED",
    }, "cross-audit selection projection drift")
    cross_payload = cross_audit_path.read_bytes() if cross_audit_path.is_file() else b""
    require(sha256(cross_payload) == CROSS_AUDIT_SHA256
            and len(cross_payload) == CROSS_AUDIT_BYTES,
            "cross-audit runtime file lock mismatch")
    try:
        cross_document = json.loads(cross_payload)
    except json.JSONDecodeError as exc:
        raise ContractError("cross-audit file is invalid JSON") from exc
    require(cross_document.get("schema") == cross_ref["schema"]
            and cross_document.get("status") == cross_ref["status"],
            "cross-audit schema/status drift")
    manifests = selection.get("manifests")
    require(isinstance(manifests, list) and len(manifests) == 2,
            "selection manifest count must be exactly two")
    manifest_ids = [record.get("id") for record in manifests
                    if isinstance(record, dict)]
    require(manifest_ids == ["fourier", "weighted"],
            "manifest id set/order must be exactly fourier, weighted")
    require(len(manifest_ids) == len(set(manifest_ids)), "duplicate manifest id")
    all_repairs: dict[str, dict[str, Any]] = {}
    manifest_records: list[dict[str, Any]] = []
    manifest_runtime_paths: list[str] = []
    for record in manifests:
        require(isinstance(record, dict), "manifest record must be an object")
        if record.get("status") != "READY" or contains_pending(record):
            raise PendingInput(f"manifest record is PENDING: {record.get('id')}")
        runtime_value, runtime_path = exact_runtime_path(
            record.get("runtime_path"), root, suffix=".json"
        )
        manifest_runtime_paths.append(runtime_value)
        manifest, raw = read_json(runtime_path, pending_if_missing=True)
        require(sha256(raw) == record.get("sha256")
                and len(raw) == record.get("bytes"),
                f"manifest lock mismatch: {record.get('id')}")
        repairs = validate_manifest(manifest, source_lock["sha256"])
        require(manifest.get("manifest_id") == record.get("id"),
                "manifest id/record mismatch")
        require([repair["id"] for repair in repairs]
                == EXACT_REPAIR_IDS_BY_MANIFEST[record["id"]],
                f"manifest repair ID/order drift: {record['id']}")
        for repair in repairs:
            require(repair["id"] not in all_repairs,
                    f"duplicate cross-manifest repair id: {repair['id']}")
            all_repairs[repair["id"]] = repair
        manifest_records.append({"record": record, "payload": manifest})
    require(len(manifest_runtime_paths) == len(set(manifest_runtime_paths)),
            "duplicate manifest runtime path")
    sequences = [repair["sequence"] for repair in all_repairs.values()]
    require(len(sequences) == len(set(sequences)),
            "cross-manifest repair sequence is not globally unique")
    require(sequences == list(range(6)),
            "cross-manifest repair sequence/order must be exact 0..5")
    ancestors = validate_dependency_and_overlap_graph(all_repairs)
    order = selection.get("variant_order")
    variants = selection.get("variants")
    exact_variant_order = [
        "core", "fourier_pair", "fourier_3933_isolated",
        "weighted_r17", "weighted_r17_r18e", "weighted_r17_r18e_r18t",
        "all_no_3933", "all_full",
    ]
    require(order == exact_variant_order, "variant names/order are not exact eight-way lock")
    require(isinstance(variants, list) and len(variants) == len(order),
            "variant list/order length mismatch")
    require([row.get("name") for row in variants] == order,
            "variant list is not in locked order")
    for row in variants:
        require(row.get("status") == "READY", f"variant not READY: {row.get('name')}")
        selected = row.get("selected_repair_ids")
        require(isinstance(selected, list) and len(selected) == len(set(selected)),
                f"invalid repair selection: {row.get('name')}")
        require(all(item in all_repairs for item in selected),
                f"unknown repair selected: {row.get('name')}")
        require(selected == EXACT_SELECTION_MAP[row["name"]],
                f"variant exact repair selection drift: {row.get('name')}")
        require(selected == sorted(selected, key=lambda item: all_repairs[item]["sequence"]),
                f"selected repair IDs are not in exact global sequence: {row.get('name')}")
        selected_set = set(selected)
        for position, repair_id in enumerate(selected):
            dependencies = all_repairs[repair_id]["depends_on"]
            require(set(dependencies).issubset(selected_set),
                    f"selected repair dependency missing: {row.get('name')}:{repair_id}")
            require(all(selected.index(dependency) < position for dependency in dependencies),
                    f"selected repair dependency order invalid: {row.get('name')}:{repair_id}")
        expected = row.get("expected_candidate")
        require(isinstance(expected, dict)
                and SHA256_RE.fullmatch(str(expected.get("sha256"))) is not None
                and isinstance(expected.get("bytes"), int) and expected["bytes"] > 0
                and isinstance(expected.get("lines"), int) and expected["lines"] > 0,
                f"invalid candidate lock: {row.get('name')}")
        require((expected["sha256"], expected["bytes"], expected["lines"])
                == EXACT_CANDIDATE_LOCKS[row["name"]],
                f"candidate lock differs from cross-audit: {row.get('name')}")
        ordinals = {ordinal for repair_id in selected
                    for ordinal in all_repairs[repair_id]["diagnostic_coverage"]["baseline_ordinals"]}
        require(row.get("expected_diagnostic_coverage") == sorted(ordinals),
                f"variant diagnostic coverage mismatch: {row.get('name')}")
    constraints = selection.get("constraints")
    require(constraints == {
        "body_only": True,
        "source_moves": 0,
        "maxHeartbeats_delta": 0,
        "trust_six_delta": 0,
        "diagnostic_coverage_overlap": "SAME_OWNER_ROOT_ORDERED_ONLY",
        "runtime_evidence_fallback_allowed": False,
        "missing_or_pending_exit_code": 2,
    }, "selection constraints are not fail-closed")
    return {
        "selection": selection,
        "selection_bytes": selection_bytes,
        "selection_sha256": sha256(selection_bytes),
        "authority": authority,
        "all_repairs": all_repairs,
        "manifest_records": manifest_records,
    }
