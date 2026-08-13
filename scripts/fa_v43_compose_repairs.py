#!/usr/bin/env python3
"""v43 adapter around the already-promoted v42 static repair composer.

The v42 composer remains the single implementation of declaration parsing,
owner-local replacement, header/comment/attribute preservation, and executable
trust scanning.  This adapter only verifies that dependency by SHA-256 and
normalizes v43 worker-manifest schemas to the v42 composer's contract.

It never invokes Lean, Lake, git, GitHub, or the network.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import sys
from pathlib import Path
from typing import Any


HEX = set("0123456789abcdef")
EXPECTED_AUTHORITY = {
    "run_id": 31709054520,
    "head_sha": "d6e8e7d12bbf76bf371bb0f21c085f0ebd4ba199",
    "artifact_id": 9184978707,
    "artifact_digest": (
        "sha256:a587808a5ca47993bba554673c4b24d2f8c6cbea08415be69db7f9f11923e042"
    ),
    "source_path": (
        "work/v42-run-31709054520/9184978707/"
        "Mock2_FunctionalAnalysis-candidate.lean"
    ),
    "source_sha256": (
        "442dc2841f80b6814a16396a9b08ec27e90d3bd3d1913c4edd417137d8d1bbe7"
    ),
    "source_bytes": 2776625,
    "source_lines": 62113,
    "declaration_count": 4416,
}

# Schema alone is not enough for EARLY because its HC and staged records use
# different list shapes.  Lock the exact (schema, status, list field) triples
# produced by the six audited v43 manifests.
ACCEPTED_LAYOUTS = {
    (
        "fa-v43-early-repair-manifest-v1",
        "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
    ): "repairs",
    (
        "fa-v43-early-repair-manifest-v1",
        "STAGED_DIRECT_LEAN_REQUIRED",
    ): "proposals",
    (
        "fa-v42-declaration-local-repairs-v1",
        "STATIC_ONLY_DIRECT_LEAN_UNVERIFIED_V43_MID_HIGH_CONFIDENCE",
    ): "repairs",
    (
        "fa-v42-declaration-local-repairs-v1",
        "STAGED_STATIC_ONLY_DIRECT_LEAN_UNVERIFIED_V43_MID",
    ): "repairs",
    (
        "fa-v43-late-repair-manifest-v1",
        "HIGH_CONFIDENCE_STATIC_DIRECT_LEAN_UNVERIFIED",
    ): "repairs",
    (
        "fa-v43-late-repair-manifest-v1",
        "STAGE_PROBE_DIRECT_LEAN_REQUIRED",
    ): "repairs",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def require_sha(value: str, label: str) -> str:
    require(len(value) == 64 and set(value) <= HEX, f"{label}: invalid SHA-256")
    require(value != "0" * 64, f"{label}: zero SHA-256")
    return value


def load_locked_module(path: Path, expected_sha: str):
    payload = path.read_bytes()
    require(sha256(payload) == require_sha(expected_sha, "base composer"),
            "base composer SHA mismatch")
    spec = importlib.util.spec_from_file_location("fa_v42_locked_composer", path)
    require(spec is not None and spec.loader is not None,
            "cannot load locked base composer")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_authority(authority: dict[str, Any]) -> dict[str, Any]:
    archive_sha = authority.get("archive_sha256")
    artifact_digest = authority.get("artifact_digest")
    if archive_sha is not None:
        require(
            isinstance(archive_sha, str)
            and len(archive_sha) == 64
            and set(archive_sha) <= HEX,
            "invalid manifest archive_sha256",
        )
        normalized_archive = f"sha256:{archive_sha}"
        if artifact_digest is None:
            artifact_digest = normalized_archive
        else:
            require(
                artifact_digest == normalized_archive,
                "artifact_digest conflicts with archive_sha256",
            )
    require(
        isinstance(artifact_digest, str)
        and artifact_digest.startswith("sha256:")
        and len(artifact_digest) == 71
        and set(artifact_digest[7:]) <= HEX,
        "invalid manifest artifact_digest",
    )
    required = {
        "run_id": authority.get("run_id"),
        "head_sha": authority.get("head_sha"),
        "artifact_id": authority.get("artifact_id"),
        "artifact_digest": artifact_digest,
        "source_path": authority.get("source_path"),
        "source_sha256": authority.get("source_sha256"),
        "source_bytes": authority.get("source_bytes"),
        "source_lines": authority.get("source_lines"),
        "declaration_count": authority.get("declaration_count"),
    }
    missing = [key for key, value in required.items() if value is None]
    require(not missing, f"manifest authority fields missing: {missing}")
    require(required == EXPECTED_AUTHORITY, "manifest authority lock mismatch")
    return required


def normalize_one_repair(
    original: dict[str, Any],
    inherited: dict[str, Any] | None = None,
) -> dict[str, Any]:
    repair = dict(inherited or {})
    repair.update(original)
    required = ("id", "owner", "declaration_index", "old", "new")
    missing = [key for key in required if key not in repair]
    require(not missing, f"repair fields missing: {missing}")
    require(repair.get("kind", "body") == "body",
            f"non-body repair rejected: {repair['id']}")
    require(isinstance(repair["old"], str) and repair["old"],
            f"empty old fragment: {repair['id']}")
    require(isinstance(repair["new"], str) and repair["new"],
            f"empty new fragment: {repair['id']}")
    require(repair["old"] != repair["new"],
            f"no-op repair rejected: {repair['id']}")
    canonical_count = repair.get("expected_count_in_owner")
    alias_count = repair.get("expected_owner_count")
    if canonical_count is not None and alias_count is not None:
        require(
            not isinstance(canonical_count, bool)
            and not isinstance(alias_count, bool)
            and int(canonical_count) == int(alias_count),
            f"conflicting expected owner counts: {repair['id']}",
        )
    selected_count = canonical_count if canonical_count is not None else (
        alias_count if alias_count is not None else 1
    )
    require(not isinstance(selected_count, bool),
            f"boolean expected owner count: {repair['id']}")
    repair["expected_count_in_owner"] = int(selected_count)
    repair.pop("expected_owner_count", None)
    require(repair["expected_count_in_owner"] > 0,
            f"invalid expected owner count: {repair['id']}")
    return repair


def canonical_repairs(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    key = (manifest.get("schema"), manifest.get("status"))
    require(key in ACCEPTED_LAYOUTS, f"manifest layout is not allowlisted: {key}")
    list_field = ACCEPTED_LAYOUTS[key]
    raw_list = manifest.get(list_field)
    require(isinstance(raw_list, list),
            f"allowlisted manifest lacks {list_field} list")
    result: list[dict[str, Any]] = []
    if list_field == "repairs":
        result.extend(normalize_one_repair(item) for item in raw_list)
    else:
        # EARLY staged contains both executable probes and documentation-only
        # deferred proposals.  Only explicitly simulated body fragments enter
        # the five regular variants.  Multi-fragment S13 is flattened with its
        # owner/index inherited from the parent proposal.
        for proposal in raw_list:
            if proposal.get("apply_to_simulation") is not True:
                continue
            require(proposal.get("kind") == "body",
                    f"simulated proposal is not body-local: {proposal.get('id')}")
            inherited = {
                "owner": proposal.get("owner"),
                "declaration_index": proposal.get("declaration_index"),
                "kind": "body",
                "confidence": proposal.get("confidence"),
            }
            if "old" in proposal or "new" in proposal:
                result.append(normalize_one_repair(proposal))
                continue
            replacements = proposal.get("replacements")
            require(isinstance(replacements, list) and replacements,
                    f"simulated proposal has no replacement: {proposal.get('id')}")
            result.extend(
                normalize_one_repair(replacement, inherited)
                for replacement in replacements
            )
    ids = [repair["id"] for repair in result]
    require(len(ids) == len(set(ids)), "duplicate normalized repair ID")
    return result


def main() -> int:
    bootstrap = argparse.ArgumentParser(add_help=False)
    bootstrap.add_argument("--base-composer", type=Path, required=True)
    bootstrap.add_argument("--base-composer-sha256", required=True)
    known, remaining = bootstrap.parse_known_args()

    module = load_locked_module(
        known.base_composer, known.base_composer_sha256
    )
    require(hasattr(module, "main") and hasattr(module, "normalize_manifest"),
            "base composer API mismatch")
    require(
        tuple(module.TRUST_TOKENS)
        == (
            "sorry",
            "admit",
            "axiom",
            "unsafe",
            "native_decide",
            "Lean.ofReduceBool",
        ),
        "base composer trust-token drift",
    )

    def normalize_v43(manifest: dict[str, Any]) -> dict[str, Any]:
        # Normalize only the six exact audited manifest layouts.
        return {
            "schema": module.SCHEMA,
            "status": manifest.get("status"),
            "authority": canonical_authority(manifest["authority"]),
            "repairs": canonical_repairs(manifest),
        }

    module.normalize_manifest = normalize_v43
    sys.argv = [sys.argv[0], *remaining]
    return int(module.main())


if __name__ == "__main__":
    raise SystemExit(main())
