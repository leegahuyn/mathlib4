#!/usr/bin/env python3
"""Fail-closed materializer for the five locked FA v43 CI variants.

All index, dependency, authority, manifest, selected-ID, candidate, and audit
locks are checked before a candidate is accepted.  A pending index is rejected
with exit 86 and creates no outputs.

This script invokes only the locked v43 adapter and v42 static composer.  It
never invokes Lean, Lake, git, GitHub, or the network.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


SCHEMA = "fa-v43-five-variant-index-v1"
READY_STATUS = "STATIC_INPUTS_LOCKED_DIRECT_LEAN_UNVERIFIED"
BASE_AUDIT_SCHEMA = "fa-v42-local-repair-static-audit-v1"
AUDIT_SCHEMA = "fa-v43-five-variant-static-audit-v1"
HEX = set("0123456789abcdef")
EXIT_PENDING = 86
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


def require_sha(value: object, label: str) -> str:
    text = str(value)
    require(len(text) == 64 and set(text) <= HEX, f"{label}: invalid SHA-256")
    require(text != "0" * 64, f"{label}: zero SHA-256")
    return text


def contains_pending(value: Any) -> bool:
    if value is None:
        return True
    if isinstance(value, str):
        return value.startswith("PENDING")
    if isinstance(value, list):
        return any(contains_pending(item) for item in value)
    if isinstance(value, dict):
        return any(contains_pending(item) for item in value.values())
    return False


def manifest_repairs(payload: dict[str, Any]) -> list[dict[str, Any]]:
    layout = (payload.get("schema"), payload.get("status"))
    require(layout in ACCEPTED_LAYOUTS,
            f"manifest layout is not allowlisted: {layout}")
    field = ACCEPTED_LAYOUTS[layout]
    values = payload.get(field)
    require(isinstance(values, list), f"manifest lacks {field} list")
    if field == "repairs":
        result = list(values)
    else:
        result: list[dict[str, Any]] = []
        for proposal in values:
            if proposal.get("apply_to_simulation") is not True:
                continue
            require(proposal.get("kind") == "body",
                    f"selected proposal is non-body: {proposal.get('id')}")
            if "old" in proposal and "new" in proposal:
                result.append(proposal)
                continue
            replacements = proposal.get("replacements")
            require(isinstance(replacements, list) and replacements,
                    f"selected proposal lacks replacements: {proposal.get('id')}")
            for child in replacements:
                result.append({
                    "owner": proposal.get("owner"),
                    "declaration_index": proposal.get("declaration_index"),
                    **child,
                })
    for repair in result:
        require(repair.get("kind", "body") == "body",
                f"non-body repair rejected: {repair.get('id')}")
        for key in ("id", "owner", "declaration_index", "old", "new"):
            require(key in repair, f"repair field missing: {key}")
    ids = [str(repair["id"]) for repair in result]
    require(len(ids) == len(set(ids)), "duplicate normalized manifest ID")
    return result


def authority_projection(payload: dict[str, Any]) -> dict[str, Any]:
    authority = payload["authority"]
    digest = authority.get("artifact_digest")
    archive = authority.get("archive_sha256")
    if archive is not None:
        normalized = "sha256:" + archive
        if digest is None:
            digest = normalized
        else:
            require(digest == normalized,
                    "artifact_digest conflicts with archive_sha256")
    return {
        "run_id": int(authority["run_id"]),
        "head_sha": authority["head_sha"],
        "artifact_id": int(authority["artifact_id"]),
        "artifact_digest": digest,
        "source_sha256": authority["source_sha256"],
        "source_bytes": int(authority["source_bytes"]),
        "source_lines": int(authority["source_lines"]),
        "declaration_count": int(authority["declaration_count"]),
    }


def canonical_audit(
    base: dict[str, Any],
    variant_name: str,
    authority: dict[str, Any],
    manifests: list[dict[str, Any]],
) -> dict[str, Any]:
    require(base.get("schema") == BASE_AUDIT_SCHEMA,
            "base audit schema mismatch")
    require(base.get("status") == "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
            "base audit status mismatch")
    return {
        "schema": AUDIT_SCHEMA,
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "variant": variant_name,
        "authority": authority,
        "manifests": manifests,
        "selected_repair_ids": base["selected_repair_ids"],
        "selected_repair_count": base["selected_repair_count"],
        "selected_owner_count": base["selected_owner_count"],
        "applied": base["applied"],
        "candidate_sha256": base["candidate_sha256"],
        "candidate_bytes": base["candidate_bytes"],
        "candidate_lines": base["candidate_lines"],
        "declaration_count": base["declaration_count"],
        "declaration_sequence_identical": base[
            "declaration_sequence_identical"
        ],
        "all_declaration_headers_byte_identical": base[
            "all_declaration_headers_byte_identical"
        ],
        "comments_identical": base["comments_identical"],
        "attributes_identical": base["attributes_identical"],
        "trust_counts_before": base["trust_counts_before"],
        "trust_counts_after": base["trust_counts_after"],
        "direct_lean_verified": False,
        "lean_lake_git_github_invoked": False,
    }


def canonical_bytes(value: dict[str, Any]) -> bytes:
    return (
        json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--composer-wrapper", type=Path, required=True)
    parser.add_argument("--base-composer", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument(
        "--allow-source-path-fallback",
        action="store_true",
        help="Local static staging only; the GitHub workflow never sets this.",
    )
    args = parser.parse_args()

    index_bytes = args.index.read_bytes()
    index = json.loads(index_bytes)
    require(index.get("schema") == SCHEMA, "variant index schema mismatch")
    if index.get("status") != READY_STATUS or contains_pending(index):
        print(
            "v43 variant index is deliberately pending; refusing materialization",
            file=sys.stderr,
        )
        return EXIT_PENDING
    require(index.get("direct_lean_verified") is False,
            "index claims direct Lean verification")
    require(index.get("clean_build_claimed") is False,
            "index claims a clean build")
    require(index.get("runnable") is True, "ready index is not runnable")

    locks = index["scripts"]
    wrapper_bytes = args.composer_wrapper.read_bytes()
    base_bytes = args.base_composer.read_bytes()
    require(
        sha256(wrapper_bytes)
        == require_sha(locks["composer_wrapper"]["sha256"], "composer wrapper"),
        "composer wrapper SHA mismatch",
    )
    require(
        sha256(base_bytes)
        == require_sha(locks["base_composer"]["sha256"], "base composer"),
        "base composer SHA mismatch",
    )
    require(len(wrapper_bytes) == int(locks["composer_wrapper"]["bytes"]),
            "composer wrapper byte mismatch")
    require(len(base_bytes) == int(locks["base_composer"]["bytes"]),
            "base composer byte mismatch")

    authority = index["authority"]
    source_path = Path(authority["runtime_source_path"])
    source_bytes = source_path.read_bytes()
    require(
        sha256(source_bytes)
        == require_sha(authority["source_sha256"], "authority source"),
        "authority source SHA mismatch",
    )
    require(len(source_bytes) == int(authority["source_bytes"]),
            "authority source byte mismatch")
    source_text = source_bytes.decode("utf-8")
    require(len(source_text.splitlines()) == int(authority["source_lines"]),
            "authority source line mismatch")

    variants = index["variants"]
    require(args.variant in variants, f"unknown variant: {args.variant}")
    variant = variants[args.variant]
    require(variant.get("status") == "LOCKED", "variant is not locked")
    require(variant.get("runnable") is True, "variant is not runnable")
    require(
        variant.get("source_moves") == [],
        "regular v43 variants must exclude every source move",
    )
    selected_ids = list(variant["selected_repair_ids"])
    require(len(selected_ids) == len(set(selected_ids)),
            "duplicate selected repair ID")
    require(len(selected_ids) == int(variant["repair_count"]),
            "variant repair count mismatch")

    expected_authority = {
        "run_id": int(authority["run_id"]),
        "head_sha": authority["head_sha"],
        "artifact_id": int(authority["artifact_id"]),
        "artifact_digest": authority["artifact_digest"],
        "source_sha256": authority["source_sha256"],
        "source_bytes": int(authority["source_bytes"]),
        "source_lines": int(authority["source_lines"]),
        "declaration_count": int(authority["declaration_count"]),
    }
    registry = index["manifests"]
    available: dict[str, str] = {}
    manifest_paths: list[Path] = []
    manifest_evidence: list[dict[str, Any]] = []
    for key in variant["manifest_order"]:
        require(key in registry, f"unknown manifest key: {key}")
        record = registry[key]
        require(record.get("status") == "LOCKED", f"manifest {key} not locked")
        promoted_path = Path(record["promoted_path"])
        input_path = promoted_path
        used_source_fallback = False
        if not input_path.exists() and args.allow_source_path_fallback:
            input_path = Path(record["source_path"])
            used_source_fallback = True
        require(input_path.exists(), f"manifest {key} input missing")
        payload_bytes = input_path.read_bytes()
        expected_sha = require_sha(record["sha256"], f"manifest {key}")
        require(sha256(payload_bytes) == expected_sha,
                f"manifest {key} SHA mismatch")
        require(len(payload_bytes) == int(record["bytes"]),
                f"manifest {key} byte mismatch")
        payload = json.loads(payload_bytes)
        repairs = manifest_repairs(payload)
        source_values = payload.get(
            ACCEPTED_LAYOUTS[(payload.get("schema"), payload.get("status"))]
        )
        require(len(source_values) == int(record["source_entries"]),
                f"manifest {key} source-entry mismatch")
        require(len(repairs) == int(record["repair_entries"]),
                f"manifest {key} repair-entry mismatch")
        require(payload.get("schema") == record["schema"],
                f"manifest {key} schema mismatch")
        require(payload.get("status") == record["manifest_status"],
                f"manifest {key} status mismatch")
        require(authority_projection(payload) == expected_authority,
                f"manifest {key} authority mismatch")
        repair_ids = [str(repair["id"]) for repair in repairs]
        require(repair_ids == record["repair_ids"],
                f"manifest {key} repair-ID order mismatch")
        owner_count = len({str(repair["owner"]) for repair in repairs})
        require(owner_count == int(record["owner_count"]),
                f"manifest {key} owner-count mismatch")
        for repair in repairs:
            repair_id = str(repair["id"])
            require(repair_id not in available,
                    f"duplicate repair ID across manifests: {repair_id}")
            available[repair_id] = key

        manifest_paths.append(input_path)
        manifest_evidence.append({
            "key": key,
            "promoted_path": record["promoted_path"],
            "schema": record["schema"],
            "manifest_status": record["manifest_status"],
            "sha256": expected_sha,
            "bytes": len(payload_bytes),
            "source_entries": len(source_values),
            "repair_entries": len(repairs),
            "owner_count": owner_count,
            "repair_ids": repair_ids,
        })

    missing = set(selected_ids) - set(available)
    require(not missing,
            f"selected repair IDs absent from manifests: {sorted(missing)}")
    for relation in variant.get("supersedes", []):
        replacement = relation["replacement"]
        excluded = relation["excluded"]
        require(replacement in selected_ids,
                f"superseding repair absent: {replacement}")
        require(excluded not in selected_ids,
                f"superseded repair still selected: {excluded}")

    with tempfile.TemporaryDirectory(prefix="fa-v43-materialize-") as temp:
        temp_root = Path(temp)
        temp_candidate = temp_root / "candidate.lean"
        temp_base_audit = temp_root / "base-audit.json"
        command = [
            sys.executable,
            str(args.composer_wrapper),
            "--base-composer", str(args.base_composer),
            "--base-composer-sha256", locks["base_composer"]["sha256"],
        ]
        for path in manifest_paths:
            command.extend(("--manifest", str(path)))
        for repair_id in selected_ids:
            command.extend(("--repair-id", repair_id))
        command.extend((
            "--output", str(temp_candidate),
            "--audit", str(temp_base_audit),
        ))
        completed = subprocess.run(
            command, check=False, capture_output=True, text=True,
            encoding="utf-8", errors="replace"
        )
        require(completed.returncode == 0,
                f"static composer failed: {completed.stderr}")

        candidate_bytes = temp_candidate.read_bytes()
        base_audit = json.loads(temp_base_audit.read_bytes())
    audit = canonical_audit(
        base_audit, args.variant, expected_authority, manifest_evidence
    )
    audit_bytes = canonical_bytes(audit)
    expected_candidate = require_sha(variant["candidate_sha256"], "candidate")
    require(sha256(candidate_bytes) == expected_candidate,
            "candidate SHA mismatch")
    require(len(candidate_bytes) == int(variant["candidate_bytes"]),
            "candidate byte mismatch")
    candidate_text = candidate_bytes.decode("utf-8")
    require(len(candidate_text.splitlines()) == int(variant["candidate_lines"]),
            "candidate line mismatch")

    expected_audit = require_sha(variant["audit_sha256"], "audit")
    require(sha256(audit_bytes) == expected_audit, "audit SHA mismatch")
    require(len(audit_bytes) == int(variant["audit_bytes"]),
            "audit byte mismatch")
    require(len(audit_bytes.decode("utf-8").splitlines()) ==
            int(variant["audit_lines"]), "audit line mismatch")
    require(audit.get("schema") == AUDIT_SCHEMA, "audit schema mismatch")
    require(audit.get("status") == "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
            "audit status mismatch")
    require(audit.get("candidate_sha256") == expected_candidate,
            "audit candidate mismatch")
    require(audit.get("selected_repair_ids") == selected_ids,
            "audit selected-ID order mismatch")
    require(audit.get("selected_repair_count") == int(variant["repair_count"]),
            "audit repair count mismatch")
    require(audit.get("selected_owner_count") == int(variant["owner_count"]),
            "audit owner count mismatch")
    require(audit.get("declaration_count") == 4416,
            "audit declaration count mismatch")
    for field in (
        "declaration_sequence_identical",
        "all_declaration_headers_byte_identical",
        "comments_identical",
        "attributes_identical",
    ):
        require(audit.get(field) is True, f"audit invariant failed: {field}")
    require(all(value == 0 for value in audit["trust_counts_before"].values()),
            "authority trust nonzero")
    require(all(value == 0 for value in audit["trust_counts_after"].values()),
            "candidate trust nonzero")
    require(audit.get("direct_lean_verified") is False,
            "audit claims direct Lean verification")

    # No externally visible output is written until every input and output lock
    # above has passed.
    for destination in (args.output, args.audit, args.evidence):
        destination.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(candidate_bytes)
    args.audit.write_bytes(audit_bytes)
    evidence = {
        "schema": "fa-v43-materialization-evidence-v1",
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "variant": args.variant,
        "index_sha256": sha256(index_bytes),
        "composer_wrapper_sha256": sha256(wrapper_bytes),
        "base_composer_sha256": sha256(base_bytes),
        "authority_source_sha256": sha256(source_bytes),
        "manifests": manifest_evidence,
        "selected_repair_count": len(selected_ids),
        "selected_owner_count": audit["selected_owner_count"],
        "candidate_sha256": sha256(candidate_bytes),
        "candidate_bytes": len(candidate_bytes),
        "candidate_lines": len(candidate_text.splitlines()),
        "audit_sha256": sha256(audit_bytes),
        "declaration_count": audit["declaration_count"],
        "headers_comments_attributes_preserved": True,
        "trust_counts_before": audit["trust_counts_before"],
        "trust_counts_after": audit["trust_counts_after"],
        "direct_lean_verified": False,
        "lean_lake_git_github_invoked_by_materializer": False,
    }
    args.evidence.write_bytes(canonical_bytes(evidence))
    print(json.dumps(evidence, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
