#!/usr/bin/env python3
"""Fail-closed materializer for the six locked FA v45 CI variants.

The v45 manifests all use the standard v42 owner-local repair schema, so this
materializer invokes the SHA-locked v42 composer directly.  It writes no
externally visible output until authority, manifest, selection, pair, M13,
candidate, and canonical-audit locks all pass.  A pending index exits 2.
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


SCHEMA = "fa-v45-six-variant-index-v1"
MANIFEST_SCHEMA = "fa-v42-declaration-local-repairs-v1"
READY_STATUS = "STATIC_INPUTS_LOCKED_DIRECT_LEAN_UNVERIFIED"
BASE_AUDIT_SCHEMA = "fa-v42-local-repair-static-audit-v1"
AUDIT_SCHEMA = "fa-v45-six-variant-static-audit-v1"
VARIANTS = {
    "core", "common_probe", "q1_probe", "q2_probe", "q3_probe",
    "all_probes",
}
HEX = set("0123456789abcdef")
EXIT_PENDING = 2
TRUST_KEYS = (
    "sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def require_sha(value: Any, label: str) -> str:
    text = str(value)
    require(len(text) == 64 and set(text) <= HEX and text != "0" * 64,
            f"{label}: invalid SHA-256")
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


def canonical_bytes(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def authority_projection(payload: dict[str, Any]) -> dict[str, Any]:
    authority = payload["authority"]
    return {
        "run_id": int(authority["run_id"]),
        "head_sha": str(authority["head_sha"]),
        "job_id": int(authority["job_id"]),
        "artifact_id": int(authority["artifact_id"]),
        "artifact_digest": str(authority["artifact_digest"]),
        "source_path": str(authority["source_path"]),
        "source_sha256": str(authority["source_sha256"]),
        "source_bytes": int(authority["source_bytes"]),
        "source_lines": int(authority["source_lines"]),
        "declaration_count": int(authority["declaration_count"]),
    }


def manifest_repairs(payload: dict[str, Any]) -> list[dict[str, Any]]:
    require(payload.get("schema") == MANIFEST_SCHEMA,
            "manifest schema mismatch")
    repairs = payload.get("repairs")
    require(isinstance(repairs, list), "manifest repairs list missing")
    ids: list[str] = []
    for repair in repairs:
        require(repair.get("kind", "body") == "body",
                f"non-body repair: {repair.get('id')}")
        for key in ("id", "owner", "declaration_index", "old", "new"):
            require(key in repair, f"repair field missing: {key}")
        canonical = repair.get("expected_count_in_owner")
        alias = repair.get("expected_owner_count")
        if canonical is not None and alias is not None:
            require(not isinstance(canonical, bool) and
                    not isinstance(alias, bool) and int(canonical) == int(alias),
                    f"conflicting owner counts: {repair['id']}")
        ids.append(str(repair["id"]))
    require(len(ids) == len(set(ids)), "duplicate repair ID within manifest")
    return list(repairs)


def canonical_audit(
    base: dict[str, Any], variant: str, authority: dict[str, Any],
    manifests: list[dict[str, Any]],
) -> dict[str, Any]:
    require(base.get("schema") == BASE_AUDIT_SCHEMA,
            "base audit schema mismatch")
    require(base.get("status") == "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
            "base audit status mismatch")
    return {
        "schema": AUDIT_SCHEMA,
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "variant": variant,
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
        "declaration_sequence_identical": base["declaration_sequence_identical"],
        "all_declaration_headers_byte_identical": base[
            "all_declaration_headers_byte_identical"
        ],
        "comments_identical": base["comments_identical"],
        "attributes_identical": base["attributes_identical"],
        "trust_counts_before": base["trust_counts_before"],
        "trust_counts_after": base["trust_counts_after"],
        "m13_excluded": True,
        "direct_lean_verified": False,
        "lean_lake_git_github_invoked": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--base-composer", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--allow-source-path-fallback", action="store_true")
    args = parser.parse_args()

    index_bytes = args.index.read_bytes()
    index = json.loads(index_bytes)
    require(index.get("schema") == SCHEMA, "variant index schema mismatch")
    if index.get("status") != READY_STATUS or contains_pending(index):
        print("v45 index is pending; refusing materialization", file=sys.stderr)
        return EXIT_PENDING
    require(index.get("runnable") is True, "ready index is not runnable")
    require(index.get("direct_lean_verified") is False,
            "index claims direct Lean verification")
    require(index.get("clean_build_claimed") is False,
            "index claims a clean build")
    require(set(index.get("variants", {})) == VARIANTS,
            "six-variant set mismatch")
    require(args.variant in VARIANTS, f"unknown variant: {args.variant}")

    base_bytes = args.base_composer.read_bytes()
    base_lock = index["scripts"]["base_composer"]
    require(sha256(base_bytes) == require_sha(base_lock["sha256"], "base composer"),
            "base composer SHA mismatch")
    require(len(base_bytes) == int(base_lock["bytes"]),
            "base composer byte mismatch")

    authority = index["authority"]
    expected_authority = {
        "run_id": int(authority["run_id"]),
        "head_sha": str(authority["head_sha"]),
        "job_id": int(authority["job_id"]),
        "artifact_id": int(authority["artifact_id"]),
        "artifact_digest": str(authority["artifact_digest"]),
        "source_path": str(authority["runtime_source_path"]),
        "source_sha256": str(authority["source_sha256"]),
        "source_bytes": int(authority["source_bytes"]),
        "source_lines": int(authority["source_lines"]),
        "declaration_count": int(authority["declaration_count"]),
    }
    source_path = Path(expected_authority["source_path"])
    source_bytes = source_path.read_bytes()
    require(sha256(source_bytes) == require_sha(
        expected_authority["source_sha256"], "authority source"),
        "authority source SHA mismatch")
    require(len(source_bytes) == expected_authority["source_bytes"],
            "authority source byte mismatch")
    require(len(source_bytes.decode("utf-8").splitlines()) ==
            expected_authority["source_lines"], "authority source line mismatch")

    excluded = index.get("excluded_source_moves", {}).get("middle_m13", {})
    require(excluded.get("selected_by") == [], "M13 must be excluded")

    variant = index["variants"][args.variant]
    require(variant.get("status") == "LOCKED", "variant is not locked")
    require(variant.get("runnable") is True, "variant is not runnable")
    require(variant.get("source_moves") == [], "source moves are forbidden")
    selected_ids = [str(value) for value in variant["selected_repair_ids"]]
    require(len(selected_ids) == len(set(selected_ids)),
            "duplicate selected repair ID")
    require(len(selected_ids) == int(variant["repair_count"]),
            "repair count mismatch")

    registry = index["manifests"]
    available: dict[str, str] = {}
    paths: list[Path] = []
    evidence_rows: list[dict[str, Any]] = []
    for key in variant["manifest_order"]:
        require(key in registry, f"unknown manifest key: {key}")
        record = registry[key]
        require(record.get("status") == "LOCKED", f"manifest not locked: {key}")
        runtime = Path(record["runtime_path"])
        path = runtime
        used_fallback = False
        if not path.exists() and args.allow_source_path_fallback:
            path = Path(record["source_path"])
            used_fallback = True
        require(path.is_file(), f"manifest input missing: {key}")
        payload_bytes = path.read_bytes()
        require(sha256(payload_bytes) == require_sha(record["sha256"], key),
                f"manifest SHA mismatch: {key}")
        require(len(payload_bytes) == int(record["bytes"]),
                f"manifest byte mismatch: {key}")
        payload = json.loads(payload_bytes)
        require(payload.get("status") == record["manifest_status"],
                f"manifest status mismatch: {key}")
        require(authority_projection(payload) == expected_authority,
                f"manifest authority mismatch: {key}")
        repairs = manifest_repairs(payload)
        ids = [str(repair["id"]) for repair in repairs]
        require(ids == record["repair_ids"],
                f"manifest repair-ID order mismatch: {key}")
        require(len(repairs) == int(record["repair_entries"]),
                f"manifest repair count mismatch: {key}")
        owners = {int(repair["declaration_index"]) for repair in repairs}
        require(len(owners) == int(record["owner_count"]),
                f"manifest owner count mismatch: {key}")
        for repair_id in ids:
            require(repair_id not in available,
                    f"duplicate repair ID across manifests: {repair_id}")
            available[repair_id] = key
        paths.append(path)
        evidence_rows.append({
            "key": key,
            "runtime_path": record["runtime_path"],
            "used_source_fallback": used_fallback,
            "schema": payload["schema"],
            "manifest_status": payload["status"],
            "sha256": sha256(payload_bytes),
            "bytes": len(payload_bytes),
            "repair_entries": len(repairs),
            "owner_count": len(owners),
            "repair_ids": ids,
        })

    missing = set(selected_ids) - set(available)
    require(not missing, f"selected IDs absent: {sorted(missing)}")
    for contract in index.get("pair_contracts", []):
        ids = set(contract["repair_ids"])
        selected = ids & set(selected_ids)
        require(not selected or selected == ids,
                f"pair contract partially selected: {contract['id']}")

    with tempfile.TemporaryDirectory(prefix="fa-v45-materialize-") as temp:
        temp_root = Path(temp)
        temp_candidate = temp_root / "candidate.lean"
        temp_base_audit = temp_root / "base-audit.json"
        command = [sys.executable, str(args.base_composer)]
        for path in paths:
            command.extend(("--manifest", str(path)))
        for repair_id in selected_ids:
            command.extend(("--repair-id", repair_id))
        command.extend(("--output", str(temp_candidate),
                        "--audit", str(temp_base_audit)))
        completed = subprocess.run(
            command, check=False, capture_output=True, text=True,
            encoding="utf-8", errors="replace"
        )
        require(completed.returncode == 0,
                f"static composer failed: {completed.stderr}")
        candidate_bytes = temp_candidate.read_bytes()
        base_audit = json.loads(temp_base_audit.read_bytes())

    audit = canonical_audit(
        base_audit, args.variant, expected_authority, evidence_rows
    )
    audit_bytes = canonical_bytes(audit)
    expected_candidate = require_sha(variant["candidate_sha256"], "candidate")
    expected_audit = require_sha(variant["audit_sha256"], "audit")
    require(sha256(candidate_bytes) == expected_candidate,
            "candidate SHA mismatch")
    require(len(candidate_bytes) == int(variant["candidate_bytes"]),
            "candidate byte mismatch")
    require(len(candidate_bytes.decode("utf-8").splitlines()) ==
            int(variant["candidate_lines"]), "candidate line mismatch")
    require(sha256(audit_bytes) == expected_audit, "audit SHA mismatch")
    require(len(audit_bytes) == int(variant["audit_bytes"]),
            "audit byte mismatch")
    require(audit["selected_repair_ids"] == selected_ids,
            "audit selected-ID mismatch")
    require(audit["selected_owner_count"] == int(variant["owner_count"]),
            "audit owner count mismatch")
    require(audit["declaration_count"] == 4416, "declaration count mismatch")
    for key in ("declaration_sequence_identical",
                "all_declaration_headers_byte_identical",
                "comments_identical", "attributes_identical"):
        require(audit.get(key) is True, f"audit invariant failed: {key}")
    require(all(audit["trust_counts_after"].get(key) == 0
                for key in TRUST_KEYS), "candidate trust six nonzero")

    evidence = {
        "schema": "fa-v45-materialization-evidence-v1",
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "variant": args.variant,
        "index_sha256": sha256(index_bytes),
        "base_composer_sha256": sha256(base_bytes),
        "authority_source_sha256": sha256(source_bytes),
        "manifests": evidence_rows,
        "selected_repair_count": len(selected_ids),
        "selected_owner_count": audit["selected_owner_count"],
        "candidate_sha256": sha256(candidate_bytes),
        "candidate_bytes": len(candidate_bytes),
        "candidate_lines": len(candidate_bytes.decode("utf-8").splitlines()),
        "audit_sha256": sha256(audit_bytes),
        "declaration_count": 4416,
        "m13_excluded": True,
        "headers_comments_attributes_preserved": True,
        "trust_counts_after": audit["trust_counts_after"],
        "direct_lean_verified": False,
        "lean_lake_git_github_invoked_by_materializer": False,
    }
    for destination in (args.output, args.audit, args.evidence):
        destination.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(candidate_bytes)
    args.audit.write_bytes(audit_bytes)
    args.evidence.write_bytes(canonical_bytes(evidence))
    print(json.dumps(evidence, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
