#!/usr/bin/env python3
"""Fail-closed materializer for the two FA v42 GitHub CI variants.

The script verifies the variant index, composer, authority source, manifests,
selection/supersession contract, and deterministic candidate/audit identities.
It invokes only the locked static composer; it never invokes Lean, Lake, git,
GitHub, or the network.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


SCHEMA = "fa-v42-two-variant-index-v1"
AUDIT_SCHEMA = "fa-v42-local-repair-static-audit-v1"
HEX = set("0123456789abcdef")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{path}: top level must be an object")
    return value


def require_sha(value: object, label: str) -> str:
    text = str(value)
    require(len(text) == 64 and set(text) <= HEX, f"{label}: invalid SHA-256")
    require(text != "0" * 64, f"{label}: pending SHA-256")
    return text


def manifest_repairs(payload: dict[str, Any]) -> list[dict[str, Any]]:
    schema = payload.get("schema")
    if schema == "fa-v42-declaration-local-repairs-v1":
        repairs = payload.get("repairs")
    elif schema == "fa-v42-q1-root-repair-manifest-v1":
        repairs = list(payload.get("promoted_repairs", [])) + list(
            payload.get("staged_repairs", [])
        )
    else:
        raise SystemExit(f"unsupported manifest schema: {schema}")
    require(isinstance(repairs, list), "manifest repairs must be a list")
    return repairs


def load_composer(path: Path):
    spec = importlib.util.spec_from_file_location("fa_v42_locked_composer", path)
    require(spec is not None and spec.loader is not None, "cannot load composer")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--composer", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument(
        "--allow-source-path-fallback",
        action="store_true",
        help=(
            "Static package-staging replay only: use each locked source_path "
            "when its promoted_path is absent. The GitHub workflow omits this flag."
        ),
    )
    args = parser.parse_args()

    index_bytes = args.index.read_bytes()
    index = json.loads(index_bytes)
    require(index.get("schema") == SCHEMA, "variant index schema mismatch")
    require(
        index.get("status") == "STATIC_INPUTS_LOCKED_DIRECT_LEAN_UNVERIFIED",
        "variant index is not locked",
    )
    require(index.get("direct_lean_verified") is False, "index claims Lean verification")

    composer_lock = index["composer"]
    composer_bytes = args.composer.read_bytes()
    require(
        sha256(composer_bytes) == require_sha(composer_lock["sha256"], "composer"),
        "composer SHA mismatch",
    )
    require(len(composer_bytes) == int(composer_lock["bytes"]), "composer byte mismatch")
    composer = load_composer(args.composer)
    require(tuple(composer.TRUST_TOKENS) == tuple(index["trust_tokens"]), "trust token drift")

    authority = index["authority"]
    source_path = Path(authority["runtime_source_path"])
    source_bytes = source_path.read_bytes()
    require(
        sha256(source_bytes) == require_sha(authority["source_sha256"], "authority source"),
        "authority source SHA mismatch",
    )
    require(len(source_bytes) == int(authority["source_bytes"]), "authority source byte mismatch")
    source_text = source_bytes.decode("utf-8")
    require(len(source_text.splitlines()) == int(authority["source_lines"]), "authority line mismatch")
    require(len(composer.regions(source_text)) == 4416, "authority declaration mismatch")
    require(all(value == 0 for value in composer.trust_counts(source_text).values()), "authority trust nonzero")

    variants = index["variants"]
    require(args.variant in variants, f"unknown variant: {args.variant}")
    variant = variants[args.variant]
    selected_ids = list(variant["selected_repair_ids"])
    require(len(selected_ids) == len(set(selected_ids)), "duplicate selected repair ID")
    require(len(selected_ids) == int(variant["repair_count"]), "repair count/index mismatch")

    registry = index["manifests"]
    runtime_paths: list[Path] = []
    available: dict[str, str] = {}
    manifest_evidence: list[dict[str, Any]] = []
    for key in variant["manifest_order"]:
        require(key in registry, f"unknown manifest key: {key}")
        record = registry[key]
        promoted_path = Path(record["promoted_path"])
        input_path = promoted_path
        used_source_fallback = False
        if not input_path.exists() and args.allow_source_path_fallback:
            input_path = Path(record["source_path"])
            used_source_fallback = True
        require(input_path.exists(), f"manifest {key} promoted input is missing")
        promoted_bytes = input_path.read_bytes()
        expected_sha = require_sha(record["sha256"], f"manifest {key}")
        require(sha256(promoted_bytes) == expected_sha, f"manifest {key} SHA mismatch")
        require(len(promoted_bytes) == int(record["bytes"]), f"manifest {key} byte mismatch")
        payload = json.loads(promoted_bytes)
        repairs = manifest_repairs(payload)
        require(len(repairs) == int(record["repair_entries"]), f"manifest {key} entry mismatch")
        for repair in repairs:
            repair_id = str(repair["id"])
            require(repair_id not in available, f"duplicate repair ID across manifests: {repair_id}")
            available[repair_id] = key

        runtime_path = Path(record["runtime_path"])
        runtime_path.parent.mkdir(parents=True, exist_ok=True)
        if input_path.resolve() != runtime_path.resolve():
            shutil.copyfile(input_path, runtime_path)
        require(runtime_path.read_bytes() == promoted_bytes, f"manifest {key} runtime copy drift")
        runtime_paths.append(runtime_path)
        manifest_evidence.append(
            {
                "key": key,
                "promoted_path": promoted_path.as_posix(),
                "input_path": input_path.as_posix(),
                "used_source_path_fallback": used_source_fallback,
                "runtime_path": runtime_path.as_posix(),
                "sha256": expected_sha,
                "bytes": len(promoted_bytes),
                "repair_entries": len(repairs),
            }
        )

    missing = set(selected_ids) - set(available)
    require(not missing, f"selected repair IDs absent from variant manifests: {sorted(missing)}")
    for relation in variant.get("supersedes", []):
        replacement = relation["replacement"]
        excluded = relation["excluded"]
        require(replacement in selected_ids, f"superseding repair absent: {replacement}")
        require(excluded not in selected_ids, f"superseded repair still selected: {excluded}")

    command = [
        sys.executable,
        str(args.composer),
    ]
    for path in runtime_paths:
        command.extend(("--manifest", str(path)))
    for repair_id in selected_ids:
        command.extend(("--repair-id", repair_id))
    command.extend(("--output", str(args.output), "--audit", str(args.audit)))
    completed = subprocess.run(command, check=False, text=True, capture_output=True)
    require(completed.returncode == 0, f"composer failed: {completed.stderr}")

    candidate_bytes = args.output.read_bytes()
    expected_candidate = require_sha(variant["candidate_sha256"], "candidate")
    require(sha256(candidate_bytes) == expected_candidate, "candidate SHA mismatch")
    require(len(candidate_bytes) == int(variant["candidate_bytes"]), "candidate byte mismatch")
    candidate_text = candidate_bytes.decode("utf-8")
    require(len(candidate_text.splitlines()) == int(variant["candidate_lines"]), "candidate line mismatch")

    # The authoritative local audit was emitted by Python on Windows and is
    # intentionally locked with CRLF. Normalize deterministically so Ubuntu
    # reproduces the same byte identity instead of maintaining an OS-specific
    # second audit lock.
    audit_lf = args.audit.read_bytes().replace(b"\r\n", b"\n")
    args.audit.write_bytes(audit_lf.replace(b"\n", b"\r\n"))
    audit_bytes = args.audit.read_bytes()
    expected_audit = require_sha(variant["audit_sha256"], "audit")
    require(sha256(audit_bytes) == expected_audit, "audit SHA mismatch")
    require(len(audit_bytes) == int(variant["audit_bytes"]), "audit byte mismatch")
    audit = json.loads(audit_bytes)
    require(audit.get("schema") == AUDIT_SCHEMA, "audit schema mismatch")
    require(audit.get("status") == "STATIC_PASS_DIRECT_LEAN_UNVERIFIED", "audit status mismatch")
    require(audit.get("candidate_sha256") == expected_candidate, "audit candidate mismatch")
    require(audit.get("selected_repair_ids") == selected_ids, "audit selection/order mismatch")
    require(audit.get("selected_repair_count") == int(variant["repair_count"]), "audit repair count mismatch")
    require(audit.get("selected_owner_count") == int(variant["owner_count"]), "audit owner count mismatch")
    require(audit.get("declaration_count") == 4416, "audit declaration count mismatch")
    for field in (
        "declaration_sequence_identical",
        "all_declaration_headers_byte_identical",
        "comments_identical",
        "attributes_identical",
    ):
        require(audit.get(field) is True, f"audit invariant failed: {field}")
    require(all(value == 0 for value in audit["trust_counts_before"].values()), "audit source trust nonzero")
    require(all(value == 0 for value in audit["trust_counts_after"].values()), "audit candidate trust nonzero")
    require(audit.get("direct_lean_verified") is False, "audit claims Lean verification")

    args.evidence.parent.mkdir(parents=True, exist_ok=True)
    evidence = {
        "schema": "fa-v42-materialization-evidence-v1",
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "variant": args.variant,
        "index_sha256": sha256(index_bytes),
        "composer_sha256": sha256(composer_bytes),
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
    args.evidence.write_text(
        json.dumps(evidence, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(evidence, indent=2, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
