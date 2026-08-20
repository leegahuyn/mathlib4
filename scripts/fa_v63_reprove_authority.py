#!/usr/bin/env python3
"""Re-prove the exact official v62 winner artifact before materialization.

This utility accepts only the locked run/jobs/artifact API payloads and the
locked ZIP.  It validates every input and all 48 flat member names in memory,
then exclusively emits the authority source, an attestation, and six immutable
BASE_* evidence copies required by the exact v63 result-artifact contract.
There is no repository-source, artifact-local-index, or other runtime fallback.
"""

from __future__ import annotations

import argparse
import io
import json
import os
import re
import sys
import zipfile
from pathlib import Path
from typing import Any

from fa_v63_contract import (
    BASE_AUTHORITY_COPIES,
    ContractError,
    canonical_authority_projection,
    sha256,
    validate_authority,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def read_json(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    require(path.is_file(), f"missing {label}: {path}")
    payload = path.read_bytes()
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"invalid {label} JSON: {exc}") from exc
    require(isinstance(value, dict), f"{label} root is not object")
    return value, payload


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)
            + "\n").encode("utf-8")


def exclusive_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
    except BaseException:
        try:
            path.unlink()
        except OSError:
            pass
        raise


def build_bundle(args: argparse.Namespace) -> tuple[bytes, bytes, dict[str, bytes]]:
    require(re.fullmatch(r"[0-9a-f]{64}", args.expected_authority_lock_sha256)
            is not None, "invalid expected authority-lock SHA")
    authority_bytes = (args.authority_lock.read_bytes()
                       if args.authority_lock.is_file() else b"")
    require(bool(authority_bytes), "authority lock missing")
    require(sha256(authority_bytes) == args.expected_authority_lock_sha256,
            "configured authority-lock SHA mismatch")
    authority = validate_authority(
        args.authority_lock, args.expected_authority_lock_sha256,
        len(authority_bytes))
    run, run_bytes = read_json(args.run_api, "run API")
    jobs, jobs_bytes = read_json(args.jobs_api, "jobs API")
    artifact, artifact_api_bytes = read_json(args.artifact_api, "artifact API")
    workflow = authority["workflow"]
    artifact_lock = authority["artifact"]
    require(run.get("id") == workflow["run_id"], "run API ID mismatch")
    require(run.get("run_attempt") == workflow["run_attempt"],
            "run API attempt mismatch")
    require(run.get("event") == workflow["event"], "run API event mismatch")
    require(run.get("name") == workflow["workflow_name"], "run API name mismatch")
    require(run.get("path") == workflow["workflow_path"], "run API path mismatch")
    require(run.get("head_branch") == workflow["head_branch"],
            "run API branch mismatch")
    require(run.get("head_sha") == workflow["head_sha"], "run API head mismatch")
    require(run.get("status") == "completed" and run.get("conclusion") == "failure",
            "run API terminal result mismatch")
    job_rows = jobs.get("jobs")
    require(isinstance(job_rows, list), "jobs API lacks jobs array")
    matched = [row for row in job_rows if row.get("id") == workflow["job_id"]]
    require(len(matched) == 1, "authority job not found exactly once")
    job = matched[0]
    require(job.get("name") == workflow["job_name"], "authority job name mismatch")
    require(job.get("status") == "completed"
            and job.get("conclusion") == workflow["job_conclusion"],
            "authority job terminal result mismatch")
    require(artifact.get("id") == artifact_lock["id"], "artifact API ID mismatch")
    require(artifact.get("name") == artifact_lock["name"], "artifact API name mismatch")
    require(artifact.get("size_in_bytes") == artifact_lock["size_in_bytes"],
            "artifact API size mismatch")
    require(artifact.get("digest") == artifact_lock["digest"],
            "artifact API digest mismatch")
    require(artifact.get("expired") is False, "artifact is expired")
    workflow_run = artifact.get("workflow_run", {})
    require(workflow_run.get("id") == workflow["run_id"]
            and workflow_run.get("head_sha") == workflow["head_sha"]
            and workflow_run.get("head_branch") == workflow["head_branch"],
            "artifact workflow provenance mismatch")
    require(args.artifact_zip.is_file(), "artifact ZIP missing")
    zip_payload = args.artifact_zip.read_bytes()
    require(sha256(zip_payload) == artifact_lock["zip_sha256"],
            "artifact ZIP SHA mismatch")
    require(len(zip_payload) == artifact_lock["zip_bytes"],
            "artifact ZIP byte mismatch")
    try:
        archive = zipfile.ZipFile(io.BytesIO(zip_payload), "r")
    except zipfile.BadZipFile as exc:
        raise ContractError(f"invalid artifact ZIP: {exc}") from exc
    with archive:
        infos = archive.infolist()
        names = [info.filename for info in infos]
        require(len(infos) == artifact_lock["member_count"],
                "artifact member count mismatch")
        require(len(set(names)) == len(names), "artifact contains duplicate member names")
        require(all(not info.is_dir() for info in infos),
                "artifact contains directory member")
        require(all("/" not in name and "\\" not in name
                    and name not in ("", ".", "..") for name in names),
                "artifact contains non-flat or unsafe member")
        require(sorted(names) == authority["expected_flat_members"],
                "artifact exact flat member set mismatch")
        members = {name: archive.read(name) for name in names}
    for name, lock in authority["member_locks"].items():
        payload = members.get(name)
        require(payload is not None, f"locked member missing: {name}")
        require(sha256(payload) == lock["sha256"] and len(payload) == lock["bytes"],
                f"locked member hash/byte mismatch: {name}")
    source_lock = authority["source"]
    source_payload = members[source_lock["member"]]
    try:
        source_text = source_payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ContractError("authority source member is not UTF-8") from exc
    require(len(source_text.splitlines()) == source_lock["lines"],
            "authority source member line mismatch")
    metric = json.loads(members["METRIC.json"])
    direct = authority["direct_chain"]
    require(metric.get("variant") == "fourier_pair", "authority metric variant mismatch")
    require(metric.get("source_sha256") == source_lock["sha256"],
            "authority metric source mismatch")
    require(metric.get("Mock2_exit") == direct["Mock2_exit"]
            and metric.get("Mock2_Advanced_exit") == direct["Mock2_Advanced_exit"]
            and metric.get("FA_exit") == direct["Mock2_FunctionalAnalysis_exit"],
            "authority metric exit mismatch")
    require(metric.get("FA_compile_max_errors") == 2000
            and metric.get("FA_error_headers_captured") == 8
            and metric.get("FA_warning_headers_captured") == 463
            and metric.get("FA_error_cap_sentinel_present") is False
            and metric.get("FA_inventory_complete_by_header_evidence") is True,
            "authority metric inventory mismatch")
    require(metric.get("source_declaration_count") == 4416
            and metric.get("source_executable_trust_six_zero") is True
            and metric.get("synthetic_declaration_uses_sorry_warning_count") == 0,
            "authority metric structural/trust mismatch")
    base_copies = {
        result_member: members[authority_member]
        for result_member, authority_member in BASE_AUTHORITY_COPIES
    }
    base_copy_locks = [
        {
            "result_member": result_member,
            "authority_member": authority_member,
            "sha256": sha256(base_copies[result_member]),
            "bytes": len(base_copies[result_member]),
        }
        for result_member, authority_member in BASE_AUTHORITY_COPIES
    ]
    all_member_locks = {
        name: {"sha256": sha256(members[name]), "bytes": len(members[name])}
        for name in sorted(members)
    }
    proof = {
        "schema": "fa-v63-v62-winner-authority-reproof-v1",
        "status": "EXACT",
        "authority_lock_sha256": args.expected_authority_lock_sha256,
        "authority": canonical_authority_projection(authority),
        "run_api": {"sha256": sha256(run_bytes), "bytes": len(run_bytes)},
        "jobs_api": {"sha256": sha256(jobs_bytes), "bytes": len(jobs_bytes)},
        "artifact_api": {
            "sha256": sha256(artifact_api_bytes), "bytes": len(artifact_api_bytes),
        },
        "artifact_zip": {"sha256": sha256(zip_payload), "bytes": len(zip_payload)},
        "flat_member_count": len(members),
        "flat_member_names": sorted(members),
        "source_sha256": sha256(source_payload),
        "source_bytes": len(source_payload),
        "source_lines": len(source_text.splitlines()),
        "declared_member_lock_count": len(authority["member_locks"]),
        "declared_member_locks": authority["member_locks"],
        "all_member_lock_count": len(all_member_locks),
        "all_member_locks": all_member_locks,
        "all_member_locks_derived_only_after_exact_zip_reproof": True,
        "base_authority_copies": base_copy_locks,
        "runtime_evidence_fallback_used": False,
        "repository_source_fallback_used": False,
        "embedded_artifact_authority_trusted_without_reproof": False,
        "direct_lean_invoked_by_reproof": False,
        "clean_claimed": False,
    }
    return source_payload, json_bytes(proof), base_copies


def build(args: argparse.Namespace) -> tuple[bytes, bytes]:
    """Compatibility wrapper used by read-only static/adversarial tests."""
    source, proof, _ = build_bundle(args)
    return source, proof


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--authority-lock", type=Path, required=True)
    parser.add_argument("--expected-authority-lock-sha256", required=True)
    parser.add_argument("--run-api", type=Path, required=True)
    parser.add_argument("--jobs-api", type=Path, required=True)
    parser.add_argument("--artifact-api", type=Path, required=True)
    parser.add_argument("--artifact-zip", type=Path, required=True)
    parser.add_argument("--source-output", type=Path, required=True)
    parser.add_argument("--proof-output", type=Path, required=True)
    parser.add_argument("--base-output-dir", type=Path, required=True)
    args = parser.parse_args()
    try:
        source, proof, base_copies = build_bundle(args)
        copy_paths = {
            result_member: args.base_output_dir / result_member
            for result_member in base_copies
        }
        outputs = [args.source_output, args.proof_output, *copy_paths.values()]
        resolved = [path.resolve() for path in outputs]
        require(len(set(resolved)) == len(resolved),
                "authority reproof outputs must be distinct")
        require(all(not path.exists() for path in outputs),
                "authority reproof output already exists")
    except (ContractError, OSError) as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        return 86
    for result_member, payload in base_copies.items():
        exclusive_write(copy_paths[result_member], payload)
    exclusive_write(args.proof_output, proof)
    exclusive_write(args.source_output, source)
    print(proof.decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
