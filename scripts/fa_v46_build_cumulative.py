#!/usr/bin/env python3
"""Fail-closed static composer for the saturated v46 FA repair wave.

This program never invokes Lean, Lake, git, GitHub, or the network.  It accepts
only a fully hydrated selection index, locks every input by SHA-256, requires
all 34 logical workers to have a terminal disposition, enforces ALL_OR_NONE
repair groups, and delegates declaration-local replacement/invariant parsing
to the locked v42 composer.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path
from typing import Any


SCRIPT_PATH = Path(__file__).resolve()
# The same locked file is audited from work/v46-cumulative locally and is
# promoted to scripts/ for GitHub Actions.  Resolve the repository root
# deterministically in both layouts without depending on the process cwd.
ROOT = (
    SCRIPT_PATH.parents[1]
    if SCRIPT_PATH.parent.name == "scripts"
    else SCRIPT_PATH.parents[2]
)
INDEX_SCHEMA = "fa-v46-cumulative-selection-v1"
QUEUE_SCHEMA = "fa-v46-logical-repair-worker-queue-v1"
MANIFEST_SCHEMA = "fa-v42-declaration-local-repairs-v1"
AUDIT_SCHEMA = "fa-v46-cumulative-static-audit-v1"
TERMINAL_DISPOSITIONS = {"PATCH_READY", "STAGED_PROBE", "DEFER", "CASCADE_DEFER"}
HEX_RE = re.compile(r"^[0-9a-f]{64}$")
DIFF_PREFIX_RE = re.compile(r"(?m)^\+")


def fail(message: str) -> None:
    raise SystemExit(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def locked_bytes(path: Path, expected_sha: str, label: str) -> bytes:
    require(HEX_RE.fullmatch(expected_sha) is not None, f"{label}: invalid SHA")
    require(path.is_file(), f"{label}: missing file: {path}")
    payload = path.read_bytes()
    require(sha256(payload) == expected_sha, f"{label}: SHA mismatch")
    return payload


def load_json_locked(path: Path, expected_sha: str, label: str) -> tuple[bytes, Any]:
    payload = locked_bytes(path, expected_sha, label)
    try:
        parsed = json.loads(payload)
    except Exception as exc:
        fail(f"{label}: invalid JSON: {exc}")
    return payload, parsed


def load_composer(path: Path, expected_sha: str):
    locked_bytes(path, expected_sha, "composer")
    spec = importlib.util.spec_from_file_location("fa_v46_locked_composer", path)
    require(spec is not None and spec.loader is not None, "cannot load composer")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    required = (
        "regions",
        "raw_headers",
        "comments_and_attributes",
        "trust_counts",
        "replace_in_owner",
    )
    require(all(hasattr(module, name) for name in required), "composer API mismatch")
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
        "composer trust-token drift",
    )
    return module


def input_path(record: dict[str, Any], allow_fallback: bool, label: str) -> Path:
    runtime = ROOT / str(record["path"])
    if runtime.is_file():
        return runtime
    if allow_fallback and record.get("source_path"):
        source = ROOT / str(record["source_path"])
        require(source.is_file(), f"{label}: missing fallback file: {source}")
        return source
    fail(f"{label}: missing runtime file: {runtime}")


def canonical_authority(
    value: dict[str, Any], *, missing_variant: str | None = None
) -> dict[str, Any]:
    keys = (
        "run_id",
        "head_sha",
        "job_id",
        "artifact_id",
        "artifact_digest",
        "variant",
        "source_path",
        "source_sha256",
        "source_bytes",
        "source_lines",
        "declaration_count",
    )
    normalized = dict(value)
    if "variant" not in normalized and missing_variant is not None:
        normalized["variant"] = missing_variant
    missing = [key for key in keys if key not in normalized]
    require(not missing, f"authority missing fields: {missing}")
    authority = {key: normalized[key] for key in keys}
    require(authority["run_id"] == 31728453514, "unexpected authority run")
    require(
        authority["head_sha"] == "5ec44f3d343955f3124e7efecc048b648dccc5ab",
        "unexpected authority head",
    )
    require(authority["job_id"] == 94542617528, "unexpected authority job")
    require(authority["artifact_id"] == 9192669673, "unexpected artifact")
    require(
        authority["artifact_digest"]
        == "sha256:8f07a678145b62342aaa9cb94ebbce6c9f7cc1a45c400560918d42499e67f2f3",
        "unexpected artifact digest",
    )
    require(authority["variant"] == "all_probes", "unexpected authority variant")
    require(
        authority["source_sha256"]
        == "726f40d1dd03d32f03592adf4f6b02e3f7f52e7e1f71087ee53bdb83c4bb0caf",
        "unexpected authority source",
    )
    require(authority["source_bytes"] == 2788764, "unexpected source bytes")
    require(authority["source_lines"] == 62383, "unexpected source lines")
    require(authority["declaration_count"] == 4416, "unexpected declaration count")
    return authority


def normalized_task_disposition(status: str) -> str:
    if status.startswith("PATCH_READY"):
        return "PATCH_READY"
    if status.startswith("STAGED_PROBE") or status.startswith("STAGED_"):
        return "STAGED_PROBE"
    if status.startswith("CASCADE_DEFER"):
        return "CASCADE_DEFER"
    if status.startswith("DEFER"):
        return "DEFER"
    return status


def validate_queue(queue: dict[str, Any]) -> dict[str, dict[str, Any]]:
    require(queue.get("schema") == QUEUE_SCHEMA, "queue schema mismatch")
    tasks = queue.get("tasks")
    require(isinstance(tasks, list) and len(tasks) >= 32, "fewer than 32 logical tasks")
    require(queue.get("task_count") == len(tasks) == 34, "task count mismatch")
    ids = [task.get("worker_id") for task in tasks]
    require(len(ids) == len(set(ids)), "duplicate queue worker ID")
    owners = [task.get("declaration_index") for task in tasks]
    require(len(owners) == len(set(owners)), "duplicate queue declaration owner")
    for task in tasks:
        disposition = normalized_task_disposition(str(task.get("status", "")))
        require(
            disposition in TERMINAL_DISPOSITIONS,
            f"nonterminal task {task.get('worker_id')}: {task.get('status')}",
        )
    return {str(task["worker_id"]): task for task in tasks}


def validate_repair(repair: dict[str, Any], worker: str) -> None:
    required = ("id", "owner", "declaration_index", "old", "new")
    missing = [key for key in required if key not in repair]
    require(not missing, f"{worker}: repair missing fields: {missing}")
    require(repair.get("kind", "body") == "body", f"{repair['id']}: non-body edit")
    require(isinstance(repair["old"], str) and repair["old"], f"{repair['id']}: empty OLD")
    require(isinstance(repair["new"], str) and repair["new"], f"{repair['id']}: empty NEW")
    require(repair["old"] != repair["new"], f"{repair['id']}: no-op")
    require(DIFF_PREFIX_RE.search(repair["new"]) is None, f"{repair['id']}: diff-prefix contamination")
    count = repair.get("expected_count_in_owner", 1)
    require(isinstance(count, int) and not isinstance(count, bool) and count > 0,
            f"{repair['id']}: invalid expected owner count")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--allow-source-path-fallback", action="store_true")
    args = parser.parse_args()

    index_payload = args.index.read_bytes()
    index = json.loads(index_payload)
    require(index.get("schema") == INDEX_SCHEMA, "selection index schema mismatch")
    require(index.get("status") == "READY", "selection index is not READY")
    require("PENDING" not in index_payload.decode("utf-8"), "selection index contains PENDING")

    composer_record = index.get("composer")
    require(isinstance(composer_record, dict), "missing composer lock")
    composer = load_composer(
        input_path(
            composer_record, args.allow_source_path_fallback, "composer"
        ),
        composer_record["sha256"],
    )

    queue_record = index.get("queue")
    require(isinstance(queue_record, dict), "missing queue lock")
    queue_payload, queue = load_json_locked(
        input_path(queue_record, args.allow_source_path_fallback, "queue"),
        queue_record["sha256"],
        "queue",
    )
    tasks = validate_queue(queue)

    index_authority = canonical_authority(index["authority"])
    queue_authority = queue["authority"]
    queue_authority_keys = (
        "run_id",
        "head_sha",
        "job_id",
        "artifact_id",
        "artifact_digest",
        "variant",
        "source_sha256",
    )
    queue_missing = [key for key in queue_authority_keys if key not in queue_authority]
    require(not queue_missing, f"queue authority missing fields: {queue_missing}")
    require(
        all(queue_authority[key] == index_authority[key] for key in queue_authority_keys),
        "queue/index authority mismatch",
    )

    variants = index.get("variants")
    require(isinstance(variants, list) and variants, "missing variants")
    matches = [variant for variant in variants if variant.get("name") == args.variant]
    require(len(matches) == 1, "requested variant is absent or duplicated")
    variant = matches[0]
    entries = variant.get("manifests")
    require(isinstance(entries, list) and entries, "variant has no manifests")

    selected_workers: list[str] = []
    manifest_audit: list[dict[str, Any]] = []
    repairs: list[dict[str, Any]] = []
    repair_workers: dict[str, str] = {}
    manifest_paths: set[str] = set()
    for entry in entries:
        worker = str(entry.get("worker_id"))
        require(worker in tasks, f"unknown worker in selection: {worker}")
        task_disposition = normalized_task_disposition(str(tasks[worker]["status"]))
        require(
            task_disposition == entry.get("disposition"),
            f"{worker}: selection disposition mismatch",
        )
        require(
            task_disposition in {"PATCH_READY", "STAGED_PROBE"},
            f"{worker}: non-executable disposition selected",
        )
        path_text = str(entry.get("path"))
        require(path_text not in manifest_paths, f"duplicate manifest path: {path_text}")
        manifest_paths.add(path_text)
        payload, manifest = load_json_locked(
            input_path(entry, args.allow_source_path_fallback, f"manifest {worker}"),
            str(entry.get("sha256")),
            f"manifest {worker}",
        )
        require(manifest.get("schema") == MANIFEST_SCHEMA, f"{worker}: schema mismatch")
        require(canonical_authority(
                    manifest["authority"], missing_variant=index_authority["variant"]
                ) == index_authority,
                f"{worker}: authority mismatch")
        manifest_repairs = manifest.get("repairs")
        require(isinstance(manifest_repairs, list) and manifest_repairs,
                f"{worker}: no repairs")
        expected_ids = entry.get("repair_ids")
        actual_ids = [repair.get("id") for repair in manifest_repairs]
        require(actual_ids == expected_ids, f"{worker}: repair ID/order mismatch")
        for repair in manifest_repairs:
            validate_repair(repair, worker)
            require(
                int(repair["declaration_index"])
                == int(tasks[worker]["declaration_index"]),
                f"{worker}: repair owner index differs from queue assignment",
            )
            require(
                repair["owner"] == tasks[worker]["declaration"],
                f"{worker}: repair owner name differs from queue assignment",
            )
            require(repair["id"] not in repair_workers, f"duplicate repair ID: {repair['id']}")
            repair_workers[repair["id"]] = worker
            repairs.append(repair)
        selected_workers.append(worker)
        manifest_audit.append(
            {
                "worker_id": worker,
                "path": path_text,
                "sha256": sha256(payload),
                "bytes": len(payload),
                "disposition": task_disposition,
                "repair_ids": actual_ids,
            }
        )

    require(len(selected_workers) == len(set(selected_workers)), "duplicate selected worker")

    selected_ids = set(repair_workers)
    atomic_groups = variant.get("atomic_groups", [])
    require(isinstance(atomic_groups, list), "atomic_groups must be a list")
    for group in atomic_groups:
        group_ids = group.get("repair_ids")
        require(isinstance(group_ids, list) and len(group_ids) >= 2,
                "invalid atomic repair group")
        selected_count = len(selected_ids.intersection(group_ids))
        require(
            selected_count in (0, len(group_ids)),
            f"atomic group partially selected: {group.get('id')}",
        )

    owner_workers: dict[int, str] = {}
    for repair in repairs:
        owner_index = int(repair["declaration_index"])
        worker = repair_workers[repair["id"]]
        previous = owner_workers.setdefault(owner_index, worker)
        require(previous == worker, f"cross-worker owner collision at {owner_index}")

    source_path = ROOT / index_authority["source_path"]
    source_payload = locked_bytes(
        source_path, index_authority["source_sha256"], "authority source"
    )
    require(len(source_payload) == index_authority["source_bytes"], "source byte mismatch")
    source = source_payload.decode("utf-8")
    require(len(source.splitlines()) == index_authority["source_lines"], "source line mismatch")
    before_regions = composer.regions(source)
    require(len(before_regions) == index_authority["declaration_count"], "source decl mismatch")
    before_names = [region["name"] for region in before_regions]
    before_headers = composer.raw_headers(source)
    before_comments, before_attrs = composer.comments_and_attributes(source)
    before_trust = composer.trust_counts(source)
    require(not any(before_trust.values()), f"authority trust tokens nonzero: {before_trust}")

    current = source
    applied: list[dict[str, Any]] = []
    # Python's sort is stable, so sorting only by owner index preserves the
    # explicitly locked order of multiple fragments within one owner.
    for repair in sorted(repairs, key=lambda item: int(item["declaration_index"])):
        current, record = composer.replace_in_owner(current, repair)
        record["worker_id"] = repair_workers[repair["id"]]
        applied.append(record)

    after_regions = composer.regions(current)
    after_names = [region["name"] for region in after_regions]
    after_headers = composer.raw_headers(current)
    after_comments, after_attrs = composer.comments_and_attributes(current)
    after_trust = composer.trust_counts(current)
    require(after_names == before_names, "declaration sequence changed")
    require(after_headers == before_headers, "declaration header changed")
    require(after_comments == before_comments, "comments changed")
    require(after_attrs == before_attrs, "attributes changed")
    require(after_trust == before_trust and not any(after_trust.values()), "trust counts changed")

    output_payload = current.encode("utf-8")
    expected = variant.get("expected_candidate")
    if expected is not None:
        require(sha256(output_payload) == expected.get("sha256"), "candidate SHA mismatch")
        require(len(output_payload) == expected.get("bytes"), "candidate byte mismatch")
        require(len(current.splitlines()) == expected.get("lines"), "candidate line mismatch")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(output_payload)
    audit = {
        "schema": AUDIT_SCHEMA,
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "selection_index": {
            "path": str(index.get("runtime_path", "scripts/fa_v46_selection.json")),
            "sha256": sha256(index_payload),
            "bytes": len(index_payload),
        },
        "queue": {
            "path": queue_record["path"],
            "sha256": sha256(queue_payload),
            "task_count": len(tasks),
            "all_tasks_terminal": True,
        },
        "variant": args.variant,
        "authority": index_authority,
        "manifests": manifest_audit,
        "selected_worker_count": len(selected_workers),
        "selected_repair_count": len(repairs),
        "selected_owner_count": len(owner_workers),
        "selected_workers": selected_workers,
        "atomic_groups_checked": [group.get("id") for group in atomic_groups],
        "applied": applied,
        "candidate_sha256": sha256(output_payload),
        "candidate_bytes": len(output_payload),
        "candidate_lines": len(current.splitlines()),
        "declaration_count": len(after_regions),
        "declaration_sequence_identical": True,
        "all_declaration_headers_byte_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "diff_prefix_contamination_rejected": True,
        "direct_lean_verified": False,
        "lean_lake_git_github_network_invoked": False,
    }
    audit_payload = (json.dumps(audit, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    args.audit.write_bytes(audit_payload)
    print(json.dumps(audit, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
