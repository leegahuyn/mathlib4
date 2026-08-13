#!/usr/bin/env python3
"""Add the two body-only conditional probe bundles to a locked v41 candidate.

M13's source move is intentionally unsupported here.  This script emits a
second candidate for the same full direct-compile matrix; it never treats the
conditional repairs as proven before that compile.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
from typing import Any


INDEX_SCHEMA = "fa-v41-conditional-probe-index-v1"
AUDIT_SCHEMA = "fa-v41-conditional-probe-static-audit-v1"
ALLOWED_SECTIONS = ("M05_M06", "LR_BODY")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"{path}: expected a JSON object")
    return value


def load_core(path: Path) -> Any:
    spec = importlib.util.spec_from_file_location("v41_core", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"cannot load core builder: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def apply_conditional_section(
    core: Any,
    source: str,
    section: str,
    manifest: dict[str, Any],
) -> tuple[str, list[dict[str, Any]], set[str]]:
    """Apply staged fragments in their unique declaration-owner regions."""
    current = source
    applied: list[dict[str, Any]] = []
    owners_used: set[str] = set()
    local_ids: set[str] = set()
    repairs = manifest.get("repairs")
    if not isinstance(repairs, list) or not repairs:
        raise SystemExit(f"{section}: conditional manifest has no repairs")
    for repair in repairs:
        if not isinstance(repair, dict):
            raise SystemExit(f"{section}: repair entry is not an object")
        repair_id = str(repair.get("id", ""))
        if not repair_id or repair_id in local_ids:
            raise SystemExit(f"{section}: missing/duplicate repair id {repair_id!r}")
        local_ids.add(repair_id)
        if int(repair.get("expected_count", 1)) != 1 or "owners" in repair:
            raise SystemExit(f"{section}/{repair_id}: expected one declaration owner")
        owner = repair.get("owner")
        if not isinstance(owner, str) or not owner:
            raise SystemExit(f"{section}/{repair_id}: missing owner")
        regions = [region for region in core.declaration_regions(current) if region["name"] == owner]
        if len(regions) != 1:
            raise SystemExit(
                f"{section}/{repair_id}: owner count {len(regions)} for {owner}"
            )
        region = regions[0]
        old = repair.get("old")
        new = repair.get("new")
        if not isinstance(old, str) or not isinstance(new, str) or not old or old == new:
            raise SystemExit(f"{section}/{repair_id}: invalid old/new fragment")
        body = current[region["start"] : region["end"]]
        if body.count(old) != 1:
            raise SystemExit(
                f"{section}/{repair_id}: owner-local old count {body.count(old)} != 1"
            )
        if new not in old and new in body:
            raise SystemExit(f"{section}/{repair_id}: new fragment already present in owner")
        edited = body.replace(old, new, 1)
        current = current[: region["start"]] + edited + current[region["end"] :]
        owners_used.add(owner)
        applied.append(
            {
                "section": section,
                "id": repair_id,
                "sites": 1,
                "owners": [owner],
                "kind": repair.get("kind"),
                "confidence": repair.get("confidence"),
            }
        )
    return current, applied, owners_used


def apply_conditional_order(
    core: Any,
    source: str,
    order: tuple[str, ...],
    manifests: dict[str, dict[str, Any]],
) -> tuple[str, list[dict[str, Any]], dict[str, set[str]]]:
    current = source
    applied: list[dict[str, Any]] = []
    owners: dict[str, set[str]] = {}
    for section in order:
        current, section_applied, section_owners = apply_conditional_section(
            core, current, section, manifests[section]
        )
        applied.extend(section_applied)
        owners[section] = section_owners
    return current, applied, owners


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--core-builder", type=Path, required=True)
    parser.add_argument("--main-candidate", type=Path, required=True)
    parser.add_argument("--main-audit", type=Path, required=True)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()

    core = load_core(args.core_builder)
    index = read_json(args.index)
    if index.get("schema") != INDEX_SCHEMA:
        raise SystemExit("unexpected conditional-probe index schema")
    if index.get("m13_source_move_included") is not False:
        raise SystemExit("the M13 source move must remain excluded")

    main_bytes = args.main_candidate.read_bytes()
    main_text = main_bytes.decode("utf-8")
    main_audit = read_json(args.main_audit)
    main_sha = sha256(main_bytes)
    if main_audit.get("schema") != core.AUDIT_SCHEMA:
        raise SystemExit("unexpected main audit schema")
    if main_audit.get("status") != "STATIC_PASS_DIRECT_LEAN_UNVERIFIED":
        raise SystemExit("main candidate static audit did not pass")
    if main_audit.get("candidate_sha256") != main_sha:
        raise SystemExit("main candidate/audit SHA identity mismatch")
    if index.get("main_candidate_sha256") != main_sha:
        raise SystemExit("conditional index main candidate SHA lock mismatch")
    if main_audit.get("direct_lean_verified") is not False:
        raise SystemExit("main candidate unexpectedly claims direct Lean verification")

    entries = index.get("manifests")
    if not isinstance(entries, list):
        raise SystemExit("conditional manifests must be a list")
    sections = [str(entry.get("section")) for entry in entries if isinstance(entry, dict)]
    if sorted(sections) != sorted(ALLOWED_SECTIONS) or len(set(sections)) != 2:
        raise SystemExit(f"conditional sections must be exactly {ALLOWED_SECTIONS}: {sections}")

    manifests: dict[str, dict[str, Any]] = {}
    manifest_meta: list[dict[str, Any]] = []
    repair_ids: set[str] = set()
    main_ids = {str(item["id"]) for item in main_audit.get("applied", [])}
    for entry in entries:
        if not isinstance(entry, dict):
            raise SystemExit("conditional manifest entry is not an object")
        section = str(entry["section"])
        path = Path(str(entry["path"]))
        data = path.read_bytes()
        actual_sha = sha256(data)
        if actual_sha != entry.get("sha256"):
            raise SystemExit(f"{section}: conditional manifest SHA mismatch")
        manifest = json.loads(data.decode("utf-8"))
        if manifest.get("schema") != "fa-v40-conditional-fragment-repairs-v1":
            raise SystemExit(f"{section}: unexpected conditional manifest schema")
        if manifest.get("direct_lean_verified") is True:
            raise SystemExit(f"{section}: unexpectedly claims direct Lean verification")
        if not core.nested_contains(manifest, core.AUTHORITY_SHA256):
            raise SystemExit(f"{section}: missing v40 authority source lock")
        if not core.nested_contains(manifest, core.DIAGNOSTICS_SHA256):
            raise SystemExit(f"{section}: missing v40 diagnostic inventory lock")
        for repair in manifest.get("repairs", []):
            repair_id = str(repair.get("id", ""))
            if not repair_id or repair_id in repair_ids or repair_id in main_ids:
                raise SystemExit(f"conditional repair id missing/colliding: {repair_id}")
            repair_ids.add(repair_id)
        manifests[section] = manifest
        manifest_meta.append(
            {
                "section": section,
                "path": str(path),
                "sha256": actual_sha,
                "repair_entries": len(manifest.get("repairs", [])),
            }
        )

    main_declarations = [match.group(1) for match in core.DECL_RE.finditer(main_text)]
    main_headers = core.raw_declaration_headers(main_text)
    main_comments, main_attributes = core.comments_and_attributes(main_text)
    main_trust = core.trust_counts(main_text)
    if len(main_declarations) != core.EXPECTED_DECLARATIONS:
        raise SystemExit("main declaration count mismatch")
    if any(main_trust.values()):
        raise SystemExit(f"main candidate executable trust counts are nonzero: {main_trust}")

    main_owners = {
        owner
        for item in main_audit.get("applied", [])
        for owner in item.get("owners", [])
        if owner is not None
    }
    permutation_hashes: dict[str, str] = {}
    canonical_text: str | None = None
    canonical_applied: list[dict[str, Any]] = []
    conditional_owners: dict[str, set[str]] = {}
    for order in itertools.permutations(ALLOWED_SECTIONS):
        candidate, applied, owners = apply_conditional_order(
            core, main_text, order, manifests
        )
        key = "->".join(order)
        permutation_hashes[key] = sha256(candidate.encode("utf-8"))
        if canonical_text is None:
            canonical_text = candidate
            canonical_applied = applied
            conditional_owners = owners
        elif candidate != canonical_text:
            raise SystemExit(f"conditional section order is not independent: {key}")
    assert canonical_text is not None

    conditional_owner_union = set().union(*conditional_owners.values())
    overlap = sorted(main_owners & conditional_owner_union)
    if overlap:
        raise SystemExit(f"main/conditional owner collision: {overlap}")
    if conditional_owners["M05_M06"] & conditional_owners["LR_BODY"]:
        raise SystemExit("conditional sections share declaration owners")

    after_declarations = [match.group(1) for match in core.DECL_RE.finditer(canonical_text)]
    after_headers = core.raw_declaration_headers(canonical_text)
    after_comments, after_attributes = core.comments_and_attributes(canonical_text)
    after_trust = core.trust_counts(canonical_text)
    if after_declarations != main_declarations:
        raise SystemExit("conditional probe changed declaration sequence")
    if after_headers != main_headers:
        raise SystemExit("conditional probe changed declaration headers")
    if after_comments != main_comments:
        raise SystemExit("conditional probe changed comments")
    if after_attributes != main_attributes:
        raise SystemExit("conditional probe changed attributes")
    if after_trust != main_trust or any(after_trust.values()):
        raise SystemExit(f"conditional probe changed executable trust counts: {after_trust}")

    output_bytes = canonical_text.encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(output_bytes)
    audit = {
        "schema": AUDIT_SCHEMA,
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "main_candidate_sha256": main_sha,
        "main_audit_sha256": sha256(args.main_audit.read_bytes()),
        "index_sha256": sha256(args.index.read_bytes()),
        "manifests": manifest_meta,
        "candidate_sha256": sha256(output_bytes),
        "candidate_bytes": len(output_bytes),
        "candidate_lines": len(canonical_text.splitlines()),
        "declaration_count": len(main_declarations),
        "declaration_sequence_identical": True,
        "all_v41_main_headers_byte_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "trust_counts_before": main_trust,
        "trust_counts_after": after_trust,
        "repair_entry_count": len(canonical_applied),
        "replacement_site_count": sum(item["sites"] for item in canonical_applied),
        "main_conditional_owner_collisions": [],
        "conditional_permutation_hashes": permutation_hashes,
        "conditional_order_independent": len(set(permutation_hashes.values())) == 1,
        "m13_source_move_included": False,
        "direct_lean_verified": False,
        "full_fa_clean_claimed": False,
        "applied": canonical_applied,
    }
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.audit.write_text(
        json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps(audit, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
