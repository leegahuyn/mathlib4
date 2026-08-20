#!/usr/bin/env python3
"""Merge the four v40 residual repair sections into one v41 candidate.

This is a static, fail-closed builder.  It never invokes Lean, Lake, git, or
GitHub.  The resulting source is only a candidate for the next authoritative
direct GitHub compile.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path
from typing import Any, Iterable


INDEX_SCHEMA = "fa-v41-selected-manifests-v1"
AUDIT_SCHEMA = "fa-v41-cumulative-static-audit-v1"
AUTHORITY_SHA256 = "c88cd9832ea095ab22b0f1dd9307c8f43587d85b10688d47c4a534529cebca5c"
DIAGNOSTICS_SHA256 = "fe09d7ad50bfebb6fbc13e03e2bb58cfde0f7116e4ed624f97a7204c2de38efc"
EXPECTED_SECTIONS = ("G1", "G2", "G3", "G4")
EXPECTED_DECLARATIONS = 4416

DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
TRUST_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"{path}: top-level JSON value must be an object")
    return value


def declaration_regions(text: str) -> list[dict[str, Any]]:
    matches = list(DECL_RE.finditer(text))
    return [
        {
            "index": index,
            "name": match.group(1),
            "start": match.start(),
            "end": matches[index + 1].start() if index + 1 < len(matches) else len(text),
        }
        for index, match in enumerate(matches)
    ]


def owner_at(text: str, offset: int) -> tuple[int, str] | None:
    for region in declaration_regions(text):
        if region["start"] <= offset < region["end"]:
            return int(region["index"]), str(region["name"])
    return None


def raw_declaration_headers(text: str) -> list[tuple[str, str]]:
    matches = list(DECL_RE.finditer(text))
    headers: list[tuple[str, str]] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        block = text[match.start() : end]
        cuts = [
            position
            for position in (
                block.find(":= by"),
                block.find(":="),
                block.find(" where\n"),
            )
            if position >= 0
        ]
        header = block if not cuts else block[: min(cuts)]
        headers.append((match.group(1), header))
    return headers


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
                if index >= len(text):
                    raise SystemExit("unterminated block comment")
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
            if end < 0:
                raise SystemExit("unterminated declaration attribute")
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
    if depth or in_string:
        raise SystemExit("unterminated comment or string")
    return "".join(chars)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        token: len(
            re.findall(
                r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])",
                code,
            )
        )
        for token in TRUST_TOKENS
    }


def nested_contains(value: Any, needle: str) -> bool:
    if isinstance(value, dict):
        return any(nested_contains(item, needle) for item in value.values())
    if isinstance(value, list):
        return any(nested_contains(item, needle) for item in value)
    return value == needle


def offsets_of(text: str, fragment: str) -> list[int]:
    offsets: list[int] = []
    cursor = 0
    while True:
        offset = text.find(fragment, cursor)
        if offset < 0:
            return offsets
        offsets.append(offset)
        cursor = offset + len(fragment)


def wanted_owners(repair: dict[str, Any], expected: int) -> list[str | None]:
    owners = repair.get("owners")
    if isinstance(owners, list) and owners:
        if len(owners) != expected:
            raise SystemExit(
                f"{repair.get('id')}: owners length {len(owners)} != expected {expected}"
            )
        return [str(owner) if owner is not None else None for owner in owners]
    owner = repair.get("owner")
    if owner is None:
        raise SystemExit(f"{repair.get('id')}: missing owner/owners")
    return [str(owner)] * expected


def apply_section(
    source: str,
    section: str,
    manifest: dict[str, Any],
) -> tuple[str, list[dict[str, Any]], set[str]]:
    repairs = manifest.get("repairs")
    if not isinstance(repairs, list) or not repairs:
        raise SystemExit(f"{section}: manifest has no repairs")
    current = source
    applied: list[dict[str, Any]] = []
    owners_used: set[str] = set()
    local_ids: set[str] = set()
    for repair in repairs:
        if not isinstance(repair, dict):
            raise SystemExit(f"{section}: repair entry is not an object")
        repair_id = str(repair.get("id", ""))
        if not repair_id or repair_id in local_ids:
            raise SystemExit(f"{section}: missing/duplicate repair id {repair_id!r}")
        local_ids.add(repair_id)
        old = repair.get("old")
        new = repair.get("new")
        if not isinstance(old, str) or not isinstance(new, str) or not old or old == new:
            raise SystemExit(f"{section}/{repair_id}: invalid old/new fragment")
        expected = int(repair.get("expected_count", 1))
        offsets = offsets_of(current, old)
        if len(offsets) != expected:
            raise SystemExit(
                f"{section}/{repair_id}: old count {len(offsets)} != expected {expected}"
            )
        expected_names = wanted_owners(repair, expected)
        actual_owners = [owner_at(current, offset) for offset in offsets]
        actual_names = [owner[1] if owner else None for owner in actual_owners]
        if actual_names != expected_names and repair.get("kind") == "environment":
            # Environment insertions can intentionally begin between declarations
            # and include the following declaration header as their right anchor.
            # In that case the byte offset belongs to the preceding parser region,
            # while the manifest owner is correctly the declaration being prepared.
            anchored_names = [match.group(1) for match in DECL_RE.finditer(old)]
            if expected == 1 and expected_names[0] in anchored_names:
                actual_names = expected_names
        if actual_names != expected_names:
            raise SystemExit(
                f"{section}/{repair_id}: owners {actual_names} != {expected_names}"
            )
        owners_used.update(name for name in actual_names if name is not None)
        current = current.replace(old, new)
        applied.append(
            {
                "section": section,
                "id": repair_id,
                "sites": expected,
                "owners": actual_names,
                "kind": repair.get("kind"),
                "confidence": repair.get("confidence"),
            }
        )
    return current, applied, owners_used


def apply_order(
    source: str,
    order: Iterable[str],
    manifests: dict[str, dict[str, Any]],
) -> tuple[str, list[dict[str, Any]], dict[str, set[str]]]:
    current = source
    applied: list[dict[str, Any]] = []
    owners: dict[str, set[str]] = {}
    for section in order:
        current, section_applied, section_owners = apply_section(
            current, section, manifests[section]
        )
        applied.extend(section_applied)
        owners[section] = section_owners
    return current, applied, owners


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()

    index = read_json(args.index)
    if index.get("schema") != INDEX_SCHEMA:
        raise SystemExit("unexpected selected-manifest index schema")
    authority = index.get("authority")
    if not isinstance(authority, dict):
        raise SystemExit("index authority is missing")
    source_path = Path(str(authority.get("path", "")))
    diagnostics_path = Path(str(authority.get("diagnostics_path", "")))
    source_bytes = source_path.read_bytes()
    diagnostics_bytes = diagnostics_path.read_bytes()
    if sha256(source_bytes) != AUTHORITY_SHA256:
        raise SystemExit("authority source SHA mismatch")
    if sha256(diagnostics_bytes) != DIAGNOSTICS_SHA256:
        raise SystemExit("authority diagnostics SHA mismatch")
    if authority.get("sha256") != AUTHORITY_SHA256:
        raise SystemExit("index source SHA lock mismatch")
    if authority.get("diagnostics_sha256") != DIAGNOSTICS_SHA256:
        raise SystemExit("index diagnostics SHA lock mismatch")

    selected = index.get("manifests")
    if not isinstance(selected, list):
        raise SystemExit("index manifests must be a list")
    sections = [str(item.get("section")) for item in selected if isinstance(item, dict)]
    if sorted(sections) != sorted(EXPECTED_SECTIONS) or len(set(sections)) != 4:
        raise SystemExit(f"selected sections must be exactly {EXPECTED_SECTIONS}: {sections}")

    manifests: dict[str, dict[str, Any]] = {}
    manifest_meta: list[dict[str, Any]] = []
    all_ids: dict[str, str] = {}
    for item in selected:
        if not isinstance(item, dict):
            raise SystemExit("manifest index entry is not an object")
        section = str(item["section"])
        path = Path(str(item["path"]))
        data = path.read_bytes()
        expected_sha = str(item.get("sha256", ""))
        actual_sha = sha256(data)
        if actual_sha != expected_sha:
            raise SystemExit(f"{section}: manifest SHA mismatch")
        manifest = json.loads(data.decode("utf-8"))
        if manifest.get("schema") != item.get("schema"):
            raise SystemExit(f"{section}: manifest schema mismatch")
        if not nested_contains(manifest, AUTHORITY_SHA256):
            raise SystemExit(f"{section}: manifest does not lock the v40 authority source")
        if manifest.get("direct_lean_verified") is True:
            # A direct-pass manifest would be acceptable in another workflow, but this
            # package intentionally records all four sections as unverified inputs.
            raise SystemExit(f"{section}: unexpectedly claims direct Lean verification")
        for repair in manifest.get("repairs", []):
            repair_id = str(repair.get("id", ""))
            if repair_id in all_ids:
                raise SystemExit(
                    f"repair id collision: {repair_id} in {all_ids[repair_id]} and {section}"
                )
            all_ids[repair_id] = section
        manifests[section] = manifest
        manifest_meta.append(
            {
                "section": section,
                "path": str(path),
                "schema": manifest.get("schema"),
                "sha256": actual_sha,
                "repair_entries": len(manifest.get("repairs", [])),
                "direct_lean_verified": bool(manifest.get("direct_lean_verified", False)),
            }
        )

    source = source_bytes.decode("utf-8")
    before_declarations = [match.group(1) for match in DECL_RE.finditer(source)]
    before_headers = raw_declaration_headers(source)
    before_comments, before_attributes = comments_and_attributes(source)
    before_trust = trust_counts(source)
    if len(before_declarations) != EXPECTED_DECLARATIONS:
        raise SystemExit(
            f"authority declaration count {len(before_declarations)} != {EXPECTED_DECLARATIONS}"
        )
    if any(before_trust.values()):
        raise SystemExit(f"authority executable trust counts are nonzero: {before_trust}")

    permutation_hashes: dict[str, str] = {}
    canonical_text: str | None = None
    canonical_applied: list[dict[str, Any]] = []
    canonical_owners: dict[str, set[str]] = {}
    for order_tuple in itertools.permutations(EXPECTED_SECTIONS):
        candidate, applied, owners = apply_order(source, order_tuple, manifests)
        candidate_hash = sha256(candidate.encode("utf-8"))
        order_key = "->".join(order_tuple)
        permutation_hashes[order_key] = candidate_hash
        if canonical_text is None:
            canonical_text = candidate
            canonical_applied = applied
            canonical_owners = owners
        elif candidate != canonical_text:
            raise SystemExit(f"section order is not independent: {order_key}")
    assert canonical_text is not None

    owner_to_sections: dict[str, list[str]] = {}
    for section, owners in canonical_owners.items():
        for owner in owners:
            owner_to_sections.setdefault(owner, []).append(section)
    owner_collisions = {
        owner: sections_for_owner
        for owner, sections_for_owner in owner_to_sections.items()
        if len(set(sections_for_owner)) > 1
    }
    if owner_collisions:
        raise SystemExit(f"cross-section owner collisions: {owner_collisions}")

    after_declarations = [match.group(1) for match in DECL_RE.finditer(canonical_text)]
    after_headers = raw_declaration_headers(canonical_text)
    after_comments, after_attributes = comments_and_attributes(canonical_text)
    after_trust = trust_counts(canonical_text)
    if after_declarations != before_declarations:
        raise SystemExit("declaration sequence changed")
    if after_headers != before_headers:
        changed = [
            before_name
            for (before_name, before_header), (after_name, after_header) in zip(
                before_headers, after_headers, strict=True
            )
            if before_name != after_name or before_header != after_header
        ]
        raise SystemExit(f"new declaration-header changes are forbidden: {changed}")
    if after_comments != before_comments:
        raise SystemExit("comments changed")
    if after_attributes != before_attributes:
        raise SystemExit("attributes changed")
    if after_trust != before_trust or any(after_trust.values()):
        raise SystemExit(f"executable trust counts changed: {before_trust} -> {after_trust}")

    output_bytes = canonical_text.encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(output_bytes)
    audit = {
        "schema": AUDIT_SCHEMA,
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "authority_sha256": AUTHORITY_SHA256,
        "authority_bytes": len(source_bytes),
        "authority_lines": len(source.splitlines()),
        "diagnostics_sha256": DIAGNOSTICS_SHA256,
        "index_sha256": sha256(args.index.read_bytes()),
        "manifests": manifest_meta,
        "candidate_sha256": sha256(output_bytes),
        "candidate_bytes": len(output_bytes),
        "candidate_lines": len(canonical_text.splitlines()),
        "declaration_count": len(before_declarations),
        "declaration_sequence_identical": True,
        "all_v40_headers_byte_identical": True,
        "new_header_change_count": 0,
        "comments_identical": True,
        "attributes_identical": True,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "repair_entry_count": len(canonical_applied),
        "replacement_site_count": sum(item["sites"] for item in canonical_applied),
        "cross_section_owner_collisions": {},
        "section_permutation_count": len(permutation_hashes),
        "section_permutation_hashes": permutation_hashes,
        "section_order_independent": len(set(permutation_hashes.values())) == 1,
        "excluded_conditional_chains": index.get("excluded_conditional_chains", []),
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
