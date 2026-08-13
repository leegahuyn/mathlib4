#!/usr/bin/env python3
"""Compose exact declaration-local FA repair manifests and audit invariants.

This is a static source validator only.  It never invokes Lean, Lake, git, or
GitHub.  Replacement is owner-local, so a fragment may legitimately occur in
another symmetric declaration without allowing the wrong declaration to be
edited.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


SCHEMA = "fa-v42-declaration-local-repairs-v1"
Q1_SCHEMA = "fa-v42-q1-root-repair-manifest-v1"
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


def regions(text: str) -> list[dict[str, Any]]:
    matches = list(DECL_RE.finditer(text))
    return [
        {
            "index": i,
            "name": match.group(1),
            "start": match.start(),
            "end": matches[i + 1].start() if i + 1 < len(matches) else len(text),
        }
        for i, match in enumerate(matches)
    ]


def raw_headers(text: str) -> list[tuple[str, str]]:
    result: list[tuple[str, str]] = []
    for region in regions(text):
        block = text[region["start"] : region["end"]]
        cuts = [
            point
            for point in (block.find(":= by"), block.find(":="), block.find(" where\n"))
            if point >= 0
        ]
        header = block if not cuts else block[: min(cuts)]
        result.append((region["name"], header))
    return result


def comments_and_attributes(text: str) -> tuple[list[str], list[str]]:
    comments: list[str] = []
    attributes: list[str] = []
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            start = i
            depth = 1
            i += 2
            while depth:
                if i >= len(text):
                    raise SystemExit("unterminated block comment")
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            comments.append(text[start:i])
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            comments.append(text[i:end])
            i = end
            continue
        if text.startswith("@[", i):
            end = text.find("]", i + 2)
            if end < 0:
                raise SystemExit("unterminated attribute")
            attributes.append(text[i : end + 1])
            i = end + 1
            continue
        i += 1
    return comments, attributes


def strip_noncode(text: str) -> str:
    chars = list(text)
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(chars):
        if depth:
            if text.startswith("/-", i):
                chars[i] = chars[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                chars[i] = chars[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue
        if in_string:
            original = chars[i]
            if original != "\n":
                chars[i] = " "
            if escaped:
                escaped = False
            elif original == "\\":
                escaped = True
            elif original == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            chars[i] = chars[i + 1] = " "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        if chars[i] == '"':
            chars[i] = " "
            in_string = True
        i += 1
    if depth or in_string:
        raise SystemExit("unterminated non-code region")
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


def replace_in_owner(text: str, repair: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    declaration_regions = regions(text)
    declaration_index = int(repair["declaration_index"])
    if not 0 <= declaration_index < len(declaration_regions):
        raise SystemExit(f"{repair['id']}: declaration index out of range")
    owner_region = declaration_regions[declaration_index]
    if owner_region["name"] != repair["owner"]:
        raise SystemExit(
            f"{repair['id']}: owner mismatch at {declaration_index}: "
            f"{owner_region['name']} != {repair['owner']}"
        )
    old = repair["old"]
    new = repair["new"]
    if not old or old == new:
        raise SystemExit(f"{repair['id']}: empty or no-op fragment")
    block = text[owner_region["start"] : owner_region["end"]]
    expected = int(repair.get("expected_count_in_owner", 1))
    owner_count = block.count(old)
    if owner_count != expected:
        raise SystemExit(
            f"{repair['id']}: owner-local old count {owner_count} != {expected}"
        )
    global_count = text.count(old)
    replaced_block = block.replace(old, new)
    if replaced_block.count(old) != block.count(old) - expected + expected * new.count(old):
        raise SystemExit(f"{repair['id']}: replacement count postcondition failed")
    result = (
        text[: owner_region["start"]]
        + replaced_block
        + text[owner_region["end"] :]
    )
    return result, {
        "id": repair["id"],
        "owner": repair["owner"],
        "declaration_index": declaration_index,
        "owner_old_count": owner_count,
        "global_old_count": global_count,
        "kind": repair.get("kind"),
        "confidence": repair.get("confidence"),
    }


def normalize_manifest(manifest: dict[str, Any]) -> dict[str, Any]:
    """Normalize worker-specific manifests to the local composer contract."""
    schema = manifest.get("schema")
    if schema == SCHEMA:
        return manifest
    if schema != Q1_SCHEMA:
        raise SystemExit(f"unexpected schema: {schema}")

    authority = manifest["authority"]
    candidate = authority["candidate"]
    repairs: list[dict[str, Any]] = []
    for original in (
        list(manifest["promoted_repairs"]) + list(manifest.get("staged_repairs", []))
    ):
        repair = dict(original)
        repair["expected_count_in_owner"] = int(
            repair.pop("expected_owner_count", 1)
        )
        repairs.append(repair)
    return {
        "schema": SCHEMA,
        "status": manifest.get("status"),
        "authority": {
            "run_id": authority["run_id"],
            "head_sha": authority["head_sha"],
            "artifact_id": authority["artifact_id"],
            "artifact_digest": authority["artifact_digest"],
            "source_path": candidate["path"],
            "source_sha256": candidate["sha256"],
            "source_bytes": candidate["bytes"],
            "source_lines": candidate["lines"],
            "declaration_count": 4416,
        },
        "repairs": repairs,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", action="append", type=Path, required=True)
    parser.add_argument("--repair-id", action="append", default=[])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()

    manifest_records: list[tuple[Path, bytes, dict[str, Any]]] = []
    for path in args.manifest:
        payload = path.read_bytes()
        manifest = normalize_manifest(json.loads(payload))
        manifest_records.append((path, payload, manifest))

    first_authority = manifest_records[0][2]["authority"]
    authority_keys = (
        "run_id",
        "head_sha",
        "artifact_id",
        "artifact_digest",
        "source_path",
        "source_sha256",
        "source_bytes",
        "source_lines",
        "declaration_count",
    )
    for path, _payload, manifest in manifest_records[1:]:
        authority = manifest["authority"]
        mismatches = [
            key for key in authority_keys if authority.get(key) != first_authority.get(key)
        ]
        if mismatches:
            raise SystemExit(f"{path}: authority mismatch: {mismatches}")

    source_path = Path(first_authority["source_path"])
    source_bytes = source_path.read_bytes()
    if sha256(source_bytes) != first_authority["source_sha256"]:
        raise SystemExit("authority source SHA mismatch")
    if len(source_bytes) != int(first_authority["source_bytes"]):
        raise SystemExit("authority source byte count mismatch")
    source = source_bytes.decode("utf-8")
    if len(source.splitlines()) != int(first_authority["source_lines"]):
        raise SystemExit("authority source line count mismatch")

    before_regions = regions(source)
    if len(before_regions) != int(first_authority["declaration_count"]):
        raise SystemExit(f"authority declaration count mismatch: {len(before_regions)}")
    before_names = [region["name"] for region in before_regions]
    before_headers = raw_headers(source)
    before_comments, before_attributes = comments_and_attributes(source)
    before_trust = trust_counts(source)
    if any(before_trust.values()):
        raise SystemExit(f"authority executable trust counts nonzero: {before_trust}")

    requested_ids = set(args.repair_id)
    all_repairs: list[dict[str, Any]] = []
    for _path, _payload, manifest in manifest_records:
        all_repairs.extend(manifest["repairs"])
    all_ids = [repair["id"] for repair in all_repairs]
    if len(all_ids) != len(set(all_ids)):
        raise SystemExit("duplicate repair IDs across manifests")
    if requested_ids:
        missing = requested_ids - set(all_ids)
        if missing:
            raise SystemExit(f"unknown requested repair IDs: {sorted(missing)}")
        selected = [repair for repair in all_repairs if repair["id"] in requested_ids]
    else:
        selected = all_repairs

    current = source
    applied: list[dict[str, Any]] = []
    for repair in selected:
        current, record = replace_in_owner(current, repair)
        applied.append(record)

    after_regions = regions(current)
    after_names = [region["name"] for region in after_regions]
    after_headers = raw_headers(current)
    after_comments, after_attributes = comments_and_attributes(current)
    after_trust = trust_counts(current)
    if after_names != before_names:
        raise SystemExit("declaration sequence changed")
    if after_headers != before_headers:
        changed = [
            before[0]
            for before, after in zip(before_headers, after_headers, strict=True)
            if before != after
        ]
        raise SystemExit(f"declaration headers changed: {changed}")
    if after_comments != before_comments:
        raise SystemExit("comments changed")
    if after_attributes != before_attributes:
        raise SystemExit("attributes changed")
    if after_trust != before_trust or any(after_trust.values()):
        raise SystemExit(f"executable trust changed: {before_trust} -> {after_trust}")

    output_bytes = current.encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(output_bytes)
    audit = {
        "schema": "fa-v42-local-repair-static-audit-v1",
        "status": "STATIC_PASS_DIRECT_LEAN_UNVERIFIED",
        "authority": first_authority,
        "manifests": [
            {
                "path": path.as_posix(),
                "sha256": sha256(payload),
                "bytes": len(payload),
                "repair_entries": len(manifest["repairs"]),
            }
            for path, payload, manifest in manifest_records
        ],
        "selected_repair_ids": [repair["id"] for repair in selected],
        "selected_repair_count": len(selected),
        "selected_owner_count": len({repair["owner"] for repair in selected}),
        "applied": applied,
        "candidate_sha256": sha256(output_bytes),
        "candidate_bytes": len(output_bytes),
        "candidate_lines": len(current.splitlines()),
        "declaration_count": len(after_regions),
        "declaration_sequence_identical": True,
        "all_declaration_headers_byte_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "direct_lean_verified": False,
        "lean_lake_git_github_invoked": False,
    }
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.audit.write_text(
        json.dumps(audit, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(audit, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
