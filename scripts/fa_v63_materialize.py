#!/usr/bin/env python3
"""Exact multi-manifest v63 body-only materializer.

Every candidate is independently recomposed from the same v62 winner bytes.
There is no parent-candidate input, artifact-local manifest, or runtime fallback.
The CLI writes nothing for missing/PENDING inputs (exit 2), and it performs all
contract, replacement, candidate-lock, and invariant checks in memory before it
creates any output (contract violation exit 86).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

from fa_v63_contract import (
    ContractError,
    DECLARATION_COUNT,
    PendingInput,
    TRUST_TOKENS,
    canonical_authority_projection,
    load_ready_contract,
    require,
    sha256,
)


DECLARATION_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def comment_spans(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    index = 0
    in_string = False
    escaped = False
    while index < len(text):
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            spans.append((index, end))
            index = end
            continue
        if text.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            require(depth == 0, "unterminated block comment")
            spans.append((start, index))
            continue
        index += 1
    return spans


def comments_and_attributes(text: str) -> tuple[list[str], list[str]]:
    spans = comment_spans(text)
    found_comments = [text[start:end] for start, end in spans]
    attributes: list[str] = []
    span_index = 0
    index = 0
    in_string = False
    escaped = False
    while index < len(text):
        if span_index < len(spans) and index == spans[span_index][0]:
            index = spans[span_index][1]
            span_index += 1
            continue
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if text.startswith("@[", index):
            end = text.find("]", index + 2)
            require(end >= 0, "unterminated attribute")
            attributes.append(text[index:end + 1])
            index = end + 1
            continue
        index += 1
    return found_comments, attributes


def strip_comments_and_strings(text: str) -> str:
    chars = list(text)
    for start, end in comment_spans(text):
        chars[start:end] = " " * (end - start)
    value = "".join(chars)
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', value)


def trust_counts(text: str) -> dict[str, int]:
    executable = strip_comments_and_strings(text)
    return {
        token: len(re.findall(
            r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])",
            executable,
        ))
        for token in TRUST_TOKENS
    }


def heartbeat_counts(text: str) -> dict[str, int]:
    executable = strip_comments_and_strings(text)
    return {
        "token_count": len(re.findall(r"\bmaxHeartbeats\b", executable)),
        "set_option_count": len(re.findall(
            r"\bset_option\s+maxHeartbeats\b", executable)),
    }


def declaration_regions(text: str) -> list[dict[str, Any]]:
    matches = list(DECLARATION_RE.finditer(text))
    return [{
        "index": index,
        "name": match.group(1),
        "start": match.start(),
        "end": matches[index + 1].start() if index + 1 < len(matches) else len(text),
    } for index, match in enumerate(matches)]


def raw_header(region: str) -> str:
    cuts = [point for point in (
        region.find(":= by"), region.find(":="), region.find(" where\n"),
    ) if point >= 0]
    return region if not cuts else region[:min(cuts)]


def declaration_headers(text: str) -> list[tuple[str, str]]:
    return [(region["name"], raw_header(text[region["start"]:region["end"]]))
            for region in declaration_regions(text)]


def locate_owner(text: str, owner: dict[str, Any]) -> tuple[int, int, str, str]:
    regions = declaration_regions(text)
    index = owner["declaration_index"]
    require(0 <= index < len(regions), "owner declaration index out of range")
    observed = regions[index]
    require(observed["name"] == owner["declaration_name"],
            "owner declaration index/name mismatch")
    region = text[observed["start"]:observed["end"]]
    header = raw_header(region)
    require(header == owner["expected_header"], "owner raw header mismatch")
    require(sha256(header.encode("utf-8")) == owner["expected_header_sha256"],
            "owner raw header hash mismatch")
    return observed["start"], observed["end"], region, header


def overlaps(spans: list[tuple[int, int]], start: int, end: int) -> bool:
    return any(start < span_end and end > span_start for span_start, span_end in spans)


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)
            + "\n").encode("utf-8")


def compose(contract: dict[str, Any], source_payload: bytes,
            variant_name: str) -> tuple[bytes, dict[str, Any], dict[str, Any]]:
    selection = contract["selection"]
    variants = [row for row in selection["variants"] if row["name"] == variant_name]
    require(len(variants) == 1, "variant is not selected exactly once")
    variant = variants[0]
    source_lock = contract["authority"]["source"]
    require(sha256(source_payload) == source_lock["sha256"],
            "authority source SHA-256 mismatch")
    require(len(source_payload) == source_lock["bytes"],
            "authority source byte mismatch")
    try:
        source = source_payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ContractError("authority source is not UTF-8") from exc
    require(len(source.splitlines()) == source_lock["lines"],
            "authority source line mismatch")
    before_headers = declaration_headers(source)
    require(len(before_headers) == source_lock["declaration_count"] == DECLARATION_COUNT,
            "authority parsed declaration count mismatch")
    before_comments, before_attributes = comments_and_attributes(source)
    before_heartbeats = heartbeat_counts(source)
    require(before_heartbeats == {"token_count": 8, "set_option_count": 8},
            "authority heartbeat inventory is not exact 8/8")
    before_trust = trust_counts(source)
    require(before_trust == {token: 0 for token in TRUST_TOKENS},
            "authority executable trust-six is nonzero")

    selected_ids = variant["selected_repair_ids"]
    selected_repairs = [contract["all_repairs"][repair_id] for repair_id in selected_ids]
    require([row["sequence"] for row in selected_repairs] ==
            sorted(row["sequence"] for row in selected_repairs),
            "selected repairs are not in exact sequence order")
    current = source
    applied: list[dict[str, Any]] = []
    authority_owner_hashes: dict[tuple[int, str], str] = {}
    for repair in selected_repairs:
        repair_id = repair["id"]
        owner = repair["owner"]
        owner_key = (owner["declaration_index"], owner["declaration_name"])
        if owner_key not in authority_owner_hashes:
            _, _, authority_region, _ = locate_owner(source, owner)
            authority_owner_hashes[owner_key] = sha256(authority_region.encode("utf-8"))
        require(authority_owner_hashes[owner_key] ==
                owner["expected_authority_region_sha256"],
                f"authority owner-region SHA mismatch: {repair_id}")
        operation_audits: list[dict[str, Any]] = []
        for operation in repair["operations"]:
            operation_id = operation["id"]
            start, end, region, observed_header = locate_owner(current, owner)
            old = operation["old"]
            new = operation["new"]
            counts = operation["counts"]
            require(region.count(old) == counts["old_owner_before"],
                    f"OLD owner count mismatch: {repair_id}/{operation_id}")
            require(current.count(old) == counts["old_global_before"],
                    f"OLD global count mismatch: {repair_id}/{operation_id}")
            require(region.count(new) == counts["new_owner_before"],
                    f"NEW-before owner count mismatch: {repair_id}/{operation_id}")
            require(current.count(new) == counts["new_global_before"],
                    f"NEW-before global count mismatch: {repair_id}/{operation_id}")
            require(sha256(old.encode("utf-8")) == operation["old_sha256"]
                    and len(old.encode("utf-8")) == operation["old_bytes"],
                    f"OLD fragment lock mismatch: {repair_id}/{operation_id}")
            require(sha256(new.encode("utf-8")) == operation["new_sha256"]
                    and len(new.encode("utf-8")) == operation["new_bytes"],
                    f"NEW fragment lock mismatch: {repair_id}/{operation_id}")
            offset = region.find(old)
            require(offset >= 0, f"OLD fragment absent: {repair_id}/{operation_id}")
            body_marker = region.find(":=")
            require(body_marker >= 0 and offset > body_marker,
                    f"operation is not strictly after statement: {repair_id}/{operation_id}")
            absolute_start = start + offset
            require(not overlaps(comment_spans(current), absolute_start,
                                 absolute_start + len(old)),
                    f"OLD fragment overlaps comment: {repair_id}/{operation_id}")
            outside_before = (current[:start] + current[end:]).encode("utf-8")
            region_hb_before = heartbeat_counts(region)
            changed_region = region.replace(old, new, counts["old_owner_before"])
            require(changed_region.count(old) == counts["old_owner_after"],
                    f"OLD-after owner count mismatch: {repair_id}/{operation_id}")
            require(changed_region.count(new) == counts["new_owner_after"],
                    f"NEW-after owner count mismatch: {repair_id}/{operation_id}")
            require(raw_header(changed_region) == observed_header,
                    f"owner header changed: {repair_id}/{operation_id}")
            current = current[:start] + changed_region + current[end:]
            changed_end = start + len(changed_region)
            outside_after = (current[:start] + current[changed_end:]).encode("utf-8")
            require(outside_after == outside_before,
                    f"outside-owner bytes changed: {repair_id}/{operation_id}")
            region_hb_after = heartbeat_counts(changed_region)
            require(region_hb_after == region_hb_before,
                    f"owner heartbeat changed: {repair_id}/{operation_id}")
            require(current.count(old) == counts["old_global_after"],
                    f"OLD-after global count mismatch: {repair_id}/{operation_id}")
            require(current.count(new) == counts["new_global_after"],
                    f"NEW-after global count mismatch: {repair_id}/{operation_id}")
            operation_audits.append({
                "id": operation_id,
                "old_sha256": operation["old_sha256"],
                "new_sha256": operation["new_sha256"],
                "old_bytes": operation["old_bytes"],
                "new_bytes": operation["new_bytes"],
                "counts": counts,
                "owner_region_maxHeartbeats_before": region_hb_before,
                "owner_region_maxHeartbeats_after": region_hb_after,
                "outside_owner_sha256_before": sha256(outside_before),
                "outside_owner_sha256_after": sha256(outside_after),
                "outside_owner_byte_identical": True,
            })
        applied.append({
            "id": repair_id,
            "sequence": repair["sequence"],
            "stage": repair["stage"],
            "depends_on": repair["depends_on"],
            "conflicts_with": repair["conflicts_with"],
            "owner": owner,
            "diagnostic_roots": repair["diagnostic_roots"],
            "operations": operation_audits,
        })

    after_payload = current.encode("utf-8")
    expected = variant["expected_candidate"]
    require(sha256(after_payload) == expected["sha256"], "candidate SHA-256 mismatch")
    require(len(after_payload) == expected["bytes"], "candidate byte mismatch")
    require(len(current.splitlines()) == expected["lines"], "candidate line mismatch")
    after_headers = declaration_headers(current)
    after_comments, after_attributes = comments_and_attributes(current)
    after_heartbeats = heartbeat_counts(current)
    after_trust = trust_counts(current)
    require(after_headers == before_headers and len(after_headers) == DECLARATION_COUNT,
            "declaration headers/order changed")
    require(after_comments == before_comments, "comments changed")
    require(after_attributes == before_attributes, "attributes changed")
    require(after_heartbeats == before_heartbeats ==
            {"token_count": 8, "set_option_count": 8},
            "global heartbeat inventory changed")
    require(after_trust == before_trust == {token: 0 for token in TRUST_TOKENS},
            "trust-six inventory changed or nonzero")
    actual_roots = sorted({root for repair in applied
                           for root in repair["diagnostic_roots"]})
    require(actual_roots == sorted(variant["expected_diagnostic_roots"]),
            "diagnostic root coverage mismatch")
    changed_heartbeat_before = {
        key: sum(operation["owner_region_maxHeartbeats_before"][key]
                 for repair in applied for operation in repair["operations"])
        for key in ("token_count", "set_option_count")
    }
    changed_heartbeat_after = {
        key: sum(operation["owner_region_maxHeartbeats_after"][key]
                 for repair in applied for operation in repair["operations"])
        for key in ("token_count", "set_option_count")
    }
    require(changed_heartbeat_before == changed_heartbeat_after,
            "changed-region heartbeat aggregate changed")
    authority_projection = canonical_authority_projection(contract["authority"])
    audit = {
        "schema": "fa-v63-body-only-patch-audit-v1",
        "status": "PASS_EXACT_BODY_ONLY_DIRECT_LEAN_UNVERIFIED",
        "authority": authority_projection,
        "selection_sha256": contract["selection_sha256"],
        "composition_mode": "EXACT_FROM_AUTHORITY_NONCUMULATIVE",
        "variant": variant_name,
        "candidate_sha256": sha256(after_payload),
        "candidate_bytes": len(after_payload),
        "candidate_lines": len(current.splitlines()),
        "declaration_count": len(after_headers),
        "selected_repair_ids": selected_ids,
        "diagnostic_roots": variant["expected_diagnostic_roots"],
        "repairs": applied,
        "declaration_headers_and_order_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "theorem_statements_identical": True,
        "source_moves": [],
        "outside_selected_owner_regions_byte_identical": True,
        "global_maxHeartbeats_before": before_heartbeats,
        "global_maxHeartbeats_after": after_heartbeats,
        "changed_region_maxHeartbeats_before": changed_heartbeat_before,
        "changed_region_maxHeartbeats_after": changed_heartbeat_after,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "runtime_evidence_fallback_used": False,
        "direct_lean_verified": False,
        "clean_claimed": False,
    }
    evidence = {
        "schema": "fa-v63-exact-materialization-v1",
        "status": "STATIC_PASS_DIRECT_LEAN_REQUIRED",
        "authority": authority_projection,
        "selection_sha256": contract["selection_sha256"],
        "composition_mode": "EXACT_FROM_AUTHORITY_NONCUMULATIVE",
        "variant": variant_name,
        "candidate_sha256": sha256(after_payload),
        "candidate_bytes": len(after_payload),
        "candidate_lines": len(current.splitlines()),
        "declaration_count": len(after_headers),
        "selected_repair_ids": selected_ids,
        "diagnostic_roots": variant["expected_diagnostic_roots"],
        "patch_audit_sha256": sha256(json_bytes(audit)),
        "source_moves": [],
        "global_maxHeartbeats_before": before_heartbeats,
        "global_maxHeartbeats_after": after_heartbeats,
        "changed_region_maxHeartbeats_before": changed_heartbeat_before,
        "changed_region_maxHeartbeats_after": changed_heartbeat_after,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "runtime_evidence_fallback_used": False,
        "direct_lean_verified": False,
        "clean_claimed": False,
        "lean_lake_git_github_network_invoked_by_materializer": False,
    }
    return after_payload, audit, evidence


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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--authority-lock", type=Path, required=True)
    parser.add_argument("--manifest-schema", type=Path, required=True)
    parser.add_argument("--expected-selection-sha256", required=True)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--authority-source", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()
    try:
        output_paths = [args.output, args.audit, args.evidence]
        require(len({path.resolve() for path in output_paths}) == len(output_paths),
                "candidate/audit/evidence output paths must be distinct")
        contract = load_ready_contract(
            selection_path=args.selection,
            authority_lock_path=args.authority_lock,
            manifest_schema_path=args.manifest_schema,
            expected_selection_sha256=args.expected_selection_sha256,
            repo_root=args.repo_root,
        )
        source_payload = (args.authority_source.read_bytes()
                          if args.authority_source.is_file() else b"")
        require(bool(source_payload), "authority source missing")
        candidate, audit, evidence = compose(contract, source_payload, args.variant)
        require(all(not path.exists() for path in output_paths),
                "one or more output paths already exist")
    except PendingInput as exc:
        print(f"PENDING: {exc}", file=sys.stderr)
        return 2
    except (ContractError, OSError) as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        return 86
    exclusive_write(args.audit, json_bytes(audit))
    exclusive_write(args.evidence, json_bytes(evidence))
    exclusive_write(args.output, candidate)
    print(json.dumps(evidence, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
