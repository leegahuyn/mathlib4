#!/usr/bin/env python3
"""Fail-closed generic body-only materializer for v61 direct Lean probes.

PENDING or missing contract inputs return exit code 2 before any filesystem
write.  READY inputs are fully validated and transformed in memory; output,
audit, and evidence files are written atomically only after every lock passes.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tempfile
from pathlib import Path
from typing import Any

from fa_v61_contract import (
    ContractError,
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
    size = len(text)
    in_string = False
    escaped = False
    while index < size:
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
            end = size if end < 0 else end
            spans.append((index, end))
            index = end
            continue
        if text.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while index < size and depth:
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


def comments(text: str) -> list[str]:
    return [text[start:end] for start, end in comment_spans(text)]


def comments_and_attributes(text: str) -> tuple[list[str], list[str]]:
    found_comments: list[str] = []
    attributes: list[str] = []
    index = 0
    while index < len(text):
        if text.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while depth:
                require(index < len(text), "unterminated block comment")
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            found_comments.append(text[start:index])
            continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                end = len(text)
            found_comments.append(text[index:end])
            index = end
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
    result: dict[str, int] = {}
    for token in TRUST_TOKENS:
        pattern = (r"(?<![A-Za-z0-9_])" + re.escape(token)
                   + r"(?![A-Za-z0-9_])")
        result[token] = len(re.findall(pattern, executable))
    return result


def heartbeat_counts(text: str) -> dict[str, int]:
    executable = strip_comments_and_strings(text)
    return {
        "token_count": len(re.findall(r"\bmaxHeartbeats\b", executable)),
        "set_option_count": len(re.findall(
            r"\bset_option\s+maxHeartbeats\b", executable
        )),
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
        region.find(":= by"), region.find(":="), region.find(" where\n")
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
    return observed["start"], observed["end"], region, header


def range_overlaps(spans: list[tuple[int, int]], start: int, end: int) -> bool:
    return any(start < span_end and end > span_start for span_start, span_end in spans)


def atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)
            + "\n").encode("utf-8")


def materialize(args: argparse.Namespace) -> tuple[bytes, dict[str, Any], dict[str, Any]]:
    contract = load_ready_contract(
        selection_path=args.selection,
        authority_lock_path=args.authority_lock,
        manifest_schema_path=args.manifest_schema,
        cross_audit_path=args.cross_audit,
        expected_selection_sha256=args.expected_selection_sha256,
        repo_root=args.repo_root,
    )
    selection = contract["selection"]
    variants = [row for row in selection["variants"] if row["name"] == args.variant]
    require(len(variants) == 1, "variant is not selected exactly once")
    variant = variants[0]
    source_payload = args.authority_source.read_bytes() if args.authority_source.is_file() else b""
    require(bool(source_payload), "authority source missing")
    source_lock = contract["authority"]["source"]
    require(sha256(source_payload) == source_lock["sha256"],
            "authority source SHA-256 mismatch")
    require(len(source_payload) == source_lock["bytes"], "authority source byte mismatch")
    try:
        source = source_payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ContractError("authority source is not UTF-8") from exc
    require(len(source.splitlines()) == source_lock["lines"],
            "authority source line mismatch")
    before_headers = declaration_headers(source)
    require(len(before_headers) == source_lock["declaration_count"] == 4416,
            "authority parsed declaration count mismatch")
    before_comments, before_attributes = comments_and_attributes(source)
    before_heartbeats = heartbeat_counts(source)
    require(before_heartbeats == {"token_count": 8, "set_option_count": 8},
            "authority global maxHeartbeats inventory is not exact 8/8")
    before_trust = trust_counts(source)
    require(before_trust == {token: 0 for token in TRUST_TOKENS},
            "authority executable trust-six is not zero")
    current = source
    applied: list[dict[str, Any]] = []
    selected_repairs = sorted(
        (contract["all_repairs"][repair_id]
         for repair_id in variant["selected_repair_ids"]),
        key=lambda repair: repair["sequence"],
    )
    for repair in selected_repairs:
        repair_id = repair["id"]
        owner = repair["owner"]
        start, end, region, observed_header = locate_owner(current, owner)
        require(sha256(region.encode("utf-8")) == owner["expected_input_region_sha256"],
                f"owner input region SHA mismatch: {repair_id}")
        old, new = repair["old"], repair["new"]
        counts = repair["counts"]
        require(region.count(old) == counts["old_in_owner"],
                f"old owner count mismatch: {repair_id}")
        require(current.count(old) == counts["old_global"],
                f"old global count mismatch: {repair_id}")
        require(region.count(new) == counts["new_in_owner_before"],
                f"new-before owner count mismatch: {repair_id}")
        require(current.count(new) == counts["new_global_before"],
                f"new-before global count mismatch: {repair_id}")
        old_offset = region.find(old)
        require(old_offset >= 0, f"old fragment absent: {repair_id}")
        body_marker = region.find(":=")
        require(body_marker >= 0 and old_offset > body_marker,
                f"transform is not strictly after declaration statement: {repair_id}")
        absolute_old_start = start + old_offset
        require(not range_overlaps(comment_spans(current), absolute_old_start,
                                   absolute_old_start + len(old)),
                f"old fragment overlaps a comment: {repair_id}")
        region_heartbeats_before = heartbeat_counts(region)
        outside_before = (current[:start] + current[end:]).encode("utf-8")
        changed_region = region.replace(old, new, counts["old_in_owner"])
        require(changed_region.count(new) == counts["new_in_owner_after"],
                f"new-after owner count mismatch: {repair_id}")
        require(raw_header(changed_region) == observed_header,
                f"owner header changed: {repair_id}")
        current = current[:start] + changed_region + current[end:]
        changed_end = start + len(changed_region)
        outside_after = (current[:start] + current[changed_end:]).encode("utf-8")
        outside_identical = outside_before == outside_after
        require(outside_identical, f"outside-owner bytes changed: {repair_id}")
        region_heartbeats_after = heartbeat_counts(changed_region)
        require(region_heartbeats_after == region_heartbeats_before,
                f"owner-region maxHeartbeats changed: {repair_id}")
        require(current.count(new) == counts["new_global_after"],
                f"new-after global count mismatch: {repair_id}")
        applied.append({
            "id": repair_id,
            "sequence": repair["sequence"],
            "stage": repair["stage"],
            "depends_on": repair["depends_on"],
            "owner": owner,
            "observed_owner_index": owner["declaration_index"],
            "observed_owner_name": owner["declaration_name"],
            "observed_owner_header_sha256": sha256(observed_header.encode("utf-8")),
            "diagnostic_coverage": repair["diagnostic_coverage"],
            "old_sha256": sha256(old.encode("utf-8")),
            "new_sha256": sha256(new.encode("utf-8")),
            "owner_region_maxHeartbeats_before": region_heartbeats_before,
            "owner_region_maxHeartbeats_after": region_heartbeats_after,
            "outside_owner_before_sha256": sha256(outside_before),
            "outside_owner_after_sha256": sha256(outside_after),
            "outside_owner_byte_identical": outside_identical,
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
    source_moves = [] if after_headers == before_headers else [
        "DECLARATION_HEADER_OR_SEQUENCE_DRIFT"
    ]
    require(source_moves == [], "declaration headers/order changed")
    require(after_comments == before_comments, "comments changed")
    require(after_attributes == before_attributes, "attributes changed")
    require(after_heartbeats == before_heartbeats, "maxHeartbeats inventory changed")
    require(after_trust == before_trust == {token: 0 for token in TRUST_TOKENS},
            "trust-six inventory changed or nonzero")
    coverage = sorted({ordinal for repair in applied
                       for ordinal in repair["diagnostic_coverage"]["baseline_ordinals"]})
    require(coverage == variant["expected_diagnostic_coverage"],
            "applied diagnostic coverage mismatch")
    authority_projection = canonical_authority_projection(contract["authority"])
    changed_heartbeats_before = {
        "token_count": sum(row["owner_region_maxHeartbeats_before"]["token_count"]
                           for row in applied),
        "set_option_count": sum(
            row["owner_region_maxHeartbeats_before"]["set_option_count"]
            for row in applied
        ),
    }
    changed_heartbeats_after = {
        "token_count": sum(row["owner_region_maxHeartbeats_after"]["token_count"]
                           for row in applied),
        "set_option_count": sum(
            row["owner_region_maxHeartbeats_after"]["set_option_count"]
            for row in applied
        ),
    }
    audit = {
        "schema": "fa-v61-generic-body-only-patch-audit-v1",
        "status": "PASS_EXACT_BODY_ONLY",
        "authority": authority_projection,
        "selection_index_sha256": contract["selection_sha256"],
        "variant": args.variant,
        "candidate_sha256": sha256(after_payload),
        "candidate_bytes": len(after_payload),
        "candidate_lines": len(current.splitlines()),
        "selected_repair_ids": [repair["id"] for repair in applied],
        "diagnostic_coverage": coverage,
        "repairs": applied,
        "all_declaration_headers_byte_identical": True,
        "declaration_sequence_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "theorem_statements_identical": True,
        "source_moves": source_moves,
        "outside_selected_owner_regions_byte_identical": all(
            row["outside_owner_byte_identical"] for row in applied
        ),
        "global_maxHeartbeats_before": before_heartbeats,
        "global_maxHeartbeats_after": after_heartbeats,
        "changed_region_maxHeartbeats_before": changed_heartbeats_before,
        "changed_region_maxHeartbeats_after": changed_heartbeats_after,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "runtime_evidence_fallback_used": False,
        "direct_lean_verified": False,
    }
    evidence = {
        "schema": "fa-v61-generic-body-only-materialization-v1",
        "status": "STATIC_PASS_DIRECT_LEAN_REQUIRED",
        "authority": authority_projection,
        "selection_index_sha256": contract["selection_sha256"],
        "variant": args.variant,
        "candidate_sha256": sha256(after_payload),
        "candidate_bytes": len(after_payload),
        "candidate_lines": len(current.splitlines()),
        "selected_repair_ids": [repair["id"] for repair in applied],
        "diagnostic_coverage": coverage,
        "patch_audit_sha256": sha256(json_bytes(audit)),
        "source_moves": source_moves,
        "outside_selected_owner_regions_byte_identical": all(
            row["outside_owner_byte_identical"] for row in applied
        ),
        "global_maxHeartbeats_before": before_heartbeats,
        "global_maxHeartbeats_after": after_heartbeats,
        "changed_region_maxHeartbeats_before": changed_heartbeats_before,
        "changed_region_maxHeartbeats_after": changed_heartbeats_after,
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "runtime_evidence_fallback_used": False,
        "direct_lean_verified": False,
        "lean_lake_git_github_network_invoked_by_materializer": False,
    }
    return after_payload, audit, evidence


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--authority-lock", type=Path, required=True)
    parser.add_argument("--manifest-schema", type=Path, required=True)
    parser.add_argument("--cross-audit", type=Path, required=True)
    parser.add_argument("--expected-selection-sha256", required=True)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--authority-source", type=Path, required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()
    try:
        outputs = [args.output, args.audit, args.evidence]
        require(len({path.resolve() for path in outputs}) == len(outputs),
                "output, audit, and evidence paths must be distinct")
        candidate, audit, evidence = materialize(args)
    except PendingInput as exc:
        print(f"PENDING: {exc}", file=sys.stderr)
        return 2
    except (ContractError, OSError) as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        return 86
    atomic_write(args.output, candidate)
    atomic_write(args.audit, json_bytes(audit))
    atomic_write(args.evidence, json_bytes(evidence))
    print(json.dumps(evidence, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
