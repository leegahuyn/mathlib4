#!/usr/bin/env python3
"""Build and statically audit one cumulative FA v40 candidate.

This tool never invokes Lean, Lake, git, or GitHub.  It applies an exact,
source-locked repair manifest to the authoritative v39 artifact and rejects
ambiguous replacements, owner drift, undeclared theorem-header changes, or
new executable trust tokens.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


AUTHORITY_SOURCE_SHA256 = (
    "530baa644c7a86eda78328920eda4b8f5fd273bd29d9f04351914396303d4c03"
)

DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
THEOREM_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(theorem|lemma)\s+([^\s(:]+)"
)
TRUST_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_regions(text: str) -> list[dict[str, Any]]:
    matches = list(DECL_RE.finditer(text))
    result: list[dict[str, Any]] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        result.append(
            {
                "index": index,
                "name": match.group(1),
                "start": match.start(),
                "end": end,
                "text": text[match.start() : end],
            }
        )
    return result


def owner_at(text: str, offset: int) -> tuple[int, str] | None:
    regions = declaration_regions(text)
    for region in regions:
        if region["start"] <= offset < region["end"]:
            return region["index"], region["name"]
    return None


def theorem_headers(text: str) -> dict[str, str]:
    declaration_matches = list(DECL_RE.finditer(text))
    declaration_starts = [m.start() for m in declaration_matches]
    result: dict[str, str] = {}
    for match in THEOREM_RE.finditer(text):
        next_start = next(
            (start for start in declaration_starts if start > match.start()), len(text)
        )
        block = text[match.start() : next_start]
        cuts = [pos for pos in (block.find(":= by"), block.find(":=")) if pos >= 0]
        header = block if not cuts else block[: min(cuts)]
        index = declaration_starts.index(match.start())
        name = match.group(2)
        key = f"{index}:{name}"
        result[key] = re.sub(r"\s+", " ", header).strip()
    return result


def strip_noncode(text: str) -> str:
    """Mask nested comments, line comments, char literals, and strings."""

    chars = list(text)
    i = 0
    depth = 0
    in_string = False
    in_char = False
    escaped = False
    while i < len(chars):
        if depth:
            if i + 1 < len(chars) and text[i : i + 2] == "/-":
                chars[i] = chars[i + 1] = " "
                depth += 1
                i += 2
                continue
            if i + 1 < len(chars) and text[i : i + 2] == "-/":
                chars[i] = chars[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue
        if in_string or in_char:
            quote = '"' if in_string else "'"
            if chars[i] != "\n":
                original = chars[i]
                chars[i] = " "
            else:
                original = chars[i]
            if escaped:
                escaped = False
            elif original == "\\":
                escaped = True
            elif original == quote:
                in_string = in_char = False
            i += 1
            continue
        if i + 1 < len(chars) and text[i : i + 2] == "/-":
            chars[i] = chars[i + 1] = " "
            depth = 1
            i += 2
            continue
        if i + 1 < len(chars) and text[i : i + 2] == "--":
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        if chars[i] == '"':
            chars[i] = " "
            in_string = True
            i += 1
            continue
        if chars[i] == "'":
            # Lean identifiers can contain apostrophes.  Treat a quote as a
            # character literal only when a closing quote is nearby.
            close = text.find("'", i + 1, min(len(text), i + 8))
            if close >= 0:
                chars[i] = " "
                in_char = True
            i += 1
            continue
        i += 1
    if depth or in_string or in_char:
        raise SystemExit("noncode scanner ended in an unterminated token")
    return "".join(chars)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    counts: dict[str, int] = {}
    for token in TRUST_TOKENS:
        pattern = r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])"
        counts[token] = len(re.findall(pattern, code))
    return counts


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("audit", type=Path)
    parser.add_argument(
        "--allow-unlocked-candidate",
        action="store_true",
        help="static drafting only; promotion workflows must never use this",
    )
    args = parser.parse_args()

    source_bytes = args.source.read_bytes()
    source_sha = sha256_bytes(source_bytes)
    if source_sha != AUTHORITY_SOURCE_SHA256:
        raise SystemExit(
            f"authority source mismatch: {source_sha} != {AUTHORITY_SOURCE_SHA256}"
        )
    source = source_bytes.decode("utf-8")
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    if manifest.get("schema") != "fa-v40-saturation-repairs-v1":
        raise SystemExit("unexpected manifest schema")
    if manifest.get("authority_source_sha256") != source_sha:
        raise SystemExit("manifest authority mismatch")

    original_declarations = [m.group(1) for m in DECL_RE.finditer(source)]
    original_headers = theorem_headers(source)
    original_trust = trust_counts(source)
    if any(original_trust.values()):
        raise SystemExit(f"authority source executable trust tokens: {original_trust}")

    current = source
    applied: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for repair in manifest.get("repairs", []):
        repair_id = repair["id"]
        if repair_id in seen_ids:
            raise SystemExit(f"duplicate repair id: {repair_id}")
        seen_ids.add(repair_id)
        old = repair["old"]
        new = repair["new"]
        expected = int(repair.get("expected_count", 1))
        count = current.count(old)
        if count != expected:
            raise SystemExit(
                f"{repair_id}: old fragment count {count}, expected {expected}"
            )
        offsets: list[int] = []
        search_from = 0
        while True:
            offset = current.find(old, search_from)
            if offset < 0:
                break
            offsets.append(offset)
            search_from = offset + len(old)
        actual_owners = [owner_at(current, offset) for offset in offsets]
        declared_owner = repair.get("owner")
        declared_owners = repair.get("owners")
        if expected == 1:
            actual_owner = actual_owners[0]
            if declared_owner is None:
                if repair.get("kind") != "environment":
                    raise SystemExit(
                        f"{repair_id}: only environment edits may omit an owner"
                    )
            elif actual_owner is None or actual_owner[1] != declared_owner:
                raise SystemExit(
                    f"{repair_id}: owner mismatch {actual_owner}, expected {declared_owner}"
                )
        else:
            if declared_owner is not None or not isinstance(declared_owners, list):
                raise SystemExit(
                    f"{repair_id}: multi-repair requires an exact owners list"
                )
            names = [owner[1] if owner else None for owner in actual_owners]
            if names != declared_owners:
                raise SystemExit(
                    f"{repair_id}: owners mismatch {names}, expected {declared_owners}"
                )
        current = current.replace(old, new)
        # A legitimate bounded environment insertion can retain `old` as a
        # literal prefix of `new`.  Validate the exact algebraic post-count
        # instead of assuming every replacement must make the old substring
        # disappear globally.
        expected_old_after = expected * new.count(old)
        actual_old_after = current.count(old)
        if actual_old_after != expected_old_after:
            raise SystemExit(
                f"{repair_id}: old fragment post-count {actual_old_after}, "
                f"expected {expected_old_after}"
            )
        applied.append(
            {
                "id": repair_id,
                "kind": repair.get("kind", "body"),
                "owner": declared_owner,
                "owners": declared_owners,
                "confidence": repair.get("confidence"),
                "old_sha256": sha256_bytes(old.encode()),
                "new_sha256": sha256_bytes(new.encode()),
            }
        )

    candidate_bytes = current.encode("utf-8")
    candidate_sha = sha256_bytes(candidate_bytes)
    expected_candidate = manifest.get("expected_candidate_sha256")
    if not expected_candidate and not args.allow_unlocked_candidate:
        raise SystemExit("manifest has no expected candidate SHA")
    if expected_candidate and candidate_sha != expected_candidate:
        raise SystemExit(
            f"candidate SHA mismatch: {candidate_sha} != {expected_candidate}"
        )

    candidate_declarations = [m.group(1) for m in DECL_RE.finditer(current)]
    if candidate_declarations != original_declarations:
        raise SystemExit("declaration name/order changed")

    candidate_headers = theorem_headers(current)
    if set(candidate_headers) != set(original_headers):
        raise SystemExit("theorem/lemma set changed")
    header_changes = {
        name: {"before": original_headers[name], "after": candidate_headers[name]}
        for name in original_headers
        if original_headers[name] != candidate_headers[name]
    }
    allowed_header_changes = set(manifest.get("allowed_header_changes", []))
    if set(header_changes) != allowed_header_changes:
        raise SystemExit(
            "header delta mismatch: "
            f"actual={sorted(header_changes)} allowed={sorted(allowed_header_changes)}"
        )

    candidate_trust = trust_counts(current)
    if any(candidate_trust.values()) or candidate_trust != original_trust:
        raise SystemExit(
            f"candidate executable trust mismatch: {original_trust} -> {candidate_trust}"
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(candidate_bytes)
    audit = {
        "schema": "fa-v40-saturation-candidate-audit-v1",
        "authority_source_sha256": source_sha,
        "candidate_sha256": candidate_sha,
        "candidate_bytes": len(candidate_bytes),
        "candidate_lines": len(current.splitlines()),
        "declaration_count": len(candidate_declarations),
        "declaration_sequence_identical": True,
        "theorem_lemma_count": len(candidate_headers),
        "header_changes": header_changes,
        "allowed_header_changes_exact": True,
        "executable_trust_counts_before": original_trust,
        "executable_trust_counts_after": candidate_trust,
        "applied_repair_count": len(applied),
        "applied_repairs": applied,
        "lean_lake_git_github_invoked": False,
        "direct_lean_verified": False,
    }
    args.audit.write_text(
        json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
