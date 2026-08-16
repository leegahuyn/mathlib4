#!/usr/bin/env python3
"""Deterministic, scope-aware postprocessor for QYM broad-repair pass1.

Input is pinned to the exact pass1 output.  The postprocessor restores two
families that were over-rewritten by substring replacement and eliminates the
obsolete `namespace A := Target` aliases without pretending that `namespace A`
is an equivalent command.  Alias-qualified names are expanded only in Lean
code, only while the alias's enclosing namespace is active.  Comments and
strings are not rewritten.  No Lean/Lake process is invoked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path


EXPECTED_INPUT_SHA256 = "f264de0fd05911a4594b2087aa92caa5deda95c0fd378d09a5d311498b019e56"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


@dataclass
class Block:
    kind: str
    name: str
    start: int
    end: int | None = None


@dataclass
class Alias:
    name: str
    target: str
    command_start: int
    command_end: int
    parent: Block
    active_start: int
    active_end: int = -1
    qualified_rewrites: int = 0
    open_rewrites: int = 0
    bare_code_tokens: list[int] = field(default_factory=list)


ALIAS_RE = re.compile(
    r"^\s*namespace\s+([A-Za-z][A-Za-z0-9_]*)\s*:=\s*(.*?)\s*$", re.MULTILINE
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s:=]+)\s*$")
SECTION_RE = re.compile(r"^\s*section(?:\s+([^\s]+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([^\s]+))?\s*$")
TARGET_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


def parse_aliases(lines: list[str]) -> tuple[list[Alias], set[int], list[Block]]:
    stack: list[Block] = []
    blocks: list[Block] = []
    aliases: list[Alias] = []
    removed: set[int] = set()
    i = 0
    while i < len(lines):
        raw = lines[i]
        line = raw.rstrip("\n")
        am = ALIAS_RE.match(line)
        if am:
            name, rhs = am.groups()
            parent = next((b for b in reversed(stack) if b.kind == "namespace"), None)
            if parent is None:
                raise AssertionError(f"alias without enclosing namespace at line {i + 1}")
            command_end = i
            target = rhs.strip()
            if not target:
                if i + 1 >= len(lines):
                    raise AssertionError(f"missing alias target at line {i + 1}")
                command_end = i + 1
                target = lines[command_end].strip()
            if not TARGET_RE.fullmatch(target):
                raise AssertionError(f"invalid alias target at line {i + 1}: {target!r}")
            removed.update(range(i, command_end + 1))
            aliases.append(
                Alias(
                    name=name,
                    target=target,
                    command_start=i,
                    command_end=command_end,
                    parent=parent,
                    active_start=command_end + 1,
                )
            )
            i = command_end + 1
            continue
        nm = NAMESPACE_RE.match(line)
        sm = SECTION_RE.match(line)
        em = END_RE.match(line)
        if nm:
            block = Block("namespace", nm.group(1), i)
            stack.append(block)
            blocks.append(block)
        elif sm:
            block = Block("section", sm.group(1) or "", i)
            stack.append(block)
            blocks.append(block)
        elif em:
            if not stack:
                raise AssertionError(f"unmatched end at line {i + 1}: {line}")
            stack.pop().end = i
        i += 1
    for block in stack:
        block.end = len(lines)
    for alias in aliases:
        if alias.parent.end is None:
            raise AssertionError(f"unclosed parent namespace for line {alias.command_start + 1}")
        alias.active_end = alias.parent.end

    per_parent: dict[int, set[str]] = defaultdict(set)
    for alias in aliases:
        key = alias.parent.start
        if alias.name in per_parent[key]:
            raise AssertionError(
                f"duplicate alias {alias.name} in namespace at line {alias.parent.start + 1}"
            )
        per_parent[key].add(alias.name)
    return aliases, removed, blocks


def is_ident_start(ch: str) -> bool:
    return ch == "_" or ch.isalpha()


def is_ident_continue(ch: str) -> bool:
    return ch == "_" or ch == "'" or ch.isalnum()


def count_scoped_code_refs(source: str, mapping_by_line: list[dict[str, Alias]]) -> tuple[int, int]:
    """Count eligible qualified/open alias references, ignoring comments and strings."""
    lines = source.splitlines(keepends=True)
    open_mode = [bool(re.match(r"^\s*open\s+(?!scoped\b)", line)) for line in lines]
    qualified = 0
    opened = 0
    state = "code"
    block_depth = 0
    escaped = False
    line_no = 0
    i = 0
    while i < len(source):
        ch = source[i]
        pair = source[i : i + 2]
        if state == "code":
            if pair == "--":
                state = "line_comment"
                i += 2
                continue
            if pair == "/-":
                state = "block_comment"
                block_depth = 1
                i += 2
                continue
            if ch == '"':
                state = "string"
                escaped = False
                i += 1
                continue
            if is_ident_start(ch):
                j = i + 1
                while j < len(source) and is_ident_continue(source[j]):
                    j += 1
                atom = source[i:j]
                alias = mapping_by_line[line_no].get(atom)
                prefix = i == 0 or source[i - 1] != "."
                if alias is not None and prefix and j < len(source) and source[j] == ".":
                    qualified += 1
                elif alias is not None and prefix and open_mode[line_no]:
                    opened += 1
                i = j
                continue
        elif state == "line_comment":
            if ch == "\n":
                state = "code"
        elif state == "block_comment":
            if pair == "/-":
                block_depth += 1
                i += 2
                continue
            if pair == "-/":
                block_depth -= 1
                i += 2
                if block_depth == 0:
                    state = "code"
                continue
        elif state == "string":
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                state = "code"
        if ch == "\n":
            line_no += 1
        i += 1
    return qualified, opened


def expand_aliases(text: str) -> tuple[str, list[Alias], dict[str, object]]:
    lines = text.splitlines(keepends=True)
    aliases, removed, blocks = parse_aliases(lines)
    if len(aliases) != 230:
        raise AssertionError(f"expected 230 namespace aliases, got {len(aliases)}")

    starts: dict[int, list[Alias]] = defaultdict(list)
    ends: dict[int, list[Alias]] = defaultdict(list)
    for alias in aliases:
        starts[alias.active_start].append(alias)
        ends[alias.active_end].append(alias)

    active: dict[str, list[Alias]] = defaultdict(list)
    mapping_by_line: list[dict[str, Alias]] = []
    for line_no in range(len(lines)):
        for alias in ends.get(line_no, []):
            bucket = active[alias.name]
            if not bucket or bucket[-1] is not alias:
                raise AssertionError(f"alias scope stack mismatch for {alias.name}")
            bucket.pop()
        for alias in starts.get(line_no, []):
            active[alias.name].append(alias)
        mapping_by_line.append({name: bucket[-1] for name, bucket in active.items() if bucket})

    blanked = [("\n" if lines[i].endswith("\n") else "") if i in removed else lines[i]
               for i in range(len(lines))]
    source = "".join(blanked)
    open_mode = [bool(re.match(r"^\s*open\s+(?!scoped\b)", line)) for line in blanked]

    out: list[str] = []
    state = "code"
    block_depth = 0
    escaped = False
    line_no = 0
    i = 0
    while i < len(source):
        ch = source[i]
        pair = source[i : i + 2]
        if state == "code":
            if pair == "--":
                out.append(pair)
                i += 2
                state = "line_comment"
                continue
            if pair == "/-":
                out.append(pair)
                i += 2
                block_depth = 1
                state = "block_comment"
                continue
            if ch == '"':
                out.append(ch)
                i += 1
                state = "string"
                escaped = False
                continue
            if is_ident_start(ch):
                j = i + 1
                while j < len(source) and is_ident_continue(source[j]):
                    j += 1
                atom = source[i:j]
                alias = mapping_by_line[line_no].get(atom)
                at_dotted_prefix = j < len(source) and source[j] == "." and (i == 0 or source[i - 1] != ".")
                if alias is not None and at_dotted_prefix:
                    out.append(alias.target)
                    alias.qualified_rewrites += 1
                elif alias is not None and open_mode[line_no] and (i == 0 or source[i - 1] != "."):
                    out.append(alias.target)
                    alias.open_rewrites += 1
                else:
                    out.append(atom)
                    if alias is not None and (i == 0 or source[i - 1] != "."):
                        alias.bare_code_tokens.append(line_no + 1)
                i = j
                continue
        elif state == "line_comment":
            if ch == "\n":
                state = "code"
        elif state == "block_comment":
            if pair == "/-":
                out.append(pair)
                i += 2
                block_depth += 1
                continue
            if pair == "-/":
                out.append(pair)
                i += 2
                block_depth -= 1
                if block_depth == 0:
                    state = "code"
                continue
        elif state == "string":
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                state = "code"
        out.append(ch)
        if ch == "\n":
            line_no += 1
        i += 1

    result = "".join(out)
    malformed = len(ALIAS_RE.findall(result))
    # A second scoped, lexical scan must find no eligible code references.  Text
    # in documentation/comments is intentionally not changed.
    remaining_qualified, remaining_open = count_scoped_code_refs(result, mapping_by_line)

    summary = {
        "alias_commands": len(aliases),
        "alias_command_lines_blanked": len(removed),
        "qualified_rewrites": sum(a.qualified_rewrites for a in aliases),
        "open_rewrites": sum(a.open_rewrites for a in aliases),
        "bare_code_tokens": sum(len(a.bare_code_tokens) for a in aliases),
        "malformed_alias_commands_remaining": malformed,
        "scoped_qualified_alias_references_remaining": remaining_qualified,
        "scoped_open_alias_references_remaining": remaining_open,
        "regular_blocks_parsed": len(blocks),
    }
    return result, aliases, summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--audit", required=True)
    args = parser.parse_args()

    input_path = Path(args.input)
    raw = input_path.read_bytes()
    if sha256(raw) != EXPECTED_INPUT_SHA256:
        raise AssertionError("pass1 input SHA-256 mismatch")
    if b"\r" in raw or b"\x00" in raw or not raw.endswith(b"\n"):
        raise AssertionError("pass1 encoding/newline invariant mismatch")
    text = raw.decode("utf-8")

    if text.count("star_ofReal") != 8 or text.count("star_eq_iff_im") != 1:
        raise AssertionError("over-rewrite inventory mismatch")
    text = text.replace("star_ofReal", "RCLike.conj_ofReal")
    text = text.replace("star_eq_iff_im", "Complex.conj_eq_iff_im")
    repaired, aliases, summary = expand_aliases(text)

    if repaired.count("star_ofReal") or repaired.count("star_eq_iff_im"):
        raise AssertionError("over-rewritten identifiers remain")
    if repaired.count("RCLike.conj_ofReal") != 8:
        raise AssertionError("RCLike.conj_ofReal restoration mismatch")
    if repaired.count("Complex.conj_eq_iff_im") != 1:
        raise AssertionError("Complex.conj_eq_iff_im restoration mismatch")
    for key in (
        "malformed_alias_commands_remaining",
        "scoped_qualified_alias_references_remaining",
        "scoped_open_alias_references_remaining",
    ):
        if summary[key] != 0:
            raise AssertionError(f"{key}: {summary[key]}")

    candidate = repaired.encode("utf-8")
    if b"\r" in candidate or b"\x00" in candidate or not candidate.endswith(b"\n"):
        raise AssertionError("candidate encoding/newline invariant mismatch")
    output_path = Path(args.output)
    audit_path = Path(args.audit)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(candidate)

    per_alias = [
        {
            "alias": a.name,
            "target": a.target,
            "command_line": a.command_start + 1,
            "parent_namespace_line": a.parent.start + 1,
            "parent_end_line": a.parent.end + 1 if a.parent.end is not None else None,
            "qualified_rewrites": a.qualified_rewrites,
            "open_rewrites": a.open_rewrites,
            "bare_code_token_count": len(a.bare_code_tokens),
            "bare_code_token_lines": a.bare_code_tokens[:40],
        }
        for a in aliases
    ]
    result = {
        "schema": "qym-pass1-scope-aware-namespace-expansion-v1",
        "input_sha256": EXPECTED_INPUT_SHA256,
        "input_bytes": len(raw),
        "output_sha256": sha256(candidate),
        "output_git_blob": git_blob(candidate),
        "output_bytes": len(candidate),
        "input_lf": raw.count(b"\n"),
        "output_lf": candidate.count(b"\n"),
        "restored": {
            "star_ofReal_to_RCLike.conj_ofReal": 8,
            "star_eq_iff_im_to_Complex.conj_eq_iff_im": 1,
        },
        "namespace_expansion": summary,
        "aliases": per_alias,
        "lean_executed": False,
    }
    with audit_path.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
