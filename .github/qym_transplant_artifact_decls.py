#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse
import hashlib
import json
import re

DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)


@dataclass
class Block:
    name: str
    start: int
    end: int
    text: str


def parse_blocks(text: str) -> tuple[list[str], list[Block]]:
    lines = text.splitlines(keepends=True)
    marks: list[tuple[str, int]] = []
    for i, line in enumerate(lines):
        if line[:1].isspace():
            continue
        m = DECL_RE.match(line)
        if m:
            marks.append((m.group("name"), i))
    blocks: list[Block] = []
    for j, (name, start) in enumerate(marks):
        end = marks[j + 1][1] if j + 1 < len(marks) else len(lines)
        blocks.append(Block(name, start, end, "".join(lines[start:end])))
    return lines, blocks


def block_map(text: str) -> tuple[list[str], list[Block], dict[str, Block]]:
    lines, blocks = parse_blocks(text)
    mapping: dict[str, Block] = {}
    for block in blocks:
        if block.name in mapping:
            raise SystemExit(f"duplicate top-level declaration name: {block.name}")
        mapping[block.name] = block
    return lines, blocks, mapping


def normalize(block: str) -> str:
    return "\n".join(line.rstrip() for line in block.strip().splitlines())


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def changed_names(base: str, donor: str) -> tuple[list[str], list[str], list[str]]:
    _, base_blocks, bm = block_map(base)
    _, donor_blocks, dm = block_map(donor)
    changed = [
        name for name in bm.keys() & dm.keys()
        if normalize(bm[name].text) != normalize(dm[name].text)
    ]
    added = [b.name for b in donor_blocks if b.name not in bm]
    removed = [b.name for b in base_blocks if b.name not in dm]
    return changed, added, removed


def apply_donor(current: str, base: str, donor: str, label: str) -> tuple[str, dict]:
    _, base_blocks, bm = block_map(base)
    _, donor_blocks, dm = block_map(donor)
    changed, added, removed = changed_names(base, donor)
    if not changed and not added and not removed:
        raise SystemExit(f"{label}: donor has no declaration-level changes")

    report = {"label": label, "changed": changed, "added": added, "removed": removed}

    # Replace or remove from bottom to top so line offsets remain stable.
    lines, current_blocks, cm = block_map(current)
    edits: list[tuple[int, int, str, str]] = []
    for name in changed:
        if name not in cm:
            raise SystemExit(f"{label}: changed declaration missing in current source: {name}")
        edits.append((cm[name].start, cm[name].end, dm[name].text, f"replace:{name}"))
    for name in removed:
        if name not in cm:
            continue
        if name in bm and normalize(cm[name].text) != normalize(bm[name].text):
            raise SystemExit(f"{label}: refusing to remove independently modified declaration: {name}")
        edits.append((cm[name].start, cm[name].end, "", f"remove:{name}"))

    for start, end, replacement, _ in sorted(edits, reverse=True):
        lines[start:end] = [replacement]
    current = "".join(lines)

    # Insert donor-only declarations in donor order before the next declaration
    # that exists in current; otherwise append at EOF.
    for name in added:
        _, donor_order, donor_map = block_map(donor)
        donor_index = next(i for i, b in enumerate(donor_order) if b.name == name)
        next_name = next(
            (b.name for b in donor_order[donor_index + 1:]
             if b.name in block_map(current)[2]),
            None,
        )
        lines, _, cm = block_map(current)
        insertion = dm[name].text
        if next_name is None:
            if current and not current.endswith("\n"):
                current += "\n"
            current += insertion
        else:
            idx = cm[next_name].start
            lines[idx:idx] = [insertion]
            current = "".join(lines)

    return current, report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", required=True)
    parser.add_argument("--current", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--donor", action="append", default=[], help="LABEL=PATH")
    args = parser.parse_args()

    base_path = Path(args.base)
    current_path = Path(args.current)
    base = base_path.read_text(encoding="utf-8")
    current = current_path.read_text(encoding="utf-8")
    before_raw = current_path.read_bytes()
    before_audit = audit(current)

    reports = []
    for spec in args.donor:
        if "=" not in spec:
            raise SystemExit(f"invalid donor spec: {spec}")
        label, path = spec.split("=", 1)
        donor = Path(path).read_text(encoding="utf-8")
        current, report = apply_donor(current, base, donor, label)
        reports.append(report)

    after_audit = audit(current)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")

    out_path = Path(args.output)
    out_path.write_text(current, encoding="utf-8")
    after_raw = out_path.read_bytes()
    report = {
        "schema": "qym-artifact-declaration-transplant-v1",
        "base_sha256": hashlib.sha256(base_path.read_bytes()).hexdigest(),
        "input_sha256": hashlib.sha256(before_raw).hexdigest(),
        "input_blob": git_blob(before_raw),
        "candidate_sha256": hashlib.sha256(after_raw).hexdigest(),
        "candidate_blob": git_blob(after_raw),
        "bytes": len(after_raw),
        "lf": after_raw.count(b"\n"),
        "donors": reports,
        "forbidden": after_audit,
    }
    Path(args.report).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
