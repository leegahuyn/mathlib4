#!/usr/bin/env python3
"""Fail-closed sequencer for independently staged Mock2 FA repair libraries.

This tool never fixes candidate size/hash in advance.  It starts from an exact
source supplied by the caller, applies only exact literal edits from explicitly
listed libraries, and re-attests structural/trust invariants after every
library.  Candidate SHA/bytes/lines are measurements of the materialized
result.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s(:]+)"
)
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"\baxiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declarations(source: str) -> list[re.Match[str]]:
    return list(DECL_RE.finditer(source))


def declaration_names(source: str) -> list[str]:
    return [m.group("name") for m in declarations(source)]


def declaration_segments(source: str) -> list[tuple[int, int, str]]:
    ds = declarations(source)
    out: list[tuple[int, int, str]] = []
    for i, m in enumerate(ds):
        end = ds[i + 1].start() if i + 1 < len(ds) else len(source)
        out.append((m.start(), end, m.group("name")))
    return out


def declaration_headers(source: str) -> list[str]:
    out: list[str] = []
    for start, end, _ in declaration_segments(source):
        seg = source[start:end]
        positions: list[int] = []
        p = seg.find(":=")
        if p >= 0:
            positions.append(p)
        for marker in ("\nwhere\n", "\nwhere ", " where\n"):
            q = seg.find(marker)
            if q >= 0:
                positions.append(q)
        cut = min(positions) if positions else len(seg)
        out.append(seg[:cut].rstrip())
    return out


def forbidden_counts(source: str) -> dict[str, int]:
    return {name: len(rx.findall(source)) for name, rx in FORBIDDEN.items()}


def normalize_edit(obj: dict[str, Any], *, owner: str) -> dict[str, Any]:
    old = obj.get("old_fragment")
    new = obj.get("new_fragment")
    if not isinstance(old, str) or not isinstance(new, str):
        raise ValueError(f"{owner}: literal edit lacks old_fragment/new_fragment")
    return {"old": old, "new": new, "raw": obj}


def environment_edits(payload: dict[str, Any]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    one = payload.get("environment_replacement")
    if isinstance(one, dict):
        result.append(normalize_edit(one, owner="environment_replacement"))
    many = payload.get("environment_replacements")
    if isinstance(many, list):
        for i, item in enumerate(many):
            if isinstance(item, dict):
                result.append(normalize_edit(item, owner=f"environment_replacements[{i}]"))
    edits = payload.get("edits")
    if isinstance(edits, list):
        for i, item in enumerate(edits):
            if isinstance(item, dict) and item.get("scope") == "environment":
                result.append(normalize_edit(item, owner=f"edits[{i}]"))
    return result


def proof_repairs(payload: dict[str, Any]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    repairs = payload.get("repairs")
    if isinstance(repairs, list):
        result.extend(x for x in repairs if isinstance(x, dict))
    edits = payload.get("edits")
    if isinstance(edits, list):
        result.extend(
            x for x in edits
            if isinstance(x, dict)
            and x.get("scope") != "environment"
            and isinstance(x.get("declaration_index"), int)
            and isinstance(x.get("declaration_name"), str)
        )
    return result


def replacement_list(repair: dict[str, Any]) -> list[dict[str, Any]]:
    rs = repair.get("replacements")
    if isinstance(rs, list):
        return [normalize_edit(x, owner="replacement") for x in rs if isinstance(x, dict)]
    if isinstance(repair.get("old_fragment"), str) and isinstance(repair.get("new_fragment"), str):
        return [normalize_edit(repair, owner="repair")]
    return []


def replace_environment(source: str, edit: dict[str, Any], label: str) -> tuple[str, dict[str, Any]]:
    old, new, raw = edit["old"], edit["new"], edit["raw"]
    old_count = source.count(old)
    new_before = source.count(new)
    expected_old = raw.get("expected_global_old_occurrences", raw.get("old_global_count", 1))
    expected_new = raw.get("expected_global_new_occurrences_before", raw.get("new_global_count_before", 0))
    if old_count != expected_old:
        raise ValueError(f"{label}: environment old count {old_count}, expected {expected_old}")
    if new_before != expected_new:
        raise ValueError(f"{label}: environment new-before count {new_before}, expected {expected_new}")
    after = source.replace(old, new, 1)
    return after, {
        "kind": "environment",
        "id": raw.get("id", label),
        "old_sha256": sha(old.encode()),
        "new_sha256": sha(new.encode()),
    }


def replace_in_declaration(source: str, repair: dict[str, Any], label: str) -> tuple[str, list[dict[str, Any]]]:
    idx = repair.get("declaration_index")
    name = repair.get("declaration_name")
    if not isinstance(idx, int) or not isinstance(name, str):
        raise ValueError(f"{label}: repair missing declaration index/name")
    segs = declaration_segments(source)
    if idx < 0 or idx >= len(segs):
        raise ValueError(f"{label}: declaration index {idx} out of range")
    start, end, actual_name = segs[idx]
    if actual_name != name:
        raise ValueError(f"{label}: declaration {idx} is {actual_name}, expected {name}")
    applied: list[dict[str, Any]] = []
    for j, edit in enumerate(replacement_list(repair)):
        old, new, raw = edit["old"], edit["new"], edit["raw"]
        segs = declaration_segments(source)
        start, end, actual_name = segs[idx]
        segment = source[start:end]
        local_old = segment.count(old)
        local_new = segment.count(new)
        expected_local_old = raw.get("target_old_count", raw.get("expected_local_old_occurrences", 1))
        expected_local_new = raw.get("target_new_count_before", raw.get("expected_local_new_occurrences_before", 0))
        if local_old != expected_local_old:
            raise ValueError(f"{label}[{j}]: old count in {name} is {local_old}, expected {expected_local_old}")
        if local_new != expected_local_new:
            raise ValueError(f"{label}[{j}]: new-before count in {name} is {local_new}, expected {expected_local_new}")
        updated = segment.replace(old, new, 1)
        source = source[:start] + updated + source[end:]
        applied.append({
            "kind": "proof",
            "declaration_index": idx,
            "declaration_name": name,
            "old_sha256": sha(old.encode()),
            "new_sha256": sha(new.encode()),
        })
    return source, applied


def structural_snapshot(source: str) -> dict[str, Any]:
    names = declaration_names(source)
    headers = declaration_headers(source)
    return {
        "declaration_count": len(names),
        "declaration_sequence_sha256": sha("\n".join(names).encode()),
        "declaration_headers_sha256": sha("\n\0\n".join(headers).encode()),
        "forbidden_counts": forbidden_counts(source),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-source", required=True)
    ap.add_argument("--library", action="append", default=[], required=True)
    ap.add_argument("--target", required=True)
    ap.add_argument("--audit-out", required=True)
    args = ap.parse_args()

    base_path = Path(args.base_source)
    source = base_path.read_text(encoding="utf-8")
    base_bytes = base_path.read_bytes()
    if "\r" in source:
        raise SystemExit("CR byte present in base source")
    base_struct = structural_snapshot(source)
    ledger: list[dict[str, Any]] = []

    for library_name in args.library:
        path = Path(library_name)
        payload = json.loads(path.read_text(encoding="utf-8"))
        before_sha = sha(source.encode())
        edits_applied: list[dict[str, Any]] = []
        for i, edit in enumerate(environment_edits(payload)):
            source, item = replace_environment(source, edit, f"{path.name}:env:{i}")
            edits_applied.append(item)
        for i, repair in enumerate(proof_repairs(payload)):
            source, items = replace_in_declaration(source, repair, f"{path.name}:repair:{i}")
            edits_applied.extend(items)
        now = structural_snapshot(source)
        if now["declaration_count"] != base_struct["declaration_count"]:
            raise SystemExit(f"{path.name}: declaration count drift")
        if now["declaration_sequence_sha256"] != base_struct["declaration_sequence_sha256"]:
            raise SystemExit(f"{path.name}: declaration sequence drift")
        if now["declaration_headers_sha256"] != base_struct["declaration_headers_sha256"]:
            raise SystemExit(f"{path.name}: declaration header/proposition drift")
        if now["forbidden_counts"] != base_struct["forbidden_counts"]:
            raise SystemExit(f"{path.name}: forbidden lexical ledger drift: {now['forbidden_counts']} vs {base_struct['forbidden_counts']}")
        ledger.append({
            "library": str(path),
            "schema": payload.get("schema"),
            "before_sha256": before_sha,
            "after_sha256": sha(source.encode()),
            "edits_applied": edits_applied,
            "structural_snapshot": now,
        })

    target = Path(args.target)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(source, encoding="utf-8", newline="\n")
    data = target.read_bytes()
    audit = {
        "schema": "fa-dynamic-library-sequence-audit-v1",
        "base": {
            "path": str(base_path),
            "sha256": sha(base_bytes),
            "bytes": len(base_bytes),
            "lines": len(base_bytes.decode("utf-8").splitlines()),
        },
        "libraries": ledger,
        "candidate": {
            "path": str(target),
            "sha256": sha(data),
            "bytes": len(data),
            "lines": len(data.decode("utf-8").splitlines()),
        },
        "base_structural_snapshot": base_struct,
        "final_structural_snapshot": structural_snapshot(source),
        "declaration_sequence_preserved": True,
        "declaration_headers_preserved": True,
        "forbidden_ledger_preserved": True,
    }
    Path(args.audit_out).write_text(json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit["candidate"], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
