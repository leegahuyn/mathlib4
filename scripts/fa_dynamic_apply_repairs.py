#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s(:]+)"
)
FORBIDDEN = ("sorry", "admit", "native_decide", "Lean.ofReduceBool", "unsafe")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def header_for(text: str, start: int, end: int) -> str:
    segment = text[start:end]
    marker = segment.find(":= by")
    if marker < 0:
        raise RuntimeError("repaired declaration has no := by header terminator")
    marker += len(":= by")
    return segment[:marker]


def declarations(text: str):
    matches = list(DECL_RE.finditer(text))
    result = []
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        result.append({
            "index": i,
            "name": m.group("name"),
            "start": m.start(),
            "end": end,
        })
    return result


def executable_forbidden_counts(text: str) -> dict[str, int]:
    # The attested d0a3 baseline already passed the strict executable audit.
    # Rejecting lexical-count growth is deliberately conservative: proof repairs
    # cannot smuggle a newly forbidden mechanism through comments or local text.
    return {token: text.count(token) for token in FORBIDDEN}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-source", required=True)
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--target", required=True)
    ap.add_argument("--audit-out", required=True)
    args = ap.parse_args()

    base_path = Path(args.base_source)
    target_path = Path(args.target)
    manifest = json.loads(Path(args.manifest).read_text(encoding="utf-8"))
    base_bytes = base_path.read_bytes()
    base = base_bytes.decode("utf-8")
    if sha(base_bytes) != manifest["base_source_sha256"]:
        raise RuntimeError("base source SHA256 drift")
    if b"\r" in base_bytes:
        raise RuntimeError("base source must be LF-only")

    before_decls = declarations(base)
    before_names = [d["name"] for d in before_decls]
    before_sequence_sha = sha("\n".join(before_names).encode())
    if before_sequence_sha != manifest["base_declaration_sequence_sha256"]:
        raise RuntimeError("base declaration sequence drift")
    before_forbidden = executable_forbidden_counts(base)

    text = base
    applied = []
    for repair in manifest["repairs"]:
        current = declarations(text)
        idx = int(repair["declaration_index"])
        if idx >= len(current):
            raise RuntimeError(f"repair index out of range: {idx}")
        decl = current[idx]
        if decl["name"] != repair["declaration_name"]:
            raise RuntimeError(
                f"declaration identity drift at {idx}: {decl['name']} != {repair['declaration_name']}"
            )
        header = header_for(text, decl["start"], decl["end"])
        header_sha = sha(header.encode())
        if header_sha != repair["header_sha256"]:
            raise RuntimeError(f"public declaration header drift before repair {idx}")

        old = repair["old_fragment"]
        new = repair["new_fragment"]
        if any(token in new and token not in old for token in FORBIDDEN):
            raise RuntimeError(f"forbidden token introduced by repair {idx}")
        body = text[decl["start"]:decl["end"]]
        if body.count(old) != 1 or text.count(old) != 1:
            raise RuntimeError(f"exact old fragment identity failed for repair {idx}")
        absolute = decl["start"] + body.index(old)
        text = text[:absolute] + new + text[absolute + len(old):]

        after_current = declarations(text)
        after_decl = after_current[idx]
        if after_decl["name"] != repair["declaration_name"]:
            raise RuntimeError(f"declaration name changed by repair {idx}")
        after_header = header_for(text, after_decl["start"], after_decl["end"])
        if after_header != header:
            raise RuntimeError(f"public declaration proposition/header changed by repair {idx}")
        applied.append({
            "declaration_index": idx,
            "declaration_name": repair["declaration_name"],
            "header_sha256": header_sha,
            "old_fragment_sha256": sha(old.encode()),
            "new_fragment_sha256": sha(new.encode()),
        })

    if not text.endswith("\n"):
        text += "\n"
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(text, encoding="utf-8", newline="\n")
    data = target_path.read_bytes()
    after_decls = declarations(text)
    after_names = [d["name"] for d in after_decls]
    after_sequence_sha = sha("\n".join(after_names).encode())
    if after_names != before_names or after_sequence_sha != before_sequence_sha:
        raise RuntimeError("declaration sequence changed")
    after_forbidden = executable_forbidden_counts(text)
    if after_forbidden != before_forbidden:
        raise RuntimeError(
            f"forbidden lexical counts changed: {before_forbidden} -> {after_forbidden}"
        )

    audit = {
        "schema": "fa-dynamic-repair-audit-v2",
        "base_source_sha256": sha(base_bytes),
        "candidate_source_sha256": sha(data),
        "candidate_bytes": len(data),
        "candidate_lines": len(text.splitlines()),
        "declaration_count": len(after_decls),
        "declaration_sequence_sha256": after_sequence_sha,
        "public_declaration_headers_preserved": True,
        "declaration_sequence_preserved": True,
        "forbidden_counts_before": before_forbidden,
        "forbidden_counts_after": after_forbidden,
        "repairs_applied": applied,
    }
    Path(args.audit_out).write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
