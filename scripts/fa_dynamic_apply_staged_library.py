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


def sha_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def declarations(text: str) -> list[dict]:
    ms = list(DECL_RE.finditer(text))
    out = []
    for i, m in enumerate(ms):
        out.append({
            "index": i,
            "name": m.group("name"),
            "start": m.start(),
            "end": ms[i + 1].start() if i + 1 < len(ms) else len(text),
        })
    return out


def theorem_header(text: str, decl: dict) -> str:
    segment = text[decl["start"]:decl["end"]]
    k = segment.find(":= by")
    if k < 0:
        raise RuntimeError(
            f"repaired declaration {decl['index']} {decl['name']} has no := by terminator"
        )
    return segment[: k + len(":= by")]


def sequence_hash(text: str) -> tuple[list[str], str]:
    names = [d["name"] for d in declarations(text)]
    return names, sha_bytes("\n".join(names).encode())


def forbidden_counts(text: str) -> dict[str, int]:
    return {x: text.count(x) for x in FORBIDDEN}


def iter_environment_replacements(lib: dict):
    if isinstance(lib.get("environment_replacement"), dict):
        yield lib["environment_replacement"].get("id", "environment_replacement"), lib["environment_replacement"]
    for item in lib.get("environment_replacements", []):
        if "replacement" in item:
            yield item.get("id", "environment_replacement"), item["replacement"]
        else:
            yield item.get("id", "environment_replacement"), item


def flatten_repairs(lib: dict) -> list[dict]:
    out = []
    for root in lib.get("repairs", []):
        replacements = root.get("replacements")
        if replacements is None and "old_fragment" in root and "new_fragment" in root:
            replacements = [root]
        for r in replacements or []:
            out.append({
                "declaration_index": int(root["declaration_index"]),
                "declaration_name": root["declaration_name"],
                "staged_header_sha256": root.get("header_sha256"),
                "old_fragment": r["old_fragment"],
                "new_fragment": r["new_fragment"],
                "replacement_id": r.get("id") or root.get("id"),
            })
    for edit in lib.get("edits", []):
        if not all(k in edit for k in ("declaration_index", "declaration_name", "old_fragment", "new_fragment")):
            continue
        out.append({
            "declaration_index": int(edit["declaration_index"]),
            "declaration_name": edit["declaration_name"],
            "staged_header_sha256": edit.get("header_sha256"),
            "old_fragment": edit["old_fragment"],
            "new_fragment": edit["new_fragment"],
            "replacement_id": edit.get("id"),
        })
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-source", required=True)
    ap.add_argument("--library", required=True)
    ap.add_argument("--target", required=True)
    ap.add_argument("--audit-out", required=True)
    ap.add_argument("--environment-id", action="append", default=[])
    ap.add_argument("--no-environment", action="store_true")
    args = ap.parse_args()

    base_path = Path(args.base_source)
    lib_path = Path(args.library)
    target_path = Path(args.target)
    base_bytes = base_path.read_bytes()
    if b"\r" in base_bytes:
        raise RuntimeError("base source must be LF-only")
    text = base_bytes.decode("utf-8")
    lib = json.loads(lib_path.read_text(encoding="utf-8"))
    names0, seq0 = sequence_hash(text)
    forb0 = forbidden_counts(text)

    environment_audit = []
    requested_env = set(args.environment_id)
    if not args.no_environment:
        for env_id, rep in iter_environment_replacements(lib):
            if requested_env and env_id not in requested_env:
                continue
            old = rep["old_fragment"]
            new = rep["new_fragment"]
            if text.count(old) != 1:
                raise RuntimeError(f"environment {env_id}: old fragment count={text.count(old)}")
            if any(token in new and token not in old for token in FORBIDDEN):
                raise RuntimeError(f"environment {env_id}: forbidden token growth")
            before_names, before_seq = sequence_hash(text)
            text = text.replace(old, new, 1)
            after_names, after_seq = sequence_hash(text)
            if before_names != after_names or before_seq != after_seq:
                raise RuntimeError(f"environment {env_id}: declaration sequence changed")
            environment_audit.append({
                "id": env_id,
                "staged_old_sha256": rep.get("old_sha256"),
                "staged_new_sha256": rep.get("new_sha256"),
                "observed_old_sha256": sha_bytes(old.encode()),
                "observed_new_sha256": sha_bytes(new.encode()),
                "declaration_sequence_preserved": True,
            })
    if requested_env and {x["id"] for x in environment_audit} != requested_env:
        missing = requested_env - {x["id"] for x in environment_audit}
        raise RuntimeError("requested environment ids missing: " + repr(sorted(missing)))

    applied = []
    for edit in flatten_repairs(lib):
        ds = declarations(text)
        idx = edit["declaration_index"]
        if idx >= len(ds):
            raise RuntimeError(f"repair index out of range: {idx}")
        d = ds[idx]
        if d["name"] != edit["declaration_name"]:
            raise RuntimeError(
                f"repair declaration identity drift at {idx}: {d['name']} != {edit['declaration_name']}"
            )
        header_before = theorem_header(text, d)
        current_header_sha = sha_bytes(header_before.encode())
        old = edit["old_fragment"]
        new = edit["new_fragment"]
        body = text[d["start"]:d["end"]]
        if body.count(old) != 1:
            raise RuntimeError(f"repair {idx}: old fragment count in declaration={body.count(old)}")
        if text.count(old) != 1:
            raise RuntimeError(f"repair {idx}: old fragment global count={text.count(old)}")
        if any(token in new and token not in old for token in FORBIDDEN):
            raise RuntimeError(f"repair {idx}: forbidden token introduced")
        at = d["start"] + body.index(old)
        text = text[:at] + new + text[at + len(old):]
        ds_after = declarations(text)
        da = ds_after[idx]
        if da["name"] != d["name"]:
            raise RuntimeError(f"repair {idx}: declaration name changed")
        header_after = theorem_header(text, da)
        if header_after != header_before:
            raise RuntimeError(f"repair {idx}: theorem proposition/header changed")
        applied.append({
            "declaration_index": idx,
            "declaration_name": d["name"],
            "replacement_id": edit["replacement_id"],
            "current_header_sha256": current_header_sha,
            "staged_header_sha256": edit["staged_header_sha256"],
            "staged_header_hash_matches_current_scheme": edit["staged_header_sha256"] in (None, current_header_sha),
            "old_fragment_sha256": sha_bytes(old.encode()),
            "new_fragment_sha256": sha_bytes(new.encode()),
            "header_preserved": True,
        })

    if not text.endswith("\n"):
        text += "\n"
    names1, seq1 = sequence_hash(text)
    if names1 != names0 or seq1 != seq0:
        raise RuntimeError("final declaration sequence changed")
    forb1 = forbidden_counts(text)
    if forb1 != forb0:
        raise RuntimeError(f"forbidden lexical counts changed: {forb0} -> {forb1}")

    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(text, encoding="utf-8", newline="\n")
    data = target_path.read_bytes()
    audit = {
        "schema": "fa-staged-library-application-audit-v1",
        "library_path": str(lib_path),
        "library_schema": lib.get("schema"),
        "base_source_sha256": sha_bytes(base_bytes),
        "candidate_source_sha256": sha_bytes(data),
        "candidate_bytes": len(data),
        "candidate_lines": len(text.splitlines()),
        "declaration_count": len(names1),
        "declaration_sequence_sha256": seq1,
        "declaration_sequence_preserved": True,
        "public_declaration_headers_preserved": True,
        "forbidden_counts_before": forb0,
        "forbidden_counts_after": forb1,
        "environment_replacements_applied": environment_audit,
        "proof_replacements_applied": applied,
    }
    Path(args.audit_out).write_text(
        json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
