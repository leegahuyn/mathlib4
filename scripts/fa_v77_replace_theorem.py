#!/usr/bin/env python3
"""Generate trusted proof-body variants for one top-level theorem.

The script preserves the theorem statement exactly and replaces only the proof
body from `:= by` to the next top-level declaration.  It is intentionally
fail-closed: ambiguous declarations or bodies are rejected.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

DECL_START = re.compile(
    r"(?m)^(?P<indent>\s*)(?:(?:private|protected|noncomputable)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z0-9_\u0080-\uffff.]+)\b"
)

PROOFS = {
    "rfl": "by\n  rfl\n",
    "ext_rfl": "by\n  ext x\n  rfl\n",
    "funext_rfl": "by\n  funext x\n  rfl\n",
    "clm_ext_rfl": "by\n  apply ContinuousLinearMap.ext\n  intro x\n  rfl\n",
    "ext_simp": "by\n  ext x\n  simp\n",
    "simp": "by\n  simp\n",
    "aesop": "by\n  aesop\n",
    "simpa": "by\n  simpa\n",
    "exact_rfl": "by\n  exact rfl\n",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--theorem", required=True)
    ap.add_argument("--mode", choices=sorted(PROOFS), required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    ns = ap.parse_args()

    raw = ns.source.read_bytes()
    text = raw.decode("utf-8")
    declarations = list(DECL_START.finditer(text))
    matches = [m for m in declarations if m.group("name") == ns.theorem and m.group("kind") in {"theorem", "lemma"}]
    if len(matches) != 1:
        raise SystemExit(f"expected one target declaration, found {len(matches)}")
    m = matches[0]
    start = m.start()
    later = [d.start() for d in declarations if d.start() > start]
    end = min(later) if later else len(text)
    block = text[start:end]

    body_markers = list(re.finditer(r":=\s*by\b", block))
    if len(body_markers) != 1:
        raise SystemExit(f"target block must contain exactly one ':= by', got {len(body_markers)}")
    marker = body_markers[0]
    prefix = block[: marker.start()] + ":= "
    # Keep trailing blank lines/comments after the proof only when they begin
    # after a double newline followed by a top-level doc/comment.  Otherwise
    # the full body is replaced to avoid accidentally retaining old tactics.
    replacement = prefix + PROOFS[ns.mode] + "\n"
    candidate_text = text[:start] + replacement + text[end:]
    candidate = candidate_text.encode("utf-8")

    forbidden_added = {
        token: candidate_text.count(token) - text.count(token)
        for token in ["sorry", "admit", "native_decide", "Lean.ofReduceBool"]
    }
    if any(v > 0 for v in forbidden_added.values()):
        raise SystemExit(f"forbidden token introduced: {forbidden_added}")

    ns.output.parent.mkdir(parents=True, exist_ok=True)
    ns.output.write_bytes(candidate)
    evidence = {
        "schema": "fa-v77-theorem-body-variant-v1",
        "source_sha256": sha(raw),
        "candidate_sha256": sha(candidate),
        "candidate_bytes": len(candidate),
        "candidate_lines": len(candidate_text.splitlines()),
        "theorem": ns.theorem,
        "mode": ns.mode,
        "statement_prefix_sha256": sha(prefix.encode("utf-8")),
        "old_block_sha256": sha(block.encode("utf-8")),
        "new_block_sha256": sha(replacement.encode("utf-8")),
        "forbidden_token_delta": forbidden_added,
        "trust_bypass_added": False,
    }
    ns.evidence.parent.mkdir(parents=True, exist_ok=True)
    ns.evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
