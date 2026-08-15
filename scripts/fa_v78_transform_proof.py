#!/usr/bin/env python3
"""Transform one Lean theorem proof while preserving its statement and scope."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

BOUNDARY = re.compile(
    r"(?m)^(?:"
    r"(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example|axiom)\b"
    r"|namespace\b|section\b|end\b|open\b|attribute\b|variable\b|include\b|omit\b|noncomputable\s+section\b|local\s+(?:instance|attribute|notation)\b|scoped\b|#(?:check|print|eval|reduce|synth|lint)\b"
    r")"
)
TARGET_DECL = re.compile(
    r"(?m)^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(?P<name>[A-Za-z0-9_\u0080-\uffff.]+)\b"
)

TEMPLATES = {
    "rfl": "by\n  rfl\n",
    "exact_rfl": "by\n  exact rfl\n",
    "ext_rfl": "by\n  ext x\n  rfl\n",
    "ext_simp": "by\n  ext x\n  simp\n",
    "funext_rfl": "by\n  funext x\n  rfl\n",
    "clm_ext_rfl": "by\n  apply ContinuousLinearMap.ext\n  intro x\n  rfl\n",
    "exact_question": "by\n  exact?\n",
    "apply_question": "by\n  apply?\n",
    "simp_question": "by\n  simp?\n",
    "library_search": "by\n  library_search\n",
    "aesop": "by\n  aesop\n",
    "solve_by_elim": "by\n  solve_by_elim\n",
    "assumption": "by\n  assumption\n",
    "positivity": "by\n  positivity\n",
    "gcongr": "by\n  gcongr\n",
    "norm_num": "by\n  norm_num\n",
}
TRANSFORMS = {"original", "simp_only", "simpa_using_to_exact", "simpa_using_to_refine", "rw_to_simpa_only"}
MODES = sorted(set(TEMPLATES) | TRANSFORMS)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def find_block(text: str, theorem: str) -> tuple[int, int, int, int]:
    matches = [m for m in TARGET_DECL.finditer(text) if m.group("name") == theorem]
    if len(matches) != 1:
        raise SystemExit(f"expected one theorem {theorem}, found {len(matches)}")
    start = matches[0].start()
    boundary = BOUNDARY.search(text, matches[0].end())
    end = boundary.start() if boundary else len(text)
    block = text[start:end]
    markers = list(re.finditer(r":=\s*by\b", block))
    if len(markers) != 1:
        raise SystemExit(f"expected one ':= by' in target block, found {len(markers)}")
    marker = markers[0]
    marker_start = start + marker.start()
    body_start = start + marker.end()
    return start, end, marker_start, body_start


def transform_body(body: str, mode: str) -> str:
    if mode == "original":
        return body
    if mode == "simp_only":
        body = re.sub(r"\bsimpa\b(?!\s+only\b)", "simpa only", body)
        body = re.sub(r"\bsimp\b(?!\s+(?:only|\?))", "simp only", body)
        return body
    if mode in {"simpa_using_to_exact", "simpa_using_to_refine"}:
        keyword = "exact" if mode.endswith("exact") else "refine"
        pat = re.compile(r"(?m)^(?P<i>\s*)simpa(?:\s+only)?(?:\s*\[[^\n]*\])?\s+using\s+(?P<e>[^\n]+)$")
        result, count = pat.subn(lambda m: f"{m.group('i')}{keyword} {m.group('e')}", body)
        if count == 0:
            raise SystemExit(f"mode {mode} found no one-line simpa-using expression")
        return result
    if mode == "rw_to_simpa_only":
        result, count = re.subn(r"(?m)^(?P<i>\s*)rw\s*\[(?P<r>[^\n]+)\]\s*$", lambda m: f"{m.group('i')}simpa only [{m.group('r')}]", body)
        if count == 0:
            raise SystemExit("rw_to_simpa_only found no rw line")
        return result
    raise SystemExit(f"unknown transform mode {mode}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--theorem", required=True)
    ap.add_argument("--mode", choices=MODES, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    ns = ap.parse_args()

    raw = ns.source.read_bytes()
    text = raw.decode("utf-8")
    start, end, marker_start, body_start = find_block(text, ns.theorem)
    statement_prefix = text[start:marker_start] + ":= "
    old_body = text[body_start:end]
    if ns.mode in TEMPLATES:
        new_block = statement_prefix + TEMPLATES[ns.mode] + "\n"
    else:
        transformed = transform_body(old_body, ns.mode)
        new_block = statement_prefix + "by" + transformed
    candidate_text = text[:start] + new_block + text[end:]
    candidate = candidate_text.encode("utf-8")

    deltas = {token: candidate_text.count(token) - text.count(token) for token in ["sorry", "admit", "native_decide", "Lean.ofReduceBool"]}
    if any(v > 0 for v in deltas.values()):
        raise SystemExit(f"forbidden token introduced: {deltas}")

    ns.output.parent.mkdir(parents=True, exist_ok=True)
    ns.output.write_bytes(candidate)
    evidence = {
        "schema": "fa-v78-proof-transform-v1",
        "source_sha256": digest(raw),
        "candidate_sha256": digest(candidate),
        "candidate_bytes": len(candidate),
        "candidate_lines": len(candidate_text.splitlines()),
        "theorem": ns.theorem,
        "mode": ns.mode,
        "statement_prefix_sha256": digest(statement_prefix.encode()),
        "old_body_sha256": digest(old_body.encode()),
        "new_block_sha256": digest(new_block.encode()),
        "forbidden_token_delta": deltas,
        "trust_bypass_added": False,
    }
    ns.evidence.parent.mkdir(parents=True, exist_ok=True)
    ns.evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
