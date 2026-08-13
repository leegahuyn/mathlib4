#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v26_transport_batch.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
patch = Path("scripts/fa_v26_transport_from_v25.patch")

before = source.read_bytes(); before_text = before.decode("utf-8")
base_sha = hashlib.sha256(before).hexdigest()
expected_base = "ceaa3d57513652edda592c4b22519640d4a233119f6720ff32fb07d45dcad219"
assert base_sha == expected_base, (base_sha, expected_base)
expected_env = os.environ.get("BASE_SOURCE_SHA256")
if expected_env:
    assert base_sha == expected_env, (base_sha, expected_env)
patch_bytes = patch.read_bytes(); patch_sha = hashlib.sha256(patch_bytes).hexdigest()
expected_patch = "3c6df016d9580378a346917622dbd9e40d4e7107e5bbd6e196038e5fc676a26a"
assert patch_sha == expected_patch, (patch_sha, expected_patch)
proc = subprocess.run(["patch", "-p1", "--batch", "--forward"], input=patch_bytes, capture_output=True)
(out / "patch.stdout").write_bytes(proc.stdout)
(out / "patch.stderr").write_bytes(proc.stderr)
if proc.returncode != 0:
    raise SystemExit(f"patch failed {proc.returncode}:\n{proc.stdout.decode(errors='replace')}\n{proc.stderr.decode(errors='replace')}")
after = source.read_bytes(); after_text = after.decode("utf-8")
candidate = hashlib.sha256(after).hexdigest()
expected_candidate = "b039ccaf4d7754dd943357ff6a97d97dd8d09e871a920f6c706733c481621eb9"
assert candidate == expected_candidate, (candidate, expected_candidate)
assert len(after_text.splitlines()) == 61450

decl_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
assert decl_re.findall(before_text) == decl_re.findall(after_text), "declaration sequence changed"

def headers(text):
    tr = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
    starts = [m.start() for m in decl_re.finditer(text)]
    result = []
    for m in tr.finditer(text):
        nxt = next((p for p in starts if p > m.start()), len(text))
        block = text[m.start():nxt]
        cut = block.find(":= by")
        if cut < 0:
            cut = block.find(":=")
        result.append((m.group(2), re.sub(r"\s+", " ", block if cut < 0 else block[:cut]).strip()))
    return result
assert headers(before_text) == headers(after_text), "theorem/lemma proposition header changed"

forbidden = ["sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool", "set_option"]
counts = {}
for word in forbidden:
    pat = r"(?<![A-Za-z0-9_])" + re.escape(word) + r"(?![A-Za-z0-9_])"
    counts[word] = [len(re.findall(pat, before_text)), len(re.findall(pat, after_text))]
assert all(a == b for a, b in counts.values()), counts

audit = {
    "schema": "fa-v26-dependent-index-transport-strict-v1",
    "base_source_sha256": base_sha,
    "patch_sha256": patch_sha,
    "candidate_sha256": candidate,
    "candidate_bytes": len(after),
    "candidate_lines": len(after_text.splitlines()),
    "repairs": ["energyForm_predecessor_dependent_index_transport_via_Eq_subst"],
    "semantic_public_proposition_change": False,
    "theorem_lemma_headers_identical": True,
    "declaration_sequence_identical": True,
    "existing_declaration_relative_order_preserved": True,
    "forbidden_lexical_counts_preserved": True,
    "forbidden_lexical_counts_before_after": counts,
}
(out / "PATCH_AUDIT.json").write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
(out / "candidate.sha256").write_text(candidate + "\n", encoding="utf-8")
print(json.dumps(audit, indent=2, sort_keys=True))
