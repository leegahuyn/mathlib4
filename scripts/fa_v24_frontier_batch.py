#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v24_frontier_batch.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
patch = Path("scripts/fa_v24_frontier_from_filtered.patch")

before = source.read_bytes()
before_text = before.decode("utf-8")
base_sha = hashlib.sha256(before).hexdigest()
expected_base = "931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4"
assert base_sha == expected_base, (base_sha, expected_base)

patch_bytes = patch.read_bytes()
patch_sha = hashlib.sha256(patch_bytes).hexdigest()
expected_patch = "bebc6cc76fcf669f6a10eea5f261ce5999e7090901e79b6435175e21f9c126f2"
assert patch_sha == expected_patch, (patch_sha, expected_patch)

proc = subprocess.run(
    ["patch", "-p1", "--batch", "--forward", "-i", str(patch.resolve())],
    text=True, capture_output=True)
(out / "patch.stdout").write_text(proc.stdout, encoding="utf-8")
(out / "patch.stderr").write_text(proc.stderr, encoding="utf-8")
if proc.returncode != 0:
    raise SystemExit(f"patch failed: {proc.returncode}\n{proc.stdout}\n{proc.stderr}")

after = source.read_bytes()
after_text = after.decode("utf-8")
candidate_sha = hashlib.sha256(after).hexdigest()
expected_candidate = "24127dcd7b1f0e70e132b195249dbd54dcc5c3750b44f349dbc1130161ca7570"
assert candidate_sha == expected_candidate, (candidate_sha, expected_candidate)
assert len(after_text.splitlines()) == 61520

decl_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
assert decl_re.findall(before_text) == decl_re.findall(after_text), "declaration sequence changed"

def theorem_headers(text):
    start_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
    starts = [m.start() for m in decl_re.finditer(text)]
    result = []
    for m in start_re.finditer(text):
        nxt = next((p for p in starts if p > m.start()), len(text))
        block = text[m.start():nxt]
        cut = block.find(":= by")
        if cut < 0:
            cut = block.find(":=")
        header = block if cut < 0 else block[:cut]
        result.append((m.group(2), re.sub(r"\s+", " ", header).strip()))
    return result

assert theorem_headers(before_text) == theorem_headers(after_text), "theorem/lemma header changed"

forbidden = ["sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool", "set_option"]
counts = {}
for word in forbidden:
    pat = r"(?<![A-Za-z0-9_])" + re.escape(word) + r"(?![A-Za-z0-9_])"
    counts[word] = [len(re.findall(pat, before_text)), len(re.findall(pat, after_text))]
assert all(a == b for a, b in counts.values()), counts

audit = {
    "schema": "fa-v24-layered-coercion-frontier-strict",
    "base_source_sha256": base_sha,
    "patch_sha256": patch_sha,
    "candidate_sha256": candidate_sha,
    "candidate_bytes": len(after),
    "candidate_lines": len(after_text.splitlines()),
    "repairs": [
        "3646_strongPrincipal_layered_core_to_smooth_sub_coercion",
        "3650_strongSchrodinger_layered_core_to_smooth_sub_and_smul_coercion",
    ],
    "semantic_public_proposition_change": False,
    "theorem_lemma_headers_identical": True,
    "declaration_sequence_identical": True,
    "existing_declaration_relative_order_preserved": True,
    "forbidden_lexical_counts_preserved": True,
    "forbidden_lexical_counts_before_after": counts,
}
(out / "PATCH_AUDIT.json").write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
(out / "candidate.sha256").write_text(candidate_sha + "\n", encoding="utf-8")
print(json.dumps(audit, indent=2, sort_keys=True))
