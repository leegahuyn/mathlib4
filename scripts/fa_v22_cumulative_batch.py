#!/usr/bin/env python3
import base64, hashlib, json, os, re, subprocess, sys, zlib
from pathlib import Path

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v22_cumulative_batch.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
expected_base = os.environ.get("BASE_SOURCE_SHA256", "")
expected_candidate = "6b73cb7d68157c861830dbefd30ae7bb0ddcc68b911fc89b49802836752bc965"
before = source.read_bytes()
base_sha = hashlib.sha256(before).hexdigest()
if expected_base:
    assert base_sha == expected_base, (base_sha, expected_base)
before_text = before.decode("utf-8")
PATCH_B64 = "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"
assert PATCH_B64.isascii()
patch_text = zlib.decompress(base64.b64decode(PATCH_B64)).decode("utf-8")
proc = subprocess.run(["patch", "-p1", "--batch", "--forward"], input=patch_text, text=True, capture_output=True)
(out / "patch.stdout").write_text(proc.stdout)
(out / "patch.stderr").write_text(proc.stderr)
if proc.returncode != 0:
    raise SystemExit("patch failed: %s\n%s\n%s" % (proc.returncode, proc.stdout, proc.stderr))
after = source.read_bytes()
after_text = after.decode("utf-8")
candidate_sha = hashlib.sha256(after).hexdigest()
assert candidate_sha == expected_candidate, (candidate_sha, expected_candidate)

decl_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
assert decl_re.findall(before_text) == decl_re.findall(after_text), "declaration sequence changed"

def theorem_headers(text):
    start_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
    matches = list(start_re.finditer(text))
    all_starts = [m.start() for m in decl_re.finditer(text)]
    result = []
    for m in matches:
        nxt = next((p for p in all_starts if p > m.start()), len(text))
        block = text[m.start():nxt]
        cut = block.find(":= by")
        if cut < 0:
            cut = block.find(":=")
        header = block if cut < 0 else block[:cut]
        result.append((m.group(2), re.sub(r"\s+", " ", header).strip()))
    return result
assert theorem_headers(before_text) == theorem_headers(after_text), "theorem/lemma proposition header changed"

forbidden = ["sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool"]
counts = {}
for word in forbidden:
    pat = r"(?<![A-Za-z0-9_])" + re.escape(word) + r"(?![A-Za-z0-9_])"
    counts[word] = [len(re.findall(pat, before_text)), len(re.findall(pat, after_text))]
assert all(a == b for a, b in counts.values()), counts

repairs = [
  "actual_scalar_graph_core_instances", "strong_principal_subtraction",
  "strong_schrodinger_subtraction", "typed_lsmul_norm", "real_convolution_scalar",
  "dense_inner_right_scalar", "dense_range_target", "graph_coordinate_target",
  "adjoint_pair_target", "inner_conj_orientation", "core_range_target",
  "triple_adjoint_closure_target", "joint_graph_core_instances",
  "real_to_complex_compact_support", "complex_real_smooth_mul_funprop",
  "sqrt_composition_normalization"
]
audit = {
  "schema": "fa-v22-cumulative-ascii-patch-strict-headers-r2",
  "base_source_sha256": base_sha,
  "candidate_sha256": candidate_sha,
  "candidate_bytes": len(after),
  "candidate_lines": len(after_text.splitlines()),
  "patch_payload_ascii": True,
  "patch_payload_base64_chars": len(PATCH_B64),
  "repairs": repairs,
  "semantic_public_proposition_change": False,
  "theorem_lemma_headers_identical": True,
  "declaration_sequence_identical": True,
  "existing_declaration_relative_order_preserved": True,
  "forbidden_lexical_counts_preserved": True,
  "forbidden_lexical_counts_before_after": counts
}
(out / "PATCH_AUDIT.json").write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
(out / "candidate.sha256").write_text(candidate_sha + "\n")
print(json.dumps(audit, indent=2, sort_keys=True))
