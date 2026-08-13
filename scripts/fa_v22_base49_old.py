#!/usr/bin/env python3
import base64, hashlib, json, os, re, subprocess, sys, zlib
from pathlib import Path

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v22_cumulative_batch.py <source> <outdir>")
source = Path(sys.argv[1]); out = Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
expected_base = os.environ.get("BASE_SOURCE_SHA256", "")
expected_candidate = "238957ca57b07de9b08fbf3d6195e0ce1d82ac21aed11f8abc7980dfec6b2736"
before = source.read_bytes(); base_sha = hashlib.sha256(before).hexdigest()
if expected_base:
    assert base_sha == expected_base, (base_sha, expected_base)
before_text = before.decode("utf-8")
PATCH_B64 = "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"
assert PATCH_B64.isascii()
patch_text = zlib.decompress(base64.b64decode(PATCH_B64)).decode("utf-8")
proc = subprocess.run(["patch","-p1","--batch","--forward"],
    input=patch_text, text=True, capture_output=True)
(out/"patch.stdout").write_text(proc.stdout); (out/"patch.stderr").write_text(proc.stderr)
if proc.returncode != 0:
    raise SystemExit(f"patch failed: {proc.returncode}\n{proc.stdout}\n{proc.stderr}")
after = source.read_bytes(); after_text = after.decode("utf-8")
candidate_sha = hashlib.sha256(after).hexdigest()
assert candidate_sha == expected_candidate, (candidate_sha, expected_candidate)

decl_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
assert decl_re.findall(before_text) == decl_re.findall(after_text), "declaration sequence changed"

def theorem_headers(text):
    start_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
    allm = list(decl_re.finditer(text)); starts = [m.start() for m in allm]; out = []
    for m in start_re.finditer(text):
        nxt = next((p for p in starts if p > m.start()), len(text))
        block = text[m.start():nxt]
        cut = block.find(":= by")
        if cut < 0: cut = block.find(":=")
        header = block if cut < 0 else block[:cut]
        out.append((m.group(2), re.sub(r"\s+", " ", header).strip()))
    return out
assert theorem_headers(before_text) == theorem_headers(after_text), "theorem/lemma header changed"

forbidden = ["sorry","admit","axiom","unsafe","native_decide","Lean.ofReduceBool"]
counts = {}
for word in forbidden:
    pat = r"(?<![A-Za-z0-9_])" + re.escape(word) + r"(?![A-Za-z0-9_])"
    counts[word] = [len(re.findall(pat,before_text)),len(re.findall(pat,after_text))]
assert all(a == b for a,b in counts.values()), counts

repairs = ['actual_scalar_graph_core_instances', 'typed_lsmul', 'real_full_plane_test_compact_support', 'commutator_kernel_contdiff_fun_prop', 'convolution_real_scalar', 'joint_graph_core_instances', 'sqrt_comp_def', 'joint_hybase_trans', 'dense_inner_scalar', 'minimal_dense_range', 'minimal_graph_projection', 'maximal_graph_projection', 'inner_conj_orientation', 'maximal_core_target', 'closure_adjoint_explicit']
audit = {
    "schema":"fa-v22-cumulative-ascii-strict",
    "base_source_sha256":base_sha,
    "candidate_sha256":candidate_sha,
    "candidate_bytes":len(after),
    "candidate_lines":len(after_text.splitlines()),
    "patch_payload_ascii":True,
    "patch_payload_base64_chars":len(PATCH_B64),
    "repairs":repairs,
    "semantic_public_proposition_change":False,
    "theorem_lemma_headers_identical":True,
    "declaration_sequence_identical":True,
    "existing_declaration_relative_order_preserved":True,
    "forbidden_lexical_counts_preserved":True,
    "forbidden_lexical_counts_before_after":counts
}
(out/"PATCH_AUDIT.json").write_text(json.dumps(audit,indent=2,sort_keys=True)+"\n")
(out/"candidate.sha256").write_text(candidate_sha+"\n")
print(json.dumps(audit,indent=2,sort_keys=True))
