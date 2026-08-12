#!/usr/bin/env python3
import base64, hashlib, json, os, re, subprocess, sys, zlib
from pathlib import Path

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v21_cumulative_batch.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
expected_base = os.environ.get("BASE_SOURCE_SHA256", "")
expected_candidate = "8f6cc2461efb07d09c07ecea6c6651f23ab3ccc2fa2989d6224afc7afe5167d0"
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
before_decls = decl_re.findall(before_text)
after_decls = decl_re.findall(after_text)
assert before_decls == after_decls, "declaration sequence changed"

def theorem_headers(text):
    start_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
    matches = list(start_re.finditer(text))
    all_decl_matches = list(decl_re.finditer(text))
    all_starts = [m.start() for m in all_decl_matches]
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

before_headers = theorem_headers(before_text)
after_headers = theorem_headers(after_text)
assert before_headers == after_headers, "theorem/lemma proposition header changed"

forbidden = ["sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool"]
counts = {}
for word in forbidden:
    pat = r"(?<![A-Za-z0-9_])" + re.escape(word) + r"(?![A-Za-z0-9_])"
    counts[word] = [len(re.findall(pat, before_text)), len(re.findall(pat, after_text))]
assert all(a == b for a, b in counts.values()), counts

repairs = [
    "weight_core_namespace_open", "quotient_potential_explicit_change",
    "strong_principal_definition_sub_explicit", "strong_schrodinger_definition_sub_explicit",
    "core_forcing_zero_simp", "pairing_separation_sub_explicit",
    "full_plane_pair_smul_mul", "remove_stale_lsmul_simp",
    "real_test_compact_support", "joint_graph_lower_coord_normalization",
    "joint_graph_inner_scalar_explicit", "cauchy_sub_explicit",
    "dense_range_explicit", "operator_norm_args_explicit",
    "linear_map_norm_args_explicit", "partial_eigenspace_domain_membership",
    "p5_namespace_opens", "literal_partition_index_typo",
    "ambient_l2_noncomputable", "discriminant_hard_classical",
    "discriminant_tail_classical", "discriminant_hard_measurable_bridge",
    "discriminant_tail_measurable_bridge"
]
audit = {
    "schema": "fa-v21-cumulative-ascii-patch-strict-headers",
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

# trigger bridge only: v22-run-1
