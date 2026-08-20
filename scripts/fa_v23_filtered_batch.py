#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v23_filtered_batch.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
patch = Path("scripts/fa_v23_filtered.patch")

before = source.read_bytes()
before_text = before.decode("utf-8")
base_sha = hashlib.sha256(before).hexdigest()
assert base_sha == "6b73cb7d68157c861830dbefd30ae7bb0ddcc68b911fc89b49802836752bc965", (base_sha, "6b73cb7d68157c861830dbefd30ae7bb0ddcc68b911fc89b49802836752bc965")

patch_bytes = patch.read_bytes()
patch_sha = hashlib.sha256(patch_bytes).hexdigest()
assert patch_sha == "80719e2c5910d39676eae9a5119a32017fe04b4ac13b232cc321051d043df147", (patch_sha, "80719e2c5910d39676eae9a5119a32017fe04b4ac13b232cc321051d043df147")

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
assert candidate_sha == "931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4", (candidate_sha, "931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4")

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

repairs = [
    "3646_strongPrincipal_pointwise_sub_coercion",
    "3650_strongSchrodinger_pointwise_sub_coercion",
    "3652_successor_coordinate_normalization",
    "3653_predecessor_explicit_equality_transport",
    "3659_forcing_zero_explicit_l2_zero",
    "3660_pairing_separation_ambient_vector",
    "3669_uncurry_measurable_normalization",
    "3669_prod_swap_right_integral_normalization",
    "3669_holder_ae_rewrite_order",
    "3669_final_uncurry_target_normalization",
    "3681_affine_commutator_contdiff_explicit",
    "3687_norm_square_real_part_normalization",
    "3690_l2_equiv_base_transport",
    "3690_submodule_sub_mem",
    "3690_joint_graph_tendsto_normalization",
    "3729_maximal_graph_core_test_normalization",
    "3736_partial_eigenspace_subtype_transport",
    "3740_star_im_normalization",
    "3741_starRingEnd_orthogonality",
    "3746_eigen_graph_and_self_inner_normalization",
    "3747_manifold_contdiff_scoped_notation",
    "3751_literal_stage_finite_unfold",
    "p5_discriminant_weightcore_namespace"
]
audit = {
    "schema": "fa-v23-filtered-live-roots-strict",
    "base_source_sha256": base_sha,
    "patch_sha256": patch_sha,
    "candidate_sha256": candidate_sha,
    "candidate_bytes": len(after),
    "candidate_lines": len(after_text.splitlines()),
    "repairs": repairs,
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
