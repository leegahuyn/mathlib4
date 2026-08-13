#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, tempfile

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v22_r2_small_wrapper.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)

before = source.read_bytes()
before_text = before.decode("utf-8")
base_sha = hashlib.sha256(before).hexdigest()
expected_base = os.environ.get("BASE_SOURCE_SHA256", "")
if expected_base:
    assert base_sha == expected_base, (base_sha, expected_base)
assert base_sha == "8f6cc2461efb07d09c07ecea6c6651f23ab3ccc2fa2989d6224afc7afe5167d0"

# Reuse the exact old v22 payload blob that already materialized 49ab on Actions.
base_script = Path("scripts/fa_v22_base49_old.py").read_text(encoding="utf-8")
old_expect = 'expected_candidate = "238957ca57b07de9b08fbf3d6195e0ce1d82ac21aed11f8abc7980dfec6b2736"'
new_expect = 'expected_candidate = "49ab1ab094cad1475302c962cfb8517788b855cec64b7fb95c6e656d5917331c"'
assert base_script.count(old_expect) == 1
base_script = base_script.replace(old_expect, new_expect, 1)
fd, tmp_name = tempfile.mkstemp(prefix="fa_v22_base49_", suffix=".py")
os.close(fd)
Path(tmp_name).write_text(base_script, encoding="utf-8")
proc = subprocess.run([sys.executable, tmp_name, str(source), str(out)], text=True, capture_output=True)
(out / "base49.stdout").write_text(proc.stdout, encoding="utf-8")
(out / "base49.stderr").write_text(proc.stderr, encoding="utf-8")
if proc.returncode != 0:
    raise SystemExit(f"base49 patcher failed: {proc.returncode}\n{proc.stdout}\n{proc.stderr}")
base49_sha = hashlib.sha256(source.read_bytes()).hexdigest()
assert base49_sha == "49ab1ab094cad1475302c962cfb8517788b855cec64b7fb95c6e656d5917331c", base49_sha

text = source.read_text(encoding="utf-8")
replacements = [
    (
        "joint_graph_core_instances",
        "namespace FixedPhaseJointGraphNormClosure\n\nopen Set Function Topology Filter",
        "namespace FixedPhaseJointGraphNormClosure\n\nattribute [local instance]\n  DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule\n  DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup\n\nopen Set Function Topology Filter",
    ),
    (
        "real_to_complex_compact_support",
        "      hcompact.comp_left rfl\n    exact hcomplex\n  tsupport_subset' := by\n    intro x hx\n    simp",
        "      hcompact.comp_left (g := fun r : \u211d \u21a6 (r : \u2102)) (by norm_num)\n    exact hcomplex\n  tsupport_subset' := by\n    intro x hx\n    exact Set.mem_univ x",
    ),
    (
        "complex_real_smooth_mul_funprop",
        "  simpa only [friedrichsAffineCommutatorKernel] using hConst.mul hScaled",
        "  fun_prop",
    ),
    (
        "sqrt_composition_normalization",
        "    simpa only [Function.comp_apply, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hSqrt",
        "    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hSqrt",
    ),
]
for label, old, new in replacements:
    count = text.count(old)
    assert count == 1, (label, count)
    text = text.replace(old, new, 1)
source.write_text(text, encoding="utf-8")

after = source.read_bytes()
after_text = after.decode("utf-8")
candidate_sha = hashlib.sha256(after).hexdigest()
expected_candidate = "6b73cb7d68157c861830dbefd30ae7bb0ddcc68b911fc89b49802836752bc965"
assert candidate_sha == expected_candidate, (candidate_sha, expected_candidate)
assert len(after_text.splitlines()) == 61375

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
    "schema": "fa-v22-r2-small-wrapper-strict-headers",
    "base_source_sha256": base_sha,
    "base49_source_sha256": base49_sha,
    "candidate_sha256": candidate_sha,
    "candidate_bytes": len(after),
    "candidate_lines": len(after_text.splitlines()),
    "reused_known_good_base49_blob": True,
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
