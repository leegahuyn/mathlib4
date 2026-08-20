#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v25_rootcluster_batch.py <source> <outdir>")

source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
patch = Path("scripts/fa_v25_rootcluster_from_v23_filtered.patch")

before = source.read_bytes()
before_text = before.decode("utf-8")
base_sha = hashlib.sha256(before).hexdigest()
expected_base = "931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4"
assert base_sha == expected_base, (base_sha, expected_base)
if os.environ.get("BASE_SOURCE_SHA256"):
    assert base_sha == os.environ["BASE_SOURCE_SHA256"]

patch_bytes = patch.read_bytes()
patch_sha = hashlib.sha256(patch_bytes).hexdigest()
expected_patch = "e7e5be7395ff7fd556fd11ad02687184abf5cc0e6662a16c53e86a79607382f7"
assert patch_sha == expected_patch, (patch_sha, expected_patch)

proc = subprocess.run(
    ["patch", "-p1", "--batch", "--forward"],
    input=patch_bytes, capture_output=True
)
(out / "patch.stdout").write_bytes(proc.stdout)
(out / "patch.stderr").write_bytes(proc.stderr)
if proc.returncode != 0:
    raise SystemExit(
        f"patch failed {proc.returncode}:\n"
        + proc.stdout.decode(errors="replace")
        + "\n"
        + proc.stderr.decode(errors="replace")
    )

after = source.read_bytes()
after_text = after.decode("utf-8")
candidate = hashlib.sha256(after).hexdigest()
expected_candidate = "a0eadfaa8c92a4e1b2c5167c18c18463224e450434a8f1926c2227b1f1c84428"
assert candidate == expected_candidate, (candidate, expected_candidate)
assert len(after_text.splitlines()) == 61455

decl_re = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
assert decl_re.findall(before_text) == decl_re.findall(after_text), "declaration sequence changed"

th_re = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(theorem|lemma)\s+([^\s(:]+)"
)
def headers(s):
    starts = [m.start() for m in decl_re.finditer(s)]
    result = []
    for m in th_re.finditer(s):
        nxt = next((x for x in starts if x > m.start()), len(s))
        block = s[m.start():nxt]
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
    "schema": "fa-v25-full-inventory-rootcluster-strict-v1",
    "base_source_sha256": base_sha,
    "patch_sha256": patch_sha,
    "candidate_sha256": candidate,
    "candidate_bytes": len(after),
    "candidate_lines": len(after_text.splitlines()),
    "repairs": [
        "canonical_addgroup_graph_core",
        "canonical_addgroup_density_core",
        "canonical_addgroup_closed_tower_core",
        "canonical_addgroup_green_core",
        "dependent_index_whole_proposition_transport_3653",
        "petersson_zero_inner_zero_right_3659",
        "fubini_product_measurability_normal_form_3669",
        "translation_ae_orientation_3669",
        "reopened_reduced_chart_namespace_manifold_scope",
    ],
    "semantic_public_proposition_change": False,
    "theorem_lemma_headers_identical": True,
    "declaration_sequence_identical": True,
    "existing_declaration_relative_order_preserved": True,
    "forbidden_lexical_counts_preserved": True,
    "forbidden_lexical_counts_before_after": counts,
}
(out / "PATCH_AUDIT.json").write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
(out / "candidate.sha256").write_text(candidate + "\n")
print(json.dumps(audit, indent=2, sort_keys=True))
