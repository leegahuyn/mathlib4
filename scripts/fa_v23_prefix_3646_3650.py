#!/usr/bin/env python3
import hashlib, json, re, sys
from pathlib import Path

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v23_prefix_3646_3650.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
before = source.read_bytes()
before_text = before.decode("utf-8")
base_sha = hashlib.sha256(before).hexdigest()
expected_base = "6b73cb7d68157c861830dbefd30ae7bb0ddcc68b911fc89b49802836752bc965"
assert base_sha == expected_base, (base_sha, expected_base)

CORE = "Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore"
anchor1 = "  rw [strongPrincipalCore_apply]\n  change\n"
insert1 = (
    "  rw [strongPrincipalCore_apply]\n"
    "  change\n"
    "    (((Sub.sub\n"
    "        (Sub.sub u\n"
    "          (" + CORE + ".lowerFromSucc n\n"
    "            (" + CORE + ".raise n u)))\n"
    "        (" + CORE + ".raiseFromPred n\n"
    "          (" + CORE + ".lower n u)) : " + CORE + " n) :\n"
    "      SmoothQuotientCompactFunction) z) = _\n"
    "  change\n"
)
anchor2 = "  rw [strongSchrodingerCore_apply]\n  change\n"
insert2 = (
    "  rw [strongSchrodingerCore_apply]\n"
    "  change\n"
    "    (((Sub.sub (strongPrincipalCore n u)\n"
    "        (SMul.smul (t : Complex) (potentialMultiplicationCore n u)) : " + CORE + " n) :\n"
    "      SmoothQuotientCompactFunction) z) = _\n"
    "  change\n"
)
assert insert1.isascii() and insert2.isascii()
assert before_text.count(anchor1) == 1, before_text.count(anchor1)
text = before_text.replace(anchor1, insert1, 1)
assert text.count(anchor2) == 1, text.count(anchor2)
text = text.replace(anchor2, insert2, 1)
source.write_text(text, encoding="utf-8")
after = source.read_bytes()
after_text = after.decode("utf-8")
candidate = hashlib.sha256(after).hexdigest()
expected_candidate = "7d00ee14bea440fb721d2a95133c4dc1506d2439aa58fe44e1d092ebdfab4c16"
assert candidate == expected_candidate, (candidate, expected_candidate)
assert len(after_text.splitlines()) == 61387

decl_re = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
assert decl_re.findall(before_text) == decl_re.findall(after_text), "declaration sequence changed"

def headers(text):
    tr = re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
    starts = [m.start() for m in decl_re.finditer(text)]
    result = []
    for m in tr.finditer(text):
        nxt = next((x for x in starts if x > m.start()), len(text))
        block = text[m.start():nxt]
        cut = block.find(":= by")
        if cut < 0:
            cut = block.find(":=")
        header = block if cut < 0 else block[:cut]
        result.append((m.group(2), re.sub(r"\s+", " ", header).strip()))
    return result
assert headers(before_text) == headers(after_text), "theorem/lemma proposition header changed"

forbidden = ["sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool"]
counts = {}
for word in forbidden:
    pat = r"(?<![A-Za-z0-9_])" + re.escape(word) + r"(?![A-Za-z0-9_])"
    counts[word] = [len(re.findall(pat, before_text)), len(re.findall(pat, after_text))]
assert all(a == b for a, b in counts.values()), counts

audit = {
    "schema": "fa-v23-prefix-3646-3650-ascii-structural",
    "base_source_sha256": base_sha,
    "candidate_sha256": candidate,
    "candidate_lines": len(after_text.splitlines()),
    "repairs": ["strongPrincipalCore_pointwise_explicit_Sub_sub", "strongSchrodingerCore_pointwise_explicit_Sub_sub"],
    "patch_transport_ascii_only": True,
    "semantic_public_proposition_change": False,
    "theorem_lemma_headers_identical": True,
    "declaration_sequence_identical": True,
    "forbidden_lexical_counts_preserved": True,
    "forbidden_lexical_counts_before_after": counts,
}
(out / "PATCH_AUDIT.json").write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
(out / "candidate.sha256").write_text(candidate + "\n")
print(json.dumps(audit, indent=2, sort_keys=True))
