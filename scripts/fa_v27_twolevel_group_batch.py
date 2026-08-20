#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v27_twolevel_group_batch.py <source> <outdir>")
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path("scripts/fa_v27_twolevel_group_from_filtered.patch")
before=source.read_bytes(); bt=before.decode("utf-8")
base=hashlib.sha256(before).hexdigest(); expected_base="931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4"
assert base==expected_base,(base,expected_base)
pb=patch.read_bytes(); ps=hashlib.sha256(pb).hexdigest(); expected_patch="bb941c41a8c5bbbe6497c2359abc5f7c3f983d82e68cb0e5587e7785e87d6fc4"
assert ps==expected_patch,(ps,expected_patch)
p=subprocess.run(["patch","-p1","--batch","--forward"],input=pb,capture_output=True)
(out/"patch.stdout").write_bytes(p.stdout); (out/"patch.stderr").write_bytes(p.stderr)
if p.returncode: raise SystemExit(f"patch failed {p.returncode}: {p.stdout.decode(errors='replace')} {p.stderr.decode(errors='replace')}")
after=source.read_bytes(); at=after.decode("utf-8"); cand=hashlib.sha256(after).hexdigest(); expected_candidate="dee03b1ab34b97b853f35fe21991006c7717c81c1b0a2f6593144cd3fa8d478b"
assert cand==expected_candidate,(cand,expected_candidate)
assert len(at.splitlines())==61452

decl=re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
assert decl.findall(bt)==decl.findall(at),"declaration sequence changed"
th=re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
def headers(s):
    starts=[m.start() for m in decl.finditer(s)]; r=[]
    for m in th.finditer(s):
        nxt=next((x for x in starts if x>m.start()),len(s)); block=s[m.start():nxt]; cut=block.find(":= by")
        if cut<0: cut=block.find(":=")
        r.append((m.group(2),re.sub(r"\s+"," ",block if cut<0 else block[:cut]).strip()))
    return r
assert headers(bt)==headers(at),"theorem/lemma proposition header changed"
forbidden=["sorry","admit","axiom","unsafe","native_decide","Lean.ofReduceBool","set_option"]
counts={}
for w in forbidden:
    pat=r"(?<![A-Za-z0-9_])"+re.escape(w)+r"(?![A-Za-z0-9_])"
    counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
audit={"schema":"fa-v27-twolevel-actual-group-strict","base_source_sha256":base,"patch_sha256":ps,"candidate_sha256":cand,"candidate_bytes":len(after),"candidate_lines":len(at.splitlines()),"repairs":["fixedPhaseGraphCoreAddCommGroup_local_ambient_group_then_Submodule_group"],"semantic_public_proposition_change":False,"theorem_lemma_headers_identical":True,"declaration_sequence_identical":True,"existing_declaration_relative_order_preserved":True,"forbidden_lexical_counts_preserved":True,"forbidden_lexical_counts_before_after":counts}
(out/"PATCH_AUDIT.json").write_text(json.dumps(audit,indent=2,sort_keys=True)+"\n",encoding="utf-8")
(out/"candidate.sha256").write_text(cand+"\n",encoding="utf-8")
print(json.dumps(audit,indent=2,sort_keys=True))
