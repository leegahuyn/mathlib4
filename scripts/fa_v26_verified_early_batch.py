#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v26_verified_early_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path('scripts/fa_v26_verified_early_from_canonical.patch')
before=source.read_bytes(); bt=before.decode('utf-8')
base=hashlib.sha256(before).hexdigest(); expected_base='ceaa3d57513652edda592c4b22519640d4a233119f6720ff32fb07d45dcad219'
assert base==expected_base,(base,expected_base)
pb=patch.read_bytes(); ps=hashlib.sha256(pb).hexdigest(); expected_patch='ec5a335b3084a505e7c8f26372ebb039bc78016cbaf7ed4cffb7bad6bd36e873'
assert ps==expected_patch,(ps,expected_patch)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr)
if p.returncode: raise SystemExit(f'patch failed {p.returncode}: {p.stdout.decode(errors="replace")} {p.stderr.decode(errors="replace")}')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); expected_candidate='5721f70f128be56d9ff428d7d64a84fb4ee15c9f0806c903c7729e5a85b6fa1b'
assert cand==expected_candidate,(cand,expected_candidate)
assert len(at.splitlines())==61455
decl_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
assert decl_re.findall(bt)==decl_re.findall(at),'declaration sequence changed'
th_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(s):
    starts=[m.start() for m in decl_re.finditer(s)]; r=[]
    for m in th_re.finditer(s):
        nxt=next((x for x in starts if x>m.start()),len(s)); block=s[m.start():nxt]; cut=block.find(':= by')
        if cut<0: cut=block.find(':=')
        r.append((m.group(2),re.sub(r'\s+',' ',block if cut<0 else block[:cut]).strip()))
    return r
assert headers(bt)==headers(at),'theorem/lemma proposition header changed'
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'; counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
audit={'schema':'fa-v26-verified-early-strict','base_source_sha256':base,'patch_sha256':ps,'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':['3653_predecessor_dependent_whole_proposition_transport','3659_petersson_forcing_zero_inner_zero_right','3669_product_measurability_pointwise_normal_form','3669_translation_ae_orientation'],'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(cand+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
