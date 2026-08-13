#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v25_auth_frontier_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
patch=Path('scripts/fa_v25_auth_frontier_from_v23.patch')
base_locked='a26135f6674fb4111307c471b92b036b2d2f4a529dba3bb67bbfd7a7e35a90ce'
patch_locked='0eae32b5db6e0a85b13cc52c8c92a4469dd73088cab21e50683022ce0497268b'
candidate_locked='8746aec57bb0a2865ce890f9d1523424b2ae63ff2d8364f093096b6308274eff'
before=source.read_bytes(); before_text=before.decode('utf-8'); base=hashlib.sha256(before).hexdigest()
assert base==base_locked,(base,base_locked)
if os.environ.get('BASE_SOURCE_SHA256'): assert base==os.environ['BASE_SOURCE_SHA256']
pb=patch.read_bytes(); ps=hashlib.sha256(pb).hexdigest(); assert ps==patch_locked,(ps,patch_locked)
proc=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(proc.stdout); (out/'patch.stderr').write_bytes(proc.stderr)
if proc.returncode: raise SystemExit(f'patch failed {proc.returncode}:\n{proc.stdout.decode(errors="replace")}\n{proc.stderr.decode(errors="replace")}')
after=source.read_bytes(); after_text=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); assert cand==candidate_locked,(cand,candidate_locked)
decl_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
assert decl_re.findall(before_text)==decl_re.findall(after_text),'declaration sequence changed'
th_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(t):
    starts=[m.start() for m in decl_re.finditer(t)]; result=[]
    for m in th_re.finditer(t):
        nxt=next((x for x in starts if x>m.start()),len(t)); block=t[m.start():nxt]
        cut=block.find(':= by')
        if cut<0: cut=block.find(':=')
        result.append((m.group(2),re.sub(r'\s+',' ',block if cut<0 else block[:cut]).strip()))
    return result
assert headers(before_text)==headers(after_text),'theorem/lemma proposition header changed'
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'
    counts[w]=[len(re.findall(pat,before_text)),len(re.findall(pat,after_text))]
assert all(a==b for a,b in counts.values()),counts
audit={'schema':'fa-v25-auth-frontier-strict-v1','base_source_sha256':base,'patch_sha256':ps,'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(after_text.splitlines()),'repairs':['canonical_Submodule_addCommGroup_root','3653_dependent_binder_transport','3659_zero_application'],'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(cand+'\n')
print(json.dumps(audit,indent=2,sort_keys=True))
