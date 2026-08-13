#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v35_evalmap_structural_v2.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
before=source.read_bytes(); bt=before.decode('utf-8')
BASE='931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4'
V1='31b9a085ddc116364065467164a9a42628fe8a2759c17ccd479a7bbd90886123'
CAND='276989dce9ebe475f782253ba1274a797befb36f829d653a91e426b67f4c41ea'
assert hashlib.sha256(before).hexdigest()==BASE
sub=out/'v1'; sub.mkdir(exist_ok=True)
subprocess.run(['python3','scripts/fa_v35_evalmap_structural.py',str(source),str(sub)],check=True)
assert hashlib.sha256(source.read_bytes()).hexdigest()==V1
text=source.read_text()
old='''  rw [hPoint, strongPrincipalCore_apply_pointwise,\n    potentialMultiplicationCore_apply]\n  ring\n'''
new='''  rw [hPoint, strongPrincipalCore_apply_pointwise,\n    potentialMultiplicationCore_apply]\n  unfold strongSchrodingerDifferentialExpression\n  ring\n'''
assert text.count(old)==1,text.count(old)
text=text.replace(old,new,1)
source.write_text(text,encoding='utf-8')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest()
assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61468

decl=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
assert decl.findall(bt)==decl.findall(at),'declaration sequence changed'
th=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(s):
    starts=[m.start() for m in decl.finditer(s)]; r=[]
    for m in th.finditer(s):
        nxt=next((x for x in starts if x>m.start()),len(s)); block=s[m.start():nxt]; cut=block.find(':= by')
        if cut<0: cut=block.find(':=')
        r.append((m.group(2),re.sub(r'\s+',' ',block if cut<0 else block[:cut]).strip()))
    return r
assert headers(bt)==headers(at),'theorem/lemma header changed'
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'; counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
audit={'schema':'fa-v35-evalmap-structural-v2-strict','base_source_sha256':BASE,'candidate_sha256':CAND,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':['3646_fixedPhaseCoreEvaluation_map_sub','3650_fixedPhaseCoreEvaluation_map_sub_map_smul_unfold_expression'],'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(CAND+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
