#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
if len(sys.argv)!=3: raise SystemExit('usage: fa_v34_evalmap_immutable_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path('scripts/fa_v34_evalmap_immutable.patch')
BASE='931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4'
PATCH='2a3a07764986e24dd99650b8dac3b6f602bfd253b0c7dd200242e8f860331092'
CAND='31b9a085ddc116364065467164a9a42628fe8a2759c17ccd479a7bbd90886123'
before=source.read_bytes(); bt=before.decode('utf-8'); base=hashlib.sha256(before).hexdigest(); assert base==BASE,(base,BASE)
pb=patch.read_bytes(); ps=hashlib.sha256(pb).hexdigest(); assert ps==PATCH,(ps,PATCH)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True); (out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr); assert p.returncode==0,(p.returncode,p.stdout,p.stderr)
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61467
decl=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)'); assert decl.findall(bt)==decl.findall(at)
th=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(s):
  starts=[m.start() for m in decl.finditer(s)]; r=[]
  for m in th.finditer(s):
    nxt=next((x for x in starts if x>m.start()),len(s)); block=s[m.start():nxt]; cut=block.find(':= by')
    if cut<0: cut=block.find(':=')
    r.append((m.group(2),re.sub(r'\s+',' ',block if cut<0 else block[:cut]).strip()))
  return r
assert headers(bt)==headers(at)
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
  pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'; counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
audit={'schema':'fa-v34-evalmap-immutable-strict','base_source_sha256':BASE,'patch_sha256':PATCH,'candidate_sha256':CAND,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':['3646_fixedPhaseCoreEvaluation_map_sub','3650_fixedPhaseCoreEvaluation_map_sub_map_smul'],'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(CAND+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
