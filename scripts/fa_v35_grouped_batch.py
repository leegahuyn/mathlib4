#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
if len(sys.argv)!=3: raise SystemExit('usage: fa_v35_grouped_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path('scripts/fa_v35_grouped_from_v34.patch')
before=source.read_bytes(); bt=before.decode('utf-8')
BASE='5a3d86721303e2a03bb246176f72b0b64f52b0ed9b74ba4360a6815eb8f07dcc'
PATCH='39ddf4c5b1c121bab7773a2d6f477763d6c06593642de753609a612f406f7317'
CAND='6b065f7bbe63d1f1eda74688ae6c9ed458a5c29072597fdf8949afbfc1ddd1f1'
base=hashlib.sha256(before).hexdigest(); assert base==BASE,(base,BASE)
if os.environ.get('BASE_SOURCE_SHA256'): assert base==os.environ['BASE_SOURCE_SHA256']
pb=patch.read_bytes(); psha=hashlib.sha256(pb).hexdigest(); assert psha==PATCH,(psha,PATCH)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr)
if p.returncode: raise SystemExit(f'patch failed {p.returncode}:\n{p.stdout.decode(errors="replace")}\n{p.stderr.decode(errors="replace")}')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61475

decl=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
assert decl.findall(bt)==decl.findall(at),'declaration sequence changed'
th=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(s):
 st=[m.start() for m in decl.finditer(s)]; r=[]
 for m in th.finditer(s):
  nxt=next((x for x in st if x>m.start()),len(s)); bl=s[m.start():nxt]; cut=bl.find(':= by')
  if cut<0: cut=bl.find(':=')
  r.append((m.group(2),re.sub(r'\s+',' ',bl if cut<0 else bl[:cut]).strip()))
 return r
assert headers(bt)==headers(at),'theorem/lemma proposition header changed'
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
 pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'; counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
repairs=['3646_3650_fixedPhaseCoreEvaluation_cluster','3689_map_neg_coordinate_normalization','4276_4282_tsupport_conjugation_siblings','58085_halfWeight_namespace_context','58846_continuousLinearMap_namespace_context','59650_closedOperators_essentialCoreRoute_context','4343_direct_effective_quotient_identity','60394_halfWeight_namespace_context','4409_finset_sum_parser']
audit={'schema':'fa-v35-full-inventory-grouped-strict','base_source_sha256':base,'patch_sha256':psha,'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':repairs,'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(cand+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
