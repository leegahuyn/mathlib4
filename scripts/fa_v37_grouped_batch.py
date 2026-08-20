#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
if len(sys.argv)!=3: raise SystemExit('usage: fa_v37_grouped_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path('scripts/fa_v37_grouped_from_v36.patch')
before=source.read_bytes(); bt=before.decode('utf-8')
BASE='b453b65cb6b25b27a7ab6bf32fa657b4b15cadf97d5efdcb9c13ce748eb443aa'
PATCH='104b2154a738db5629de464ac3a5b884e854aa5871888e6bb94c93f43f5ef48e'
CAND='e17ff90193c6959b15f743ef930446b4cfd45bc6df4d762057c13b4b06602d05'
base=hashlib.sha256(before).hexdigest(); assert base==BASE,(base,BASE)
if os.environ.get('BASE_SOURCE_SHA256'): assert base==os.environ['BASE_SOURCE_SHA256']
pb=patch.read_bytes(); psha=hashlib.sha256(pb).hexdigest(); assert psha==PATCH,(psha,PATCH)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr)
if p.returncode: raise SystemExit(f'patch failed {p.returncode}:\n{p.stdout.decode(errors="replace")}\n{p.stderr.decode(errors="replace")}')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61493

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
repairs=['3653_transport_unfold_normalization','3669_uncurry_left_assoc_measurability','3689_zero_limit_ring_normalization','3690_product_sub_pair_normalization','3756_compact_support_function_add_shape','3896_Lp_pointwise_add_shape','4206_unicode_mu_API_argument','4208_negative_indicator_membership','4218_completion_uniform_inducing_explicit_type']
audit={'schema':'fa-v37-grouped-safe-roots-strict','base_source_sha256':base,'patch_sha256':psha,'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':repairs,'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(cand+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
