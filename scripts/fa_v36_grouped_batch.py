#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
if len(sys.argv)!=3: raise SystemExit('usage: fa_v36_grouped_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path('scripts/fa_v36_grouped_from_v35.patch')
before=source.read_bytes(); bt=before.decode('utf-8')
BASE='6b065f7bbe63d1f1eda74688ae6c9ed458a5c29072597fdf8949afbfc1ddd1f1'
PATCH='8d1f9710bd43786401da7a73ea7583b59ff640de3565acedd4fac7619a90280e'
CAND='b453b65cb6b25b27a7ab6bf32fa657b4b15cadf97d5efdcb9c13ce748eb443aa'
base=hashlib.sha256(before).hexdigest(); assert base==BASE,(base,BASE)
if os.environ.get('BASE_SOURCE_SHA256'): assert base==os.environ['BASE_SOURCE_SHA256']
pb=patch.read_bytes(); psha=hashlib.sha256(pb).hexdigest(); assert psha==PATCH,(psha,PATCH)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr)
if p.returncode: raise SystemExit(f'patch failed {p.returncode}:\n{p.stdout.decode(errors="replace")}\n{p.stderr.decode(errors="replace")}')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61487

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
repairs=[
 '3653_dependent_whole_proposition_transport',
 '3669_uncurry_mul_assoc_measurability_shape',
 '3689_outer_sub_eq_add_neg_normalization',
 'p5_torus_haar_probability_context',
 '3890_real_scalar_const_smul_annotation',
 '3896_3897_Lp_ext_api_shape',
 'L2_inner_self_scalar_annotation_siblings',
 '4206_restrict_withDensity_pinned_api',
 '4218_completion_isUniformInducing_coe_api',
 '4264_4268_real_complex_convolution_map_body_cluster'
]
audit={'schema':'fa-v36-full-inventory-grouped-strict','base_source_sha256':base,'patch_sha256':psha,'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':repairs,'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts,'intentionally_unmodified_public_header_blockers':['4262_friedrichsMollifier_convolution_compactIndicator_eq']}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(cand+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
