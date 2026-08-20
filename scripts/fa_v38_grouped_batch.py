#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
if len(sys.argv)!=3: raise SystemExit('usage: fa_v38_grouped_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path('scripts/fa_v38_grouped_from_v37.patch')
before=source.read_bytes(); bt=before.decode('utf-8')
BASE='e17ff90193c6959b15f743ef930446b4cfd45bc6df4d762057c13b4b06602d05'
PATCH='5796e885e6c952b70d72bb3a1b0e7c133bd4cc169e2496745e2908fc36b903f2'
CAND='bb3d1837dd3df682f8a72e8dc7301d31662b844fceab6b8aba410dc8333edefb'
base=hashlib.sha256(before).hexdigest(); assert base==BASE,(base,BASE)
if os.environ.get('BASE_SOURCE_SHA256'): assert base==os.environ['BASE_SOURCE_SHA256']
pb=patch.read_bytes(); psha=hashlib.sha256(pb).hexdigest(); assert psha==PATCH,(psha,PATCH)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr)
if p.returncode: raise SystemExit(f'patch failed {p.returncode}:\n{p.stdout.decode(errors="replace")}\n{p.stderr.decode(errors="replace")}')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61532

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
repairs=['3729_core_range_transport', '3755_partition_contdiff_coercion', '3778_localizedGauge_unfold', '3779_localizedGauge_unfold', '3842_upperLift_add_algebra', '3843_upperLift_smul_algebra', '3871_fourier_scale_pos', '3874_fourier_box_measurable_shape', '3878_complex_coordinate_projection', '3917_inverse_scale_interval', '3917_forward_scale_interval', '3920_inverse_scale_interval', '4325_realSmooth_finset_sum_shape', '4243_subset_tsupport_api', '4329_subset_tsupport_api', '4337_subset_tsupport_api', '4401_subset_tsupport_api', '4166_4173_FredholmBypass_namespace', '4403_4411_4412_prod_projection_api']
audit={'schema':'fa-v38-full-inventory-grouped-strict','base_source_sha256':base,'patch_sha256':psha,'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':repairs,'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(cand+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
