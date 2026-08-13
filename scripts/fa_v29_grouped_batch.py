#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys
if len(sys.argv)!=3:
    raise SystemExit('usage: fa_v29_grouped_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
patch=Path('scripts/fa_v29_grouped_from_filtered.patch')
before=source.read_bytes(); bt=before.decode('utf-8')
base=hashlib.sha256(before).hexdigest(); expected_base='931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4'
assert base==expected_base,(base,expected_base)
if os.environ.get('BASE_SOURCE_SHA256'):
    assert base==os.environ['BASE_SOURCE_SHA256'],(base,os.environ['BASE_SOURCE_SHA256'])
pb=patch.read_bytes(); ps=hashlib.sha256(pb).hexdigest(); expected_patch='6c36386b9d96e5dc173c4fd0af4430d1fc95fc4a06d516e1329eab4ee09a2fa0'
assert ps==expected_patch,(ps,expected_patch)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr)
if p.returncode:
    raise SystemExit(f'patch failed {p.returncode}:\n{p.stdout.decode(errors="replace")}\n{p.stderr.decode(errors="replace")}')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); expected_candidate='c0bc540977afc978a8964690dc4996759c622f000fb9a45b2647d825b0e26b07'
assert cand==expected_candidate,(cand,expected_candidate)
assert len(at.splitlines())==61456
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
repairs=[
 '3646_core_sub_add_neg_pointwise_normalization','3650_core_sub_add_neg_pointwise_normalization',
 '3653_dependent_index_whole_proposition_transport','3659_petersson_zero_inner_zero_right',
 '3669_fubini_product_measurability_normal_form','3669_translation_ae_orientation',
 '3689_lowered_cauchy_add_neg_coordinate_normalization','3758_partition_sum_eq_one_actual_signature',
 '3772_tsupport_comp_subset_explicit_complexification','4343_effective_gamma_rewrite_application',
 '4352_4374_reduced_chart_manifold_scope_parser_root']
audit={'schema':'fa-v29-full-inventory-grouped-strict-v1','base_source_sha256':base,'patch_sha256':ps,
 'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':repairs,
 'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,
 'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,
 'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(cand+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
