#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v23_cumulative_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
patch_path=Path('scripts/fa_v23_from_v22.patch')
expected_base=os.environ.get('BASE_SOURCE_SHA256','')
expected_base_locked='6b73cb7d68157c861830dbefd30ae7bb0ddcc68b911fc89b49802836752bc965'
expected_patch='8c1dd4192632021465518496eeb458476ba6b3bd416febc3058bcd83c7cad4e2'
expected_candidate='a26135f6674fb4111307c471b92b036b2d2f4a529dba3bb67bbfd7a7e35a90ce'

before=source.read_bytes(); before_text=before.decode('utf-8'); base_sha=hashlib.sha256(before).hexdigest()
assert base_sha==expected_base_locked,(base_sha,expected_base_locked)
if expected_base: assert base_sha==expected_base,(base_sha,expected_base)
patch_bytes=patch_path.read_bytes(); patch_sha=hashlib.sha256(patch_bytes).hexdigest()
assert patch_sha==expected_patch,(patch_sha,expected_patch)
proc=subprocess.run(['patch','-p1','--batch','--forward'],input=patch_bytes,capture_output=True,cwd=Path.cwd())
(out/'patch.stdout').write_bytes(proc.stdout); (out/'patch.stderr').write_bytes(proc.stderr)
if proc.returncode != 0:
    raise SystemExit(f'patch failed {proc.returncode}:\n{proc.stdout.decode(errors="replace")}\n{proc.stderr.decode(errors="replace")}')
after=source.read_bytes(); after_text=after.decode('utf-8'); candidate_sha=hashlib.sha256(after).hexdigest()
assert candidate_sha==expected_candidate,(candidate_sha,expected_candidate)

decl_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
assert decl_re.findall(before_text)==decl_re.findall(after_text),'declaration sequence changed'
start_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def theorem_headers(text):
    starts=[m.start() for m in decl_re.finditer(text)]; result=[]
    for m in start_re.finditer(text):
        nxt=next((p for p in starts if p>m.start()),len(text)); block=text[m.start():nxt]
        cut=block.find(':= by')
        if cut<0: cut=block.find(':=')
        header=block if cut<0 else block[:cut]
        result.append((m.group(2),re.sub(r'\s+',' ',header).strip()))
    return result
assert theorem_headers(before_text)==theorem_headers(after_text),'theorem/lemma proposition header changed'
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool']
counts={}
for word in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(word)+r'(?![A-Za-z0-9_])'
    counts[word]=[len(re.findall(pat,before_text)),len(re.findall(pat,after_text))]
assert all(a==b for a,b in counts.values()),counts
repairs=[
 'strong_principal_ambient_sub_coercion','strong_schrodinger_ambient_sub_coercion',
 'successor_coordinate_projection_normalization','predecessor_dependent_family_transport',
 'petersson_forcing_zero_explicit','petersson_coordinate_separation',
 'raised_lowered_norm_identity_explicit_rewrites','joint_graph_density_transport',
 'partial_eigenspace_subtype_transport','spectral_star_normal_forms',
 'spectral_graph_membership_and_coercive_inner_normalization','p5_manifold_scope',
 'literal_active_center_finite_bridge'
]
audit={
 'schema':'fa-v23-cumulative-strict-v1','base_source_sha256':base_sha,'patch_sha256':patch_sha,
 'candidate_sha256':candidate_sha,'candidate_bytes':len(after),'candidate_lines':len(after_text.splitlines()),
 'repairs':repairs,'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,
 'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,
 'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts,
}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(candidate_sha+'\n')
print(json.dumps(audit,indent=2,sort_keys=True))
