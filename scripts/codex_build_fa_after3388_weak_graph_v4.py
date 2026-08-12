from pathlib import Path

base = Path('scripts/codex_fa_after3388_weak_graph_v3.sh').read_text()
base = base.replace('codex-fa-after3388-weak-graph-v3', 'codex-fa-after3388-weak-graph-v4')
marker = "curl --retry 5 --retry-all-errors --fail --silent --show-error https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh"
assert base.count(marker) == 1
extra = r'''python3 - <<'PY4'
from pathlib import Path
import hashlib,json,re
p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before=p.read_text()
decl_rx=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0=[m.group('name') for m in decl_rx.finditer(before)]
forbidden=['sorry','admit','axiom','set_option']
fc0={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',before)) for x in forbidden}
old='''  simpa only [intrinsicJointCutoffTriple, baseProjection_apply,
    raiseProjection_apply, lowerProjection_apply] using hOuter'''
new='''  change Filter.Tendsto (fun j ↦ intrinsicJointCutoffTriple j n x)
    Filter.atTop (nhds x) at hOuter
  exact hOuter'''
assert before.count(old)==1, before.count(old)
after=before.replace(old,new,1)
p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
name='intrinsicJointCutoffTriple_tendsto'; tag='theorem '+name
a0=before.index(tag); a1=after.index(tag)
assert before[a0:before.index(':= by',a0)+5] == after[a1:after.index(':= by',a1)+5]
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest()
out=Path('build-logs/codex-fa-after3388-weak-graph-v4')
audit=json.loads((out/'PATCH_AUDIT.json').read_text())
audit['candidate_sha256']=sha
audit.setdefault('targets',[]).append(name)
audit['current_source_declaration_index_for_joint_tendsto']=3432
audit['joint_withlp_reconstruction_probe_run_id']=31576675661
audit['target_public_headers_byte_identical']=True
audit['semantic_public_proposition_change']=False
audit['existing_declaration_relative_order_preserved']=True
audit['forbidden_lexical_counts_preserved']=True
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'CANDIDATE_IDENTITY.json').write_text(json.dumps({'sha256':sha,'bytes':len(b),'lines':len(after.splitlines())},indent=2)+'\n')
(out/'candidate.sha256').write_text(sha+'\n')
PY4

'''
out = base.replace(marker, extra + marker, 1)
Path('/tmp/codex_fa_after3388_weak_graph_v4.sh').write_text(out)
