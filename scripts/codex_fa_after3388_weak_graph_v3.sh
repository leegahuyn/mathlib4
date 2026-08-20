#!/usr/bin/env bash
set -euo pipefail
OUT=build-logs/codex-fa-after3388-weak-graph-v3
BASE_RUN_ID=31585293435
BASE_JOB_ID=94077605811
BASE_HEAD_SHA=a08619a84be82a24c5b417cd2fd7f93987b43195
BASE_ARTIFACT_ID=9137152661
BASE_ARTIFACT_NAME=codex-fa-after3388-weak-graph-v1-a08619a84be82a24c5b417cd2fd7f93987b43195
BASE_ARTIFACT_DIGEST=sha256:4dececb5270dac19fc2a4d9342ef660a2e52b20709eed1e7d3d0fca37de66cec
BASE_SOURCE_SHA256=87253b668644520e28d5b9b7c36ee946d5b214b75b7b94639a0e67dbb277c386
mkdir -p "$OUT" /tmp/base

gh api "repos/${GITHUB_REPOSITORY}/actions/runs/${BASE_RUN_ID}" >"$OUT/run.json"
gh api "repos/${GITHUB_REPOSITORY}/actions/jobs/${BASE_JOB_ID}" >"$OUT/job.json"
gh api "repos/${GITHUB_REPOSITORY}/actions/artifacts/${BASE_ARTIFACT_ID}" >"$OUT/artifact.json"
gh api "repos/${GITHUB_REPOSITORY}/actions/artifacts/${BASE_ARTIFACT_ID}/zip" >/tmp/base.zip
test "sha256:$(sha256sum /tmp/base.zip | awk '{print $1}')" = "$BASE_ARTIFACT_DIGEST"
unzip -q /tmp/base.zip -d /tmp/base
BASE_RUN_ID="$BASE_RUN_ID" BASE_JOB_ID="$BASE_JOB_ID" BASE_HEAD_SHA="$BASE_HEAD_SHA" \
BASE_ARTIFACT_ID="$BASE_ARTIFACT_ID" BASE_ARTIFACT_NAME="$BASE_ARTIFACT_NAME" \
BASE_ARTIFACT_DIGEST="$BASE_ARTIFACT_DIGEST" BASE_SOURCE_SHA256="$BASE_SOURCE_SHA256" \
python3 - <<'PY'
from pathlib import Path
import hashlib,json,os,shutil
out=Path('build-logs/codex-fa-after3388-weak-graph-v3')
r=json.loads((out/'run.json').read_text()); j=json.loads((out/'job.json').read_text()); a=json.loads((out/'artifact.json').read_text())
m=json.loads(next(Path('/tmp/base').rglob('METRIC.json')).read_text())
assert r['id']==int(os.environ['BASE_RUN_ID']) and r['head_sha']==os.environ['BASE_HEAD_SHA'] and r['status']=='completed' and r['conclusion']=='failure'
assert j['id']==int(os.environ['BASE_JOB_ID']) and j['run_id']==int(os.environ['BASE_RUN_ID']) and j['conclusion']=='failure'
assert a['id']==int(os.environ['BASE_ARTIFACT_ID']) and a['name']==os.environ['BASE_ARTIFACT_NAME'] and a['digest']==os.environ['BASE_ARTIFACT_DIGEST'] and not a['expired']
assert m['Mock2_exit']==0 and m['Mock2_Advanced_exit']==0 and m['FA_exit']==1 and m['all_required_lean_executed'] is True
assert m['FA_error_declaration_index']==3388 and m['FA_first_error_declaration']=='mem_weakRaisingSubmodule_iff_maximalAdjointGraph'
assert m['FA_first_actual_error_line']==45056 and 'ring failed' in m['FA_first_error_message']
assert m['source_sha256']==os.environ['BASE_SOURCE_SHA256'] and m['source_identity_locked_after_materialization'] is True
assert m['public_proposition_changes_explicitly_audited'] is True and m['existing_declaration_relative_order_preserved'] is True
hits=[]
for p in Path('/tmp/base').rglob('Mock2_FunctionalAnalysis.lean'):
    b=p.read_bytes()
    if 'PrimalitySheafVerification' in p.as_posix() and hashlib.sha256(b).hexdigest()==os.environ['BASE_SOURCE_SHA256']: hits.append(p)
assert len(hits)==1
shutil.copy2(hits[0],'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
(out/'ALLOWED.json').write_text(json.dumps(m['allowed_public_proposition_changes'],indent=2)+'\n')
PY

python3 - <<'PY'
from pathlib import Path
import hashlib,json,re
p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before=p.read_text(); b0=p.read_bytes()
decl_rx=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0=[m.group('name') for m in decl_rx.finditer(before)]
forbidden=['sorry','admit','axiom','set_option']
fc0={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',before)) for x in forbidden}
old_r='''    have hv := hGraph (l2CoreRangeEquiv ((n + 1) + 1) v)
    simp only [l2CoreRangeEquiv_coe, LinearPMap.neg_apply,
      physicalLowerFromSucc_on_core, inner_neg_left] at hv
    linear_combination hv'''
new_r='''    have hv := hGraph (l2CoreRangeEquiv ((n + 1) + 1) v)
    rw [l2CoreRangeEquiv_coe] at hv
    change
      inner ℂ (l2Coordinate ((n + 1) + 1) v)
          (raiseProjection n x) =
        inner ℂ
          (-(physicalLowerFromSucc (n + 1)
            (l2CoreRangeEquiv ((n + 1) + 1) v)))
          (baseProjection n x) at hv
    rw [physicalLowerFromSucc_on_core, inner_neg_left] at hv
    linear_combination hv'''
old_l='''    have hv := hGraph (l2CoreRangeEquiv n v)
    simp only [l2CoreRangeEquiv_coe, LinearPMap.neg_apply,
      physicalRaise_on_core, inner_neg_left] at hv
    linear_combination hv'''
new_l='''    have hv := hGraph (l2CoreRangeEquiv n v)
    rw [l2CoreRangeEquiv_coe] at hv
    change
      inner ℂ (l2Coordinate n v) (lowerProjection n x) =
        inner ℂ (-(physicalRaise n (l2CoreRangeEquiv n v)))
          (baseProjection n x) at hv
    rw [physicalRaise_on_core, inner_neg_left] at hv
    linear_combination hv'''
old_cr='''  exact isClosed_iInter fun v ↦
    ContinuousLinearMap.isClosed_ker (raisingDefect n v)'''
new_cr='''  exact isClosed_iInter fun
      (v : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore ((n + 1) + 1)) ↦
    ContinuousLinearMap.isClosed_ker (raisingDefect n v)'''
old_cl='''  exact isClosed_iInter fun v ↦
    ContinuousLinearMap.isClosed_ker (loweringDefect n v)'''
new_cl='''  exact isClosed_iInter fun
      (v : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) ↦
    ContinuousLinearMap.isClosed_ker (loweringDefect n v)'''
old_norm='''    have hx0 : x = 0 := norm_eq_zero.mp hx
    simp only [hx0, map_zero]'''
new_norm='''    have hx0 : x = 0 := norm_eq_zero.mp hx
    simpa [hx0]'''
after=before
for tag,old,new in [('raise-second',old_r,new_r),('lower-second',old_l,new_l),('raise-closed',old_cr,new_cr),('lower-closed',old_cl,new_cl),('norm-zero',old_norm,new_norm)]:
    assert after.count(old)==1,(tag,after.count(old))
    after=after.replace(old,new,1)
p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
names=['mem_weakRaisingSubmodule_iff_maximalAdjointGraph','mem_weakLoweringSubmodule_iff_maximalAdjointGraph','weakRaisingSubmodule_isClosed','weakLoweringSubmodule_isClosed','norm_eq_zero_iff_coordinates']
for theorem in names:
    marker='theorem '+theorem; a0=before.index(marker); a1=after.index(marker)
    assert before[a0:before.index(':= by',a0)+5] == after[a1:after.index(':= by',a1)+5]
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest(); out=Path('build-logs/codex-fa-after3388-weak-graph-v3')
audit={'base_sha256':hashlib.sha256(b0).hexdigest(),'candidate_sha256':sha,'targets':names,'repair':'normalize_negated_core_applications_plus_probe_verified_downstream_binders','existing_declaration_relative_order_preserved':True,'target_public_headers_byte_identical':True,'semantic_public_proposition_change':False,'forbidden_lexical_counts_preserved':True}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'CANDIDATE_IDENTITY.json').write_text(json.dumps({'sha256':sha,'bytes':len(b),'lines':len(after.splitlines())},indent=2)+'\n')
(out/'candidate.sha256').write_text(sha+'\n')
PY

curl --retry 5 --retry-all-errors --fail --silent --show-error https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh
sh /tmp/elan.sh -y --default-toolchain none >"$OUT/elan.log" 2>&1
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(tr -d '\r\n' < lean-toolchain)" >"$OUT/toolchain.log" 2>&1
lake exe cache get >"$OUT/cache.log" 2>&1
mkdir -p .lake/build/lib/lean/PrimalitySheafVerification
one(){ local s="$1" c="$2"; local o=.lake/build/lib/lean/PrimalitySheafVerification/$s.olean i=.lake/build/lib/lean/PrimalitySheafVerification/$s.ilean; rm -f "$o" "$i"; :>"$OUT/$s.executed"; set +e; lake env lean "-DmaxErrors=$c" -DwarningAsError=false -o "$o" -i "$i" "PrimalitySheafVerification/$s.lean" >"$OUT/$s.log" 2>&1; local x=$?; set -e; echo "$x">"$OUT/$s.exit"; }
one Mock2 1
one Mock2_Advanced 1
test "$(sha256sum PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean|awk '{print $1}')" = "$(cat "$OUT/candidate.sha256")"
one Mock2_FunctionalAnalysis 1
python3 - <<'PY'
from pathlib import Path
from bisect import bisect_right
import hashlib,json,os,re
out=Path('build-logs/codex-fa-after3388-weak-graph-v3'); p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'); s=p.read_text(); b=p.read_bytes()
ds=list(re.finditer(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)',s)); starts=[s.count('\n',0,m.start())+1 for m in ds]
rx=re.compile(r'^.+?\.lean:(\d+):(\d+): error(?:\([^)]+\))?:(.*)$'); es=[]
for raw in (out/'Mock2_FunctionalAnalysis.log').read_text(errors='replace').splitlines():
    m=rx.match(raw)
    if m:
        ln=int(m.group(1)); i=bisect_right(starts,ln)-1; es.append({'line':ln,'col':int(m.group(2)),'message':m.group(3).strip(),'declaration':ds[i].group('name') if i>=0 else None,'declaration_index':i if i>=0 else None})
ex={x:int((out/f'{x}.exit').read_text()) for x in ('Mock2','Mock2_Advanced','Mock2_FunctionalAnalysis')}; first=es[0] if es else {}; au=json.loads((out/'PATCH_AUDIT.json').read_text())
metric={'schema':'fa-after3388-weak-graph-v3','run_id':os.environ['GITHUB_RUN_ID'],'head_sha':os.environ['GITHUB_SHA'],'source_sha256':hashlib.sha256(b).hexdigest(),'source_bytes':len(b),'source_lines':len(s.splitlines()),'source_identity_locked_after_materialization':hashlib.sha256(b).hexdigest()==(out/'candidate.sha256').read_text().strip(),'Mock2_exit':ex['Mock2'],'Mock2_Advanced_exit':ex['Mock2_Advanced'],'FA_exit':ex['Mock2_FunctionalAnalysis'],'all_required_lean_executed':all((out/f'{x}.executed').exists() for x in ex),'FA_first_actual_error_line':first.get('line'),'FA_first_actual_error_col':first.get('col'),'FA_first_error_declaration':first.get('declaration'),'FA_error_declaration_index':first.get('declaration_index'),'FA_first_error_message':first.get('message'),'existing_declaration_relative_order_preserved':au['existing_declaration_relative_order_preserved'],'public_proposition_changes_explicitly_audited':True,'semantic_public_proposition_change':False,'allowed_public_proposition_changes':json.loads((out/'ALLOWED.json').read_text())}
(out/'METRIC.json').write_text(json.dumps(metric,indent=2,sort_keys=True)+'\n')
PY
exit 0
