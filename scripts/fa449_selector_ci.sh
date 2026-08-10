#!/usr/bin/env bash
set -euo pipefail

BASE="build-logs/fa449-first-cluster"
SELBASE="$BASE/selector-baseline"
SELECTED="$BASE/selected"
CONFIRM="$BASE/selected-confirm"
FINAL="$BASE/final"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
ACTIVE_BRANCH="${ACTIVE_BRANCH:-fix/fa449-first-cluster-matrix-20260810}"
MAX_ERRORS="${MAX_ERRORS:-100}"
mkdir -p "$SELBASE" "$SELECTED" "$CONFIRM" "$FINAL"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

action_install() {
  local d="$1"
  curl --retry 5 --retry-all-errors --fail --silent --show-error \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none > "$d/elan-init.log" 2>&1
  export PATH="${HOME}/.elan/bin:${PATH}"
  elan toolchain install "$(cat lean-toolchain)" > "$d/toolchain-install.log" 2>&1
  printf '0' > "$d/toolchain-install.exit"
  lean --version | tee "$d/lean-version.txt"
  lake --version | tee "$d/lake-version.txt"
  lake exe cache get | tee "$d/cache-get.log"
  printf '0' > "$d/cache-get.exit"
}

compile_one() {
  local d="$1" stem="$2" cap="$3"
  local src="PrimalitySheafVerification/${stem}.lean"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  mkdir -p .lake/build/lib/lean/PrimalitySheafVerification
  rm -f "$o" "$i"
  local command=(lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false \
    -o "$o" -i "$i" "$src")
  printf '%q ' "${command[@]}" > "$d/${stem}.command"
  printf '\n' >> "$d/${stem}.command"
  touch "$d/${stem}.executed"
  set +e
  "${command[@]}" > "$d/${stem}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$d/${stem}.exit"
  if test "$rc" -eq 0 && test -s "$o" && test -s "$i"; then
    printf 'true' > "$d/${stem}.artifacts_ok"
  else
    printf 'false' > "$d/${stem}.artifacts_ok"
  fi
}

metric_set() {
  local d="$1" variant="$2" metadata="$3" cap="$4"
  compile_one "$d" Mock2 50
  compile_one "$d" Mock2_Advanced 50
  compile_one "$d" Mock2_FunctionalAnalysis "$cap"
  export VARIANT="$variant"
  export FA442_OUT_DIR="$d"
  export FA442_SOURCE="$SRC"
  export FA442_METADATA="$metadata"
  export FA442_EXPECTED_LINES="$(wc -l < "$SRC" | tr -d ' ')"
  export MAX_ERRORS="$cap"
  python3 scripts/fa442_record_direct_metric.py > "$d/metric-console.log" 2>&1
  cat "$d/metric-console.log"
}

# Independent baseline compilation in the selector job.
action_install "$SELBASE"
export PATH="${HOME}/.elan/bin:${PATH}"
python3 scripts/fa449_prepare_first_cluster.py \
  --variant baseline --output-dir "$SELBASE" > "$SELBASE/prepare.log" 2>&1
cat "$SELBASE/prepare.log"
metric_set "$SELBASE" baseline "$SELBASE/CANDIDATE.json" "$MAX_ERRORS"

# Current-run artifact selector.
python3 scripts/fa449_select_first_cluster.py > "$SELECTED/selector-console.log" 2>&1
cat "$SELECTED/selector-console.log"

# Require the independently compiled selector baseline to be byte- and metric-identical.
python3 - <<'PY'
import json
from pathlib import Path
base=Path('build-logs/fa449-first-cluster')
ind=json.loads((base/'selector-baseline/METRIC.json').read_text())
selection=json.loads((base/'selected/SELECTION.json').read_text())
mat=selection['baseline']
fields=(
  'source_sha256','line_count','target_header_sha256',
  'declaration_sequence_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
  'FA_first_actual_error_line','FA_first_actual_error_col',
  'FA_first_error_declaration','FA_error_declaration_index',
)
mismatch={k:{'matrix':mat.get(k),'independent':ind.get(k)} for k in fields if mat.get(k)!=ind.get(k)}
ok=(
  ind.get('all_required_lean_executed') is True
  and ind.get('source_sha256')=='1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a'
  and ind.get('Mock2_exit')==0 and ind.get('Mock2_Advanced_exit')==0
  and ind.get('FA_exit')==1
  and ind.get('FA_first_actual_error_line')==33624
  and ind.get('FA_first_actual_error_col')==57
  and ind.get('FA_first_error_declaration')=='selectedCuspRestrictionRepresentative_add'
  and not mismatch
)
result={'classification':'VERIFIED' if ok else 'INFRA_FAILURE','ok':ok,'mismatch':mismatch,'metric':ind}
(base/'selected/INDEPENDENT_BASELINE.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok: raise SystemExit('independent baseline mismatch')
PY

# Materialize selected source and create confirmation metadata.
cp "$SELECTED/Mock2_FunctionalAnalysis-selected.lean" "$SRC"
python3 - <<'PY'
import json
from pathlib import Path
base=Path('build-logs/fa449-first-cluster')
selection=json.loads((base/'selected/SELECTION.json').read_text())
chosen=selection['chosen']
metadata={
 'variant':chosen.get('variant','baseline'),
 'candidate_sha256':chosen['source_sha256'],
 'baseline_sha256':'1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a',
 'line_count':chosen['line_count'],
 'target_header_sha256':chosen['target_header_sha256'],
 'declaration_sequence_sha256':chosen['declaration_sequence_sha256'],
 'baseline_forbidden_counts':selection['baseline'].get('candidate_forbidden_counts',{}),
 'repairs':chosen.get('repairs',[]),
}
(base/'selected-confirm/CANDIDATE.json').write_text(json.dumps(metadata,indent=2)+'\n')
(base/'selected/SELECTED_METADATA.json').write_text(json.dumps(metadata,indent=2)+'\n')
PY
for f in lean-version.txt lake-version.txt toolchain-install.exit cache-get.exit; do
  cp "$SELBASE/$f" "$CONFIRM/$f"
done
SELECTED_VARIANT="$(python3 -c "import json; print(json.load(open('$SELECTED/SELECTION.json'))['chosen']['variant'])")"
metric_set "$CONFIRM" "$SELECTED_VARIANT" "$CONFIRM/CANDIDATE.json" "$MAX_ERRORS"

# Matrix/confirmation reproduction and selected/worktree identity.
python3 - <<'PY'
import hashlib,json
from pathlib import Path
base=Path('build-logs/fa449-first-cluster')
sel=json.loads((base/'selected/SELECTION.json').read_text())
chosen=sel['chosen']; metric=json.loads((base/'selected-confirm/METRIC.json').read_text())
src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
actual=hashlib.sha256(src.read_bytes()).hexdigest()
fields=(
 'source_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
 'FA_first_actual_error_line','FA_first_actual_error_col',
 'FA_first_error_declaration','FA_error_declaration_index',
)
mismatch={k:{'matrix':chosen.get(k),'confirm':metric.get(k)} for k in fields if chosen.get(k)!=metric.get(k)}
ok=(
 actual==chosen.get('source_sha256')
 and metric.get('all_required_lean_executed') is True
 and metric.get('Mock2_exit')==0 and metric.get('Mock2_Advanced_exit')==0
 and metric.get('forbidden_clean') is True and not mismatch
)
result={'classification':'VERIFIED' if ok else 'INFRA_FAILURE','ok':ok,'actual_sha256':actual,'mismatch':mismatch,'metric':metric}
(base/'selected-confirm/CONFIRMATION.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok: raise SystemExit('selected candidate did not reproduce')
PY

# Persist official champion source only after direct reproduction.
git add "$SRC"
git add -f "$SELECTED/SELECTION.json" "$SELECTED/CANDIDATE_RESULTS.json" \
  "$SELECTED/SELECTED_METADATA.json" "$SELECTED/INDEPENDENT_BASELINE.json" \
  "$CONFIRM/METRIC.json" "$CONFIRM/CONFIRMATION.json"
if ! git diff --cached --quiet; then
  git commit -m "ci: persist FA449 direct champion ${SELECTED_VARIANT} [skip ci]"
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi
SOURCE_COMMIT="$(git rev-parse HEAD)"

selected_sha="$(sha256sum "$SELECTED/Mock2_FunctionalAnalysis-selected.lean" | awk '{print $1}')"
worktree_sha="$(sha256sum "$SRC" | awk '{print $1}')"
head_sha="$(git show "HEAD:${SRC}" | sha256sum | awk '{print $1}')"
identity_ok=false
if test "$selected_sha" = "$worktree_sha" && test "$worktree_sha" = "$head_sha"; then identity_ok=true; fi
export selected_sha worktree_sha head_sha identity_ok SOURCE_COMMIT
python3 - <<'PY'
import json,os
from pathlib import Path
r={'selected_sha':os.environ['selected_sha'],'worktree_sha':os.environ['worktree_sha'],
'HEAD_source_sha':os.environ['head_sha'],'identity_ok':os.environ['identity_ok']=='true',
'commit':os.environ['SOURCE_COMMIT']}
Path('build-logs/fa449-first-cluster/final/CHECKED_IN_IDENTITY.json').write_text(json.dumps(r,indent=2)+'\n')
if not r['identity_ok']: raise SystemExit('checked-in identity mismatch')
PY

# Checked-in FA x2. Do not call this TRUE PASS unless exits and artifacts all pass.
compile_fa_final() {
  local n="$1"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.ilean"
  rm -f "$o" "$i"
  local cmd=(lake env lean -DmaxErrors=150 -DwarningAsError=false -o "$o" -i "$i" "$SRC")
  printf '%q ' "${cmd[@]}" > "$FINAL/FA-run${n}.command"; printf '\n' >> "$FINAL/FA-run${n}.command"
  touch "$FINAL/FA-run${n}.executed"
  set +e; "${cmd[@]}" > "$FINAL/FA-run${n}.log" 2>&1; rc=$?; set -e
  printf '%s' "$rc" > "$FINAL/FA-run${n}.exit"
  test -s "$o" && printf true > "$FINAL/FA-run${n}.olean" || printf false > "$FINAL/FA-run${n}.olean"
  test -s "$i" && printf true > "$FINAL/FA-run${n}.ilean" || printf false > "$FINAL/FA-run${n}.ilean"
}
compile_fa_final 1
compile_fa_final 2
python3 - <<'PY'
import importlib.util,json,sys
from pathlib import Path
spec=importlib.util.spec_from_file_location('audit','scripts/fa442_prepare_same_height_candidate.py')
mod=importlib.util.module_from_spec(spec); sys.modules[spec.name]=mod; spec.loader.exec_module(mod)
base=Path('build-logs/fa449-first-cluster/final')
audit=mod.forbidden_counts(Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text())
r1=int((base/'FA-run1.exit').read_text()); r2=int((base/'FA-run2.exit').read_text())
art={k:(base/k).read_text()=='true' for k in ('FA-run1.olean','FA-run1.ilean','FA-run2.olean','FA-run2.ilean')}
clean=all(v==0 for v in audit.values()); true_pass=r1==0 and r2==0 and all(art.values()) and clean
r={'run1':r1,'run2':r2,'artifacts':art,'trust_audit':audit,'FA_TRUE_PASS':true_pass}
(base/'FA_FINAL.json').write_text(json.dumps(r,indent=2)+'\n'); print(json.dumps(r,indent=2))
PY
FA_TRUE_PASS="$(python3 -c "import json; print(str(json.load(open('$FINAL/FA_FINAL.json'))['FA_TRUE_PASS']).lower())")"
mkdir -p "$FINAL/downstream"
if test "$FA_TRUE_PASS" = true; then
  printf '{"classification":"PENDING_ORDERED_DOWNSTREAM"}\n' > "$FINAL/downstream/DOWNSTREAM.json"
else
  printf '{"classification":"SKIPPED_FA_NOT_TRUE_PASS","Integrated":"SKIPPED","Mock3_bridges":"SKIPPED","QYM":"SKIPPED"}\n' > "$FINAL/downstream/DOWNSTREAM.json"
fi

python3 - <<'PY'
import json,os
from pathlib import Path
base=Path('build-logs/fa449-first-cluster')
sel=json.loads((base/'selected/SELECTION.json').read_text()); fa=json.loads((base/'final/FA_FINAL.json').read_text())
classification='TRUE PASS' if fa['FA_TRUE_PASS'] else sel['classification']
r={'classification':classification,'baseline':sel['baseline'],'chosen':sel['chosen'],
'candidate_results':sel['candidate_results'],'checked_in':json.loads((base/'final/CHECKED_IN_IDENTITY.json').read_text()),
'FA_checked_in':fa,'downstream':json.loads((base/'final/downstream/DOWNSTREAM.json').read_text()),
'workflow_run_url':f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}"}
(base/'final/FINAL.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
PY

git add -f "$FINAL/CHECKED_IN_IDENTITY.json" "$FINAL/FA_FINAL.json" \
  "$FINAL/downstream/DOWNSTREAM.json" "$FINAL/FINAL.json"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record FA449 checked-in verification [skip ci]'
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi
