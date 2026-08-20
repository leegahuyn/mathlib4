#!/usr/bin/env bash
set -euo pipefail

BASE="build-logs/fa453-compact-energy"
SELBASE="$BASE/selector-baseline"
SELECTED="$BASE/selected"
CONFIRM="$BASE/selected-confirm"
FINAL="$BASE/final"
DOWNSTREAM="$FINAL/downstream"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
ACTIVE_BRANCH="${ACTIVE_BRANCH:-fix/fa453-compact-energy-from-fa451-20260810}"
MAX_ERRORS="${MAX_ERRORS:-260}"
BASELINE_SHA="1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
mkdir -p "$SELBASE" "$SELECTED" "$CONFIRM" "$FINAL" "$DOWNSTREAM"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
test "$(git config user.name)" = 'github-actions[bot]'
test "$(git config user.email)" = \
  '41898282+github-actions[bot]@users.noreply.github.com'

install_pinned() {
  local d="$1"
  curl --retry 5 --retry-all-errors --fail --silent --show-error \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -o /tmp/elan-init.sh > "$d/elan-download.log" 2>&1
  sh /tmp/elan-init.sh -y --default-toolchain none > "$d/elan-init.log" 2>&1
  export PATH="${HOME}/.elan/bin:${PATH}"
  elan toolchain install "$(cat lean-toolchain)" \
    > "$d/toolchain-install.log" 2>&1
  printf '0' > "$d/toolchain-install.exit"
  lean --version | tee "$d/lean-version.txt"
  lake --version | tee "$d/lake-version.txt"
  lake exe cache get | tee "$d/cache-get.log"
  printf '0' > "$d/cache-get.exit"
}

compile_one() {
  local d="$1"
  local stem="$2"
  local cap="$3"
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
  local olean=false
  local ilean=false
  test -s "$o" && olean=true
  test -s "$i" && ilean=true
  printf '%s' "$olean" > "$d/${stem}.olean"
  printf '%s' "$ilean" > "$d/${stem}.ilean"
}

metric_set() {
  local d="$1"
  local variant="$2"
  local metadata="$3"
  local cap="$4"
  compile_one "$d" Mock2 50
  compile_one "$d" Mock2_Advanced 50
  compile_one "$d" Mock2_FunctionalAnalysis "$cap"
  export VARIANT="$variant"
  export FA442_OUT_DIR="$d"
  export FA442_SOURCE="$SRC"
  export FA442_METADATA="$metadata"
  export FA442_EXPECTED_LINES="$(wc -l < "$SRC" | tr -d ' ')"
  export MAX_ERRORS="$cap"
  python3 scripts/fa442_record_direct_metric.py \
    > "$d/metric-console.log" 2>&1
  cat "$d/metric-console.log"
}

# Independent baseline: current checked-in FA451 champion, never artifact metadata alone.
install_pinned "$SELBASE"
export PATH="${HOME}/.elan/bin:${PATH}"
actual_baseline_sha="$(sha256sum "$SRC" | awk '{print $1}')"
test "$actual_baseline_sha" = "$BASELINE_SHA"
git rev-parse HEAD > "$SELBASE/repository-head.txt"
python3 scripts/fa453_prepare_compact_energy.py \
  --variant baseline --output-dir "$SELBASE" \
  > "$SELBASE/prepare.log" 2>&1
cat "$SELBASE/prepare.log"
metric_set "$SELBASE" baseline "$SELBASE/CANDIDATE.json" "$MAX_ERRORS"

# Current-run strict selector.
python3 scripts/fa453_select_compact_energy.py \
  > "$SELECTED/selector-console.log" 2>&1
cat "$SELECTED/selector-console.log"

# Matrix baseline and independently recompiled baseline must be byte/metric identical.
python3 - <<'PY'
import json
from pathlib import Path
base=Path('build-logs/fa453-compact-energy')
ind=json.loads((base/'selector-baseline/METRIC.json').read_text(encoding='utf-8'))
selection=json.loads((base/'selected/SELECTION.json').read_text(encoding='utf-8'))
mat=selection['baseline']
fields=(
  'source_sha256','line_count','target_header_sha256',
  'declaration_sequence_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
  'FA_first_actual_error_line','FA_first_actual_error_col',
  'FA_first_error_declaration','FA_error_declaration_index',
)
mismatch={
  key:{'matrix':mat.get(key),'independent':ind.get(key)}
  for key in fields if mat.get(key)!=ind.get(key)
}
ok=(
  ind.get('all_required_lean_executed') is True
  and ind.get('source_sha256')=='1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb'
  and ind.get('line_count')==60450
  and ind.get('Mock2_exit')==0
  and ind.get('Mock2_Advanced_exit')==0
  and ind.get('FA_exit')==1
  and ind.get('FA_first_actual_error_line')==33929
  and ind.get('FA_first_actual_error_col')==4
  and ind.get('FA_first_error_declaration')=='compactSupport_height_mul_normSq_le_energy_Ioi'
  and ind.get('forbidden_clean') is True
  and not mismatch
)
result={
  'classification':'VERIFIED' if ok else 'INFRA_FAILURE',
  'ok':ok,
  'mismatch':mismatch,
  'independent_metric':ind,
  'matrix_metric':mat,
}
(base/'selected/INDEPENDENT_BASELINE.json').write_text(
  json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok:
  raise SystemExit('INFRA_FAILURE: independent FA451 baseline mismatch')
PY

# Materialize selector winner at the official repository path.
cp "$SELECTED/Mock2_FunctionalAnalysis-selected.lean" "$SRC"
cp "$SELECTED/SELECTED_METADATA.json" "$CONFIRM/CANDIDATE.json"
for evidence in lean-version.txt lake-version.txt toolchain-install.exit cache-get.exit; do
  cp "$SELBASE/$evidence" "$CONFIRM/$evidence"
done
SELECTED_VARIANT="$(python3 -c "import json; print(json.load(open('$SELECTED/SELECTION.json'))['chosen']['variant'])")"
metric_set "$CONFIRM" "$SELECTED_VARIANT" "$CONFIRM/CANDIDATE.json" "$MAX_ERRORS"

# Confirmation must exactly reproduce selected matrix direct metric.
python3 - <<'PY'
import hashlib,json
from pathlib import Path
base=Path('build-logs/fa453-compact-energy')
selection=json.loads((base/'selected/SELECTION.json').read_text(encoding='utf-8'))
chosen=selection['chosen']
metric=json.loads((base/'selected-confirm/METRIC.json').read_text(encoding='utf-8'))
source=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
actual=hashlib.sha256(source.read_bytes()).hexdigest()
fields=(
  'source_sha256','line_count','target_header_sha256',
  'declaration_sequence_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
  'FA_first_actual_error_line','FA_first_actual_error_col',
  'FA_first_error_declaration','FA_error_declaration_index',
)
mismatch={
  key:{'matrix':chosen.get(key),'confirmation':metric.get(key)}
  for key in fields if chosen.get(key)!=metric.get(key)
}
ok=(
  actual==chosen.get('source_sha256')
  and metric.get('all_required_lean_executed') is True
  and metric.get('Mock2_exit')==0
  and metric.get('Mock2_Advanced_exit')==0
  and metric.get('forbidden_clean') is True
  and not mismatch
)
result={
  'classification':'VERIFIED' if ok else 'INFRA_FAILURE',
  'verified':ok,
  'selected_sha256':chosen.get('source_sha256'),
  'materialized_sha256':actual,
  'selected_variant':chosen.get('variant'),
  'mismatch':mismatch,
  'direct_metric':metric,
}
(base/'selected-confirm/CONFIRMATION.json').write_text(
  json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok:
  raise SystemExit('INFRA_FAILURE: selected source did not reproduce')
PY

# Persist the direct-reproduced champion. No master push, no merge.
git add "$SRC"
git add -f \
  "$SELECTED/SELECTION.json" \
  "$SELECTED/CANDIDATE_RESULTS.json" \
  "$SELECTED/SELECTED_METADATA.json" \
  "$SELECTED/INDEPENDENT_BASELINE.json" \
  "$CONFIRM/METRIC.json" \
  "$CONFIRM/CONFIRMATION.json"
if ! git diff --cached --quiet; then
  git commit -m "ci: persist FA453 direct champion ${SELECTED_VARIANT} [skip ci]"
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi
SOURCE_COMMIT="$(git rev-parse HEAD)"

selected_sha="$(sha256sum "$SELECTED/Mock2_FunctionalAnalysis-selected.lean" | awk '{print $1}')"
worktree_sha="$(sha256sum "$SRC" | awk '{print $1}')"
head_sha="$(git show "HEAD:${SRC}" | sha256sum | awk '{print $1}')"
identity_ok=false
if test "$selected_sha" = "$worktree_sha" && test "$worktree_sha" = "$head_sha"; then
  identity_ok=true
fi
export selected_sha worktree_sha head_sha identity_ok SOURCE_COMMIT
python3 - <<'PY'
import json,os
from pathlib import Path
result={
  'selected_sha':os.environ['selected_sha'],
  'worktree_sha':os.environ['worktree_sha'],
  'HEAD_source_sha':os.environ['head_sha'],
  'identity_ok':os.environ['identity_ok']=='true',
  'commit':os.environ['SOURCE_COMMIT'],
}
path=Path('build-logs/fa453-compact-energy/final/CHECKED_IN_IDENTITY.json')
path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
if not result['identity_ok']:
  raise SystemExit('INFRA_FAILURE: checked-in source identity mismatch')
PY

# Checked-in FA direct compile run1 and run2.
compile_fa_final() {
  local n="$1"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean -DmaxErrors=320 -DwarningAsError=false \
    -o "$o" -i "$i" "$SRC")
  printf '%q ' "${command[@]}" > "$FINAL/FA-run${n}.command"
  printf '\n' >> "$FINAL/FA-run${n}.command"
  touch "$FINAL/FA-run${n}.executed"
  set +e
  "${command[@]}" > "$FINAL/FA-run${n}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$FINAL/FA-run${n}.exit"
  test -s "$o" && printf true > "$FINAL/FA-run${n}.olean" \
    || printf false > "$FINAL/FA-run${n}.olean"
  test -s "$i" && printf true > "$FINAL/FA-run${n}.ilean" \
    || printf false > "$FINAL/FA-run${n}.ilean"
}
compile_fa_final 1
compile_fa_final 2

python3 - <<'PY'
import importlib.util,json,sys
from pathlib import Path
spec=importlib.util.spec_from_file_location(
  'fa453_audit','scripts/fa442_prepare_same_height_candidate.py')
module=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=module
assert spec.loader is not None
spec.loader.exec_module(module)
root=Path('build-logs/fa453-compact-energy/final')
source=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text(
  encoding='utf-8')
audit=module.forbidden_counts(source)
r1=int((root/'FA-run1.exit').read_text())
r2=int((root/'FA-run2.exit').read_text())
artifacts={
  'run1_olean':(root/'FA-run1.olean').read_text()=='true',
  'run1_ilean':(root/'FA-run1.ilean').read_text()=='true',
  'run2_olean':(root/'FA-run2.olean').read_text()=='true',
  'run2_ilean':(root/'FA-run2.ilean').read_text()=='true',
}
clean=all(value==0 for value in audit.values())
true_pass=r1==0 and r2==0 and all(artifacts.values()) and clean
result={
  'checked_in_source':True,
  'FA_run1_exit':r1,
  'FA_run2_exit':r2,
  'artifacts':artifacts,
  'forbidden_audit':audit,
  'forbidden_clean':clean,
  'FA_TRUE_PASS':true_pass,
}
(root/'FA_FINAL.json').write_text(
  json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2,ensure_ascii=False))
PY
FA_TRUE_PASS="$(python3 -c "import json; print(str(json.load(open('$FINAL/FA_FINAL.json'))['FA_TRUE_PASS']).lower())")"

# Downstream is strictly ordered and only runs after checked-in FA TRUE PASS x2.
compile_downstream() {
  local stem="$1"
  local n="$2"
  local src="PrimalitySheafVerification/${stem}.lean"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean -DmaxErrors=160 -DwarningAsError=false \
    -o "$o" -i "$i" "$src")
  printf '%q ' "${command[@]}" > "$DOWNSTREAM/${stem}-run${n}.command"
  printf '\n' >> "$DOWNSTREAM/${stem}-run${n}.command"
  touch "$DOWNSTREAM/${stem}-run${n}.executed"
  set +e
  "${command[@]}" > "$DOWNSTREAM/${stem}-run${n}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$DOWNSTREAM/${stem}-run${n}.exit"
  test "$rc" -eq 0 && test -s "$o" && test -s "$i"
}
run_twice() {
  local stem="$1"
  compile_downstream "$stem" 1 && compile_downstream "$stem" 2
}

if test "$FA_TRUE_PASS" = true; then
  downstream_complete=true
  downstream_failure=''
  integrated=Mock2_FunctionalAnalysis_Integrated
  if test -f "PrimalitySheafVerification/${integrated}.lean"; then
    run_twice "$integrated" || {
      downstream_complete=false
      downstream_failure="$integrated"
    }
  else
    downstream_complete=false
    downstream_failure='Integrated-missing'
  fi
  if test "$downstream_complete" = true; then
    shopt -s nullglob
    bridges=(PrimalitySheafVerification/Mock3*.lean)
    if test "${#bridges[@]}" -eq 0; then
      downstream_complete=false
      downstream_failure='Mock3-bridges-missing'
    else
      for source in "${bridges[@]}"; do
        stem="$(basename "$source" .lean)"
        if ! run_twice "$stem"; then
          downstream_complete=false
          downstream_failure="$stem"
          break
        fi
      done
    fi
  fi
  if test "$downstream_complete" = true; then
    if test -f PrimalitySheafVerification/QYM.lean; then
      run_twice QYM || {
        downstream_complete=false
        downstream_failure='QYM'
      }
    else
      downstream_complete=false
      downstream_failure='QYM-missing'
    fi
  fi
  export downstream_complete downstream_failure
  python3 - <<'PY'
import json,os
from pathlib import Path
root=Path('build-logs/fa453-compact-energy/final/downstream')
exits={}
for path in sorted(root.glob('*.exit')):
  try:
    exits[path.name]=int(path.read_text())
  except ValueError:
    exits[path.name]=125
result={
  'classification':'TRUE_PASS' if os.environ['downstream_complete']=='true' else 'LEAN_FAILURE',
  'complete':os.environ['downstream_complete']=='true',
  'failure':os.environ['downstream_failure'],
  'ordered_exits':exits,
}
(root/'DOWNSTREAM.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
PY
else
  cat > "$DOWNSTREAM/DOWNSTREAM.json" <<'JSON'
{
  "classification": "SKIPPED_FA_NOT_TRUE_PASS",
  "complete": false,
  "Integrated": "SKIPPED",
  "Mock3_bridges": "SKIPPED",
  "QYM": "SKIPPED"
}
JSON
fi

# Requested compact machine-readable and human-readable report.
export ACTIVE_BRANCH SOURCE_COMMIT
python3 - <<'PY'
import json,os,subprocess
from pathlib import Path
base=Path('build-logs/fa453-compact-energy')
final=base/'final'
selection=json.loads((base/'selected/SELECTION.json').read_text(encoding='utf-8'))
identity=json.loads((final/'CHECKED_IN_IDENTITY.json').read_text(encoding='utf-8'))
fa=json.loads((final/'FA_FINAL.json').read_text(encoding='utf-8'))
down=json.loads((final/'downstream/DOWNSTREAM.json').read_text(encoding='utf-8'))
baseline=selection['baseline']
chosen=selection['chosen']
rows=selection['candidate_results']
if fa.get('FA_TRUE_PASS') and down.get('complete'):
  classification='TRUE PASS'
elif selection.get('classification')=='STRICT_PROMOTION':
  classification='STRICT PROMOTION'
else:
  classification='NO IMPROVEMENT'
audit=fa.get('forbidden_audit',{})
lines=[
  'FA MATRIX PIPELINE REPAIR REPORT','',
  'Baseline:',
  f"source SHA256: {baseline.get('source_sha256','')}",
  f"line count: {baseline.get('line_count','')}",
  f"direct Lean exit: {baseline.get('FA_exit','')}",
  f"first error: {baseline.get('FA_first_actual_error_line',0)}:{baseline.get('FA_first_actual_error_col',0)} {baseline.get('FA_first_error_message','')}",
  f"declaration: {baseline.get('FA_first_error_declaration','')}",'',
  'Pipeline issue found:',
  "root cause: FA442 guarded Lean installation and direct compilation with if: steps.prepare.outputs.ok == 'true'; checked-in promoted bytes failed the authoritative-baseline prepare check, so both direct stages were skipped and the selector received zero baseline metrics. Git identity was configured only on a later path. The repaired lineage now requires execution markers, direct metrics, independent baseline recompilation, and early bot identity.",
  'workflow files changed: .github/workflows/pre-commit.yml',
  'scripts changed: scripts/fa453_prepare_compact_energy.py, scripts/fa453_candidate_ci.sh, scripts/fa453_select_compact_energy.py, scripts/fa453_selector_ci.sh','',
  'Candidate results:',
  'variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification',
]
for row in rows:
  lines.append(
    f"{row.get('variant')} | {row.get('SHA256')} | {row.get('Lean_executed')} | "
    f"{row.get('FA_exit')} | {row.get('first_line')}:{row.get('first_col')} | "
    f"{row.get('declaration')} | {row.get('classification')}"
  )
lines += [
  '', 'Best direct-verified candidate:',
  f"variant: {chosen.get('variant','')}",
  f"SHA256: {chosen.get('source_sha256','')}",
  f"exit: {chosen.get('FA_exit','')}",
  f"first error: {chosen.get('FA_first_actual_error_line',0)}:{chosen.get('FA_first_actual_error_col',0)} {chosen.get('FA_first_error_message','')}",
  f"declaration: {chosen.get('FA_first_error_declaration','')}",
  f"strictly better than 31726?: {chosen.get('FA_exit')==0 or int(chosen.get('FA_error_declaration_index',-1))>2624}",
  '', 'Checked-in identity:',
  f"selected SHA: {identity.get('selected_sha','')}",
  f"worktree SHA: {identity.get('worktree_sha','')}",
  f"HEAD source SHA: {identity.get('HEAD_source_sha','')}",
  f"identity_ok: {identity.get('identity_ok',False)}",
  '', 'Trust audit:',
  f"sorry: {audit.get('sorry','')}",
  f"admit: {audit.get('admit','')}",
  f"global axiom: {audit.get('new_global_axiom','')}",
  f"unsafe: {audit.get('unsafe','')}",
  f"native_decide: {audit.get('native_decide','')}",
  f"Lean.ofReduceBool: {audit.get('Lean.ofReduceBool','')}",
  '', 'FA checked-in verification:',
  f"run1: {fa.get('FA_run1_exit','')}",
  f"run2: {fa.get('FA_run2_exit','')}",
  f"FA_TRUE_PASS: {fa.get('FA_TRUE_PASS',False)}",
  '', 'Downstream:',
  f"Integrated: {down.get('Integrated',down.get('classification',''))}",
  f"Mock3 bridges: {down.get('Mock3_bridges',down.get('classification',''))}",
  f"QYM: {down.get('QYM',down.get('classification',''))}",
  '', f"Final classification: {classification}", '',
  'Branches/commits:',
  f"branch: {os.environ['ACTIVE_BRANCH']}",
  f"source commit: {os.environ['SOURCE_COMMIT']}",
  f"verification HEAD: {subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()}",
  f"Workflow run URL: https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
  'Artifact ID: PENDING_UPLOAD',
]
report='\n'.join(lines)+'\n'
(final/'FA_MATRIX_PIPELINE_REPAIR_REPORT.txt').write_text(report,encoding='utf-8')
summary={
  'final_classification':classification,
  'baseline':baseline,
  'chosen':chosen,
  'candidate_results':rows,
  'checked_in_identity':identity,
  'trust_audit':audit,
  'FA_checked_in':fa,
  'downstream':down,
  'branch':os.environ['ACTIVE_BRANCH'],
  'source_commit':os.environ['SOURCE_COMMIT'],
  'workflow_run_url':f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
  'artifact_id':'PENDING_UPLOAD',
}
(final/'FINAL.json').write_text(
  json.dumps(summary,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(report)
PY

git add -f \
  "$FINAL/CHECKED_IN_IDENTITY.json" \
  "$FINAL/FA_FINAL.json" \
  "$DOWNSTREAM/DOWNSTREAM.json" \
  "$FINAL/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt" \
  "$FINAL/FINAL.json"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record FA453 checked-in direct verification [skip ci]'
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi

test "$identity_ok" = true
test -s "$SELECTED/CANDIDATE_RESULTS.json"
test -s "$CONFIRM/CONFIRMATION.json"
test -s "$FINAL/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt"
