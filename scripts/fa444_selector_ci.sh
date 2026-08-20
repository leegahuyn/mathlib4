#!/usr/bin/env bash
set -euo pipefail

ACTIVE_BRANCH="${ACTIVE_BRANCH:-fix/fa444-fa442-matrix-pipeline-repair-20260810}"
MAX_ERRORS="${MAX_ERRORS:-100}"
BASE="build-logs/fa442-pipeline-repair"
BASELINE_DIR="$BASE/selector-baseline"
SELECTED_DIR="$BASE/selected"
CONFIRM_DIR="$BASE/selected-confirm"
FINAL_DIR="$BASE/final"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
mkdir -p "$BASELINE_DIR" "$SELECTED_DIR" "$CONFIRM_DIR" "$FINAL_DIR"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
test "$(git config user.name)" = 'github-actions[bot]'
test "$(git config user.email)" = \
  '41898282+github-actions[bot]@users.noreply.github.com'

install_toolchain() {
  local d="$1"
  curl --retry 5 --retry-all-errors --fail --silent --show-error \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -o /tmp/elan-init.sh > "$d/elan-download.log" 2>&1
  sh /tmp/elan-init.sh -y --default-toolchain none \
    > "$d/elan-init.log" 2>&1
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
  if test "$rc" -eq 0 && test -s "$o" && test -s "$i"; then
    printf 'true\n' > "$d/${stem}.artifacts_ok"
  else
    printf 'false\n' > "$d/${stem}.artifacts_ok"
  fi
}

compile_metric_set() {
  local d="$1"
  local variant="$2"
  local metadata="$3"
  local cap="$4"
  compile_one "$d" Mock2 "$cap"
  compile_one "$d" Mock2_Advanced "$cap"
  compile_one "$d" Mock2_FunctionalAnalysis "$cap"
  export VARIANT="$variant"
  export FA442_OUT_DIR="$d"
  export FA442_SOURCE="$SRC"
  export FA442_METADATA="$metadata"
  export MAX_ERRORS="$cap"
  python3 scripts/fa442_record_direct_metric.py \
    > "$d/metric-console.log" 2>&1
  cat "$d/metric-console.log"
}

# The selector never trusts matrix metadata alone. It installs Lean and recompiles baseline.
install_toolchain "$BASELINE_DIR"
export PATH="${HOME}/.elan/bin:${PATH}"
python3 scripts/fa442_restore_authoritative_baseline.py \
  --output-dir "$BASELINE_DIR" > "$BASELINE_DIR/baseline-recovery.log" 2>&1
cat "$BASELINE_DIR/baseline-recovery.log"
python3 scripts/fa442_prepare_same_height_candidate.py \
  --variant baseline --output-dir "$BASELINE_DIR" \
  > "$BASELINE_DIR/prepare.log" 2>&1
cat "$BASELINE_DIR/prepare.log"
compile_metric_set "$BASELINE_DIR" baseline "$BASELINE_DIR/CANDIDATE.json" "$MAX_ERRORS"

# Download all current-run matrix artifacts, require a complete baseline, and select strictly.
python3 scripts/fa442_select_strict_champion.py \
  > "$SELECTED_DIR/selector-console.log" 2>&1
cat "$SELECTED_DIR/selector-console.log"

readarray -t selection_values < <(python3 - <<'PY'
import json
from pathlib import Path
s=json.loads(Path('build-logs/fa442-pipeline-repair/selected/SELECTION.json').read_text())
c=s['chosen']
print(c.get('variant','baseline'))
print(c.get('source_sha256',''))
print(c.get('FA_exit',125))
print(c.get('FA_first_actual_error_line',0))
print(c.get('FA_first_actual_error_col',0))
print(c.get('FA_first_error_declaration',''))
print(c.get('FA_error_declaration_index',-1))
print(s.get('selection_mode',''))
print(s.get('chosen_progress_classification',''))
PY
)
SELECTED_VARIANT="${selection_values[0]}"
SELECTED_SHA="${selection_values[1]}"
MATRIX_FA_EXIT="${selection_values[2]}"
MATRIX_FIRST_LINE="${selection_values[3]}"
MATRIX_FIRST_COL="${selection_values[4]}"
MATRIX_DECLARATION="${selection_values[5]}"
MATRIX_DECLARATION_INDEX="${selection_values[6]}"
SELECTION_MODE="${selection_values[7]}"
PROGRESS_CLASSIFICATION="${selection_values[8]}"

# Materialize the selected bytes at the repository path and reproduce the direct metric.
rm -rf "$CONFIRM_DIR"
mkdir -p "$CONFIRM_DIR"
cp "$SELECTED_DIR/Mock2_FunctionalAnalysis-selected.lean" "$SRC"
cp "$SELECTED_DIR/SELECTED_METADATA.json" "$CONFIRM_DIR/CANDIDATE.json"
for evidence in lean-version.txt lake-version.txt toolchain-install.exit cache-get.exit; do
  cp "$BASELINE_DIR/$evidence" "$CONFIRM_DIR/$evidence"
done
compile_metric_set "$CONFIRM_DIR" "$SELECTED_VARIANT" \
  "$CONFIRM_DIR/CANDIDATE.json" "$MAX_ERRORS"

export SELECTED_VARIANT SELECTED_SHA MATRIX_FA_EXIT MATRIX_FIRST_LINE
export MATRIX_FIRST_COL MATRIX_DECLARATION MATRIX_DECLARATION_INDEX
python3 - <<'PY'
import hashlib,json,os
from pathlib import Path

d=Path('build-logs/fa442-pipeline-repair/selected-confirm')
src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
metric=json.loads((d/'METRIC.json').read_text(encoding='utf-8'))
actual=hashlib.sha256(src.read_bytes()).hexdigest()
expected={
    'source_sha256':os.environ['SELECTED_SHA'],
    'FA_exit':int(os.environ['MATRIX_FA_EXIT']),
    'FA_first_actual_error_line':int(os.environ['MATRIX_FIRST_LINE']),
    'FA_first_actual_error_col':int(os.environ['MATRIX_FIRST_COL']),
    'FA_first_error_declaration':os.environ['MATRIX_DECLARATION'],
    'FA_error_declaration_index':int(os.environ['MATRIX_DECLARATION_INDEX']),
}
mismatches={
    key:{'expected':value,'actual':metric.get(key)}
    for key,value in expected.items() if metric.get(key)!=value
}
verified=(
    actual==os.environ['SELECTED_SHA']
    and metric.get('classification')!='INFRA_FAILURE'
    and metric.get('all_required_lean_executed') is True
    and metric.get('Mock2_exit')==0
    and metric.get('Mock2_Advanced_exit')==0
    and metric.get('forbidden_clean') is True
    and not mismatches
)
result={
    'classification':'VERIFIED' if verified else 'INFRA_FAILURE',
    'verified':verified,
    'selected_variant':os.environ['SELECTED_VARIANT'],
    'selected_sha256':os.environ['SELECTED_SHA'],
    'materialized_sha256':actual,
    'mismatches':mismatches,
    'direct_metric':metric,
}
(d/'CONFIRMATION.json').write_text(
    json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8'
)
(d/'CONFIRMATION.txt').write_text(
    '\n'.join(f'{k}={v}' for k,v in result.items())+'\n',encoding='utf-8'
)
print(json.dumps(result,indent=2,ensure_ascii=False))
if not verified:
    raise SystemExit('INFRA_FAILURE: selected metric did not independently reproduce')
PY

# Persist only independently reproduced bytes. No master push and no merge operation.
git add "$SRC"
git add -f \
  "$SELECTED_DIR/SELECTION.json" \
  "$SELECTED_DIR/CANDIDATE_RESULTS.json" \
  "$SELECTED_DIR/CANDIDATE_RESULTS.tsv" \
  "$SELECTED_DIR/SELECTED_METADATA.json" \
  "$CONFIRM_DIR/METRIC.json" \
  "$CONFIRM_DIR/CONFIRMATION.json" \
  "$CONFIRM_DIR/CONFIRMATION.txt"
if ! git diff --cached --quiet; then
  git commit -m \
    "ci: persist FA444 direct selection ${SELECTED_VARIANT} ${SELECTED_SHA:0:12} [skip ci]"
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi
SOURCE_COMMIT="$(git rev-parse HEAD)"

selected_sha="$(sha256sum "$SELECTED_DIR/Mock2_FunctionalAnalysis-selected.lean" | awk '{print $1}')"
worktree_sha="$(sha256sum "$SRC" | awk '{print $1}')"
head_sha="$(git show "HEAD:${SRC}" | sha256sum | awk '{print $1}')"
identity_ok=false
if test "$selected_sha" = "$SELECTED_SHA" && \
   test "$worktree_sha" = "$SELECTED_SHA" && \
   test "$head_sha" = "$SELECTED_SHA"; then
  identity_ok=true
fi
export selected_sha worktree_sha head_sha identity_ok SOURCE_COMMIT
python3 - <<'PY'
import json,os
from pathlib import Path
result={
    'selected_sha256':os.environ['selected_sha'],
    'worktree_sha256':os.environ['worktree_sha'],
    'head_source_sha256':os.environ['head_sha'],
    'identity_ok':os.environ['identity_ok']=='true',
    'head_commit':os.environ['SOURCE_COMMIT'],
}
p=Path('build-logs/fa442-pipeline-repair/final')
(p/'CHECKED_IN_IDENTITY.json').write_text(json.dumps(result,indent=2)+'\n')
(p/'CHECKED_IN_IDENTITY.txt').write_text(
    '\n'.join(f'{k}={v}' for k,v in result.items())+'\n'
)
print(json.dumps(result,indent=2))
if not result['identity_ok']:
    raise SystemExit('INFRA_FAILURE: selected/worktree/HEAD source identity mismatch')
PY

# Checked-in FA must compile twice; proof failure is recorded, not disguised as infra success.
compile_fa_run() {
  local n="$1"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean "-DmaxErrors=${MAX_ERRORS}" -DwarningAsError=false \
    -o "$o" -i "$i" "$SRC")
  printf '%q ' "${command[@]}" > "$FINAL_DIR/FA-run${n}.command"
  printf '\n' >> "$FINAL_DIR/FA-run${n}.command"
  touch "$FINAL_DIR/FA-run${n}.executed"
  set +e
  "${command[@]}" > "$FINAL_DIR/FA-run${n}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$FINAL_DIR/FA-run${n}.exit"
  test -s "$o" && printf 'true' > "$FINAL_DIR/FA-run${n}.olean" \
    || printf 'false' > "$FINAL_DIR/FA-run${n}.olean"
  test -s "$i" && printf 'true' > "$FINAL_DIR/FA-run${n}.ilean" \
    || printf 'false' > "$FINAL_DIR/FA-run${n}.ilean"
}
compile_fa_run 1
compile_fa_run 2

python3 - <<'PY'
import importlib.util,json,sys
from pathlib import Path
spec=importlib.util.spec_from_file_location(
    'fa442_audit','scripts/fa442_prepare_same_height_candidate.py'
)
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
assert spec.loader is not None
spec.loader.exec_module(mod)
root=Path('build-logs/fa442-pipeline-repair/final')
text=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text()
audit=mod.forbidden_counts(text)
r1=int((root/'FA-run1.exit').read_text())
r2=int((root/'FA-run2.exit').read_text())
artifacts={
    'run1_olean':(root/'FA-run1.olean').read_text()=='true',
    'run1_ilean':(root/'FA-run1.ilean').read_text()=='true',
    'run2_olean':(root/'FA-run2.olean').read_text()=='true',
    'run2_ilean':(root/'FA-run2.ilean').read_text()=='true',
}
clean=all(v==0 for v in audit.values())
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
    json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8'
)
print(json.dumps(result,indent=2,ensure_ascii=False))
PY
FA_TRUE_PASS="$(python3 -c "import json; print(str(json.load(open('$FINAL_DIR/FA_FINAL.json'))['FA_TRUE_PASS']).lower())")"

# Downstream is strictly gated by checked-in FA TRUE PASS x2.
DOWNSTREAM_DIR="$FINAL_DIR/downstream"
mkdir -p "$DOWNSTREAM_DIR"
if test "$FA_TRUE_PASS" = true; then
  downstream_complete=true
  downstream_failure=''
  downstream_compile() {
    local stem="$1"
    local n="$2"
    local src="PrimalitySheafVerification/${stem}.lean"
    local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
    local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
    rm -f "$o" "$i"
    local command=(lake env lean "-DmaxErrors=${MAX_ERRORS}" -DwarningAsError=false \
      -o "$o" -i "$i" "$src")
    printf '%q ' "${command[@]}" > "$DOWNSTREAM_DIR/${stem}-run${n}.command"
    printf '\n' >> "$DOWNSTREAM_DIR/${stem}-run${n}.command"
    touch "$DOWNSTREAM_DIR/${stem}-run${n}.executed"
    set +e
    "${command[@]}" > "$DOWNSTREAM_DIR/${stem}-run${n}.log" 2>&1
    local rc=$?
    set -e
    printf '%s' "$rc" > "$DOWNSTREAM_DIR/${stem}-run${n}.exit"
    test "$rc" -eq 0 && test -s "$o" && test -s "$i"
  }
  run_twice() {
    local stem="$1"
    if ! downstream_compile "$stem" 1; then
      downstream_complete=false; downstream_failure="${stem}-run1"; return 1
    fi
    if ! downstream_compile "$stem" 2; then
      downstream_complete=false; downstream_failure="${stem}-run2"; return 1
    fi
  }
  if test -f PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean; then
    run_twice Mock2_FunctionalAnalysis_Integrated || true
  else
    downstream_complete=false; downstream_failure='Integrated-missing'
  fi
  if test "$downstream_complete" = true; then
    shopt -s nullglob
    bridges=(PrimalitySheafVerification/Mock3*.lean)
    if test "${#bridges[@]}" -eq 0; then
      downstream_complete=false; downstream_failure='Mock3-bridges-missing'
    else
      for bridge in "${bridges[@]}"; do
        run_twice "$(basename "$bridge" .lean)" || break
      done
    fi
  fi
  if test "$downstream_complete" = true; then
    if test -f PrimalitySheafVerification/QYM.lean; then
      run_twice QYM || true
    else
      downstream_complete=false; downstream_failure='QYM-missing'
    fi
  fi
  export downstream_complete downstream_failure
  python3 - <<'PY'
import json,os
from pathlib import Path
d=Path('build-logs/fa442-pipeline-repair/final/downstream')
exits={}
for path in sorted(d.glob('*.exit')):
    try: exits[path.name]=int(path.read_text())
    except ValueError: exits[path.name]=125
result={
    'classification':'TRUE_PASS' if os.environ['downstream_complete']=='true' else 'LEAN_FAILURE',
    'complete':os.environ['downstream_complete']=='true',
    'failure':os.environ['downstream_failure'],
    'ordered_exits':exits,
}
(d/'DOWNSTREAM.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
PY
else
  cat > "$DOWNSTREAM_DIR/DOWNSTREAM.json" <<'JSON'
{
  "classification": "SKIPPED_FA_NOT_TRUE_PASS",
  "complete": false,
  "Integrated": "SKIPPED",
  "Mock3_bridges": "SKIPPED",
  "QYM": "SKIPPED"
}
JSON
fi

# Produce the requested human-readable report before upload; artifact ID is patched later.
export ACTIVE_BRANCH SELECTION_MODE PROGRESS_CLASSIFICATION SOURCE_COMMIT
python3 - <<'PY'
import json,os,subprocess
from pathlib import Path
base=Path('build-logs/fa442-pipeline-repair')
final=base/'final'
selection=json.loads((base/'selected/SELECTION.json').read_text())
identity=json.loads((final/'CHECKED_IN_IDENTITY.json').read_text())
fa=json.loads((final/'FA_FINAL.json').read_text())
down=json.loads((final/'downstream/DOWNSTREAM.json').read_text())
baseline=selection['baseline']; chosen=selection['chosen']; rows=selection['candidate_results']
if fa.get('FA_TRUE_PASS') and down.get('complete'):
    classification='TRUE PASS'
elif selection.get('selection_mode')=='strict_promotion':
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
"root cause: the FA442 prepare step compared the checked-in promoted SHA 885e585d... against the authoritative baseline 71dc36f... and emitted ok=false; both Lean installation and direct compilation were guarded by if: steps.prepare.outputs.ok == 'true', so they were skipped. The selector therefore received zero baseline direct metrics. Git identity lived in a later install step, which was also skipped after selector failure.",
'workflow files changed: .github/workflows/fa442-same-height-slope-cumulative.yml; .github/workflows/pre-commit.yml',
'scripts changed: scripts/fa442_restore_authoritative_baseline.py; scripts/fa442_record_direct_metric.py; scripts/fa442_select_strict_champion.py; scripts/fa444_candidate_ci.sh; scripts/fa444_selector_ci.sh','',
'Candidate results:',
'variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification']
for row in rows:
    lines.append(
        f"{row.get('variant')} | {row.get('source_sha256')} | {row.get('Lean_executed')} | "
        f"{row.get('FA_exit')} | {row.get('first_line')}:{row.get('first_col')} | "
        f"{row.get('declaration')} | {row.get('classification')}"
    )
lines += ['', 'Best direct-verified candidate:',
f"variant: {chosen.get('variant','')}",
f"SHA256: {chosen.get('source_sha256','')}",
f"exit: {chosen.get('FA_exit','')}",
f"first error: {chosen.get('FA_first_actual_error_line',0)}:{chosen.get('FA_first_actual_error_col',0)} {chosen.get('FA_first_error_message','')}",
f"declaration: {chosen.get('FA_first_error_declaration','')}",
f"strictly better than 31726?: {selection.get('selection_mode')=='strict_promotion'}",'',
'Checked-in identity:',
f"selected SHA: {identity.get('selected_sha256','')}",
f"worktree SHA: {identity.get('worktree_sha256','')}",
f"HEAD source SHA: {identity.get('head_source_sha256','')}",
f"identity_ok: {identity.get('identity_ok',False)}",'',
'Trust audit:',
f"sorry: {audit.get('sorry','')}",f"admit: {audit.get('admit','')}",
f"global axiom: {audit.get('new_global_axiom','')}",f"unsafe: {audit.get('unsafe','')}",
f"native_decide: {audit.get('native_decide','')}",f"Lean.ofReduceBool: {audit.get('Lean.ofReduceBool','')}",'',
'FA checked-in verification:',f"run1: {fa.get('FA_run1_exit','')}",f"run2: {fa.get('FA_run2_exit','')}",
f"FA_TRUE_PASS: {fa.get('FA_TRUE_PASS',False)}",'',
'Downstream:',f"Integrated: {down.get('Integrated',down.get('classification',''))}",
f"Mock3 bridges: {down.get('Mock3_bridges',down.get('classification',''))}",
f"QYM: {down.get('QYM',down.get('classification',''))}",'',
f"Final classification: {classification}",'',
'Branches/commits:',f"branch: {os.environ['ACTIVE_BRANCH']}",f"source commit: {os.environ['SOURCE_COMMIT']}",
f"verification HEAD: {subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()}",
f"Workflow run URL: https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
'Artifact ID: PENDING_UPLOAD']
report='\n'.join(lines)+'\n'
(final/'FA_MATRIX_PIPELINE_REPAIR_REPORT.txt').write_text(report)
summary={
    'final_classification':classification,'baseline':baseline,'chosen':chosen,
    'identity':identity,'trust_audit':audit,'FA_checked_in':fa,'downstream':down,
    'branch':os.environ['ACTIVE_BRANCH'],'source_commit':os.environ['SOURCE_COMMIT'],
    'workflow_run_url':f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
    'artifact_id':'PENDING_UPLOAD',
}
(final/'FINAL.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
print(report)
PY

# Persist compact final evidence with a configured identity. Logs remain in the artifact.
git add -f \
  "$FINAL_DIR/CHECKED_IN_IDENTITY.json" \
  "$FINAL_DIR/CHECKED_IN_IDENTITY.txt" \
  "$FINAL_DIR/FA_FINAL.json" \
  "$FINAL_DIR/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt" \
  "$FINAL_DIR/FINAL.json" \
  "$DOWNSTREAM_DIR/DOWNSTREAM.json"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record FA444 matrix and checked-in verification evidence [skip ci]'
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi

# Pipeline integrity is separate from Lean proof status.
test "$identity_ok" = true
test -s "$SELECTED_DIR/CANDIDATE_RESULTS.json"
test -s "$CONFIRM_DIR/CONFIRMATION.json"
test -s "$FINAL_DIR/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt"
