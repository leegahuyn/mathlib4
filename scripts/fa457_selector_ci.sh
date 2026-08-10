#!/usr/bin/env bash
set -euo pipefail

BASE="build-logs/fa457-true-first"
SELBASE="$BASE/selector-baseline"
SELECTED="$BASE/selected"
CONFIRM="$BASE/selected-confirm"
FINAL="$BASE/final"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
ACTIVE_BRANCH="${ACTIVE_BRANCH:-fix/fa457-true-error-parser-paired-matrix-20260810}"
MAX_ERRORS="${MAX_ERRORS:-300}"
mkdir -p "$SELBASE" "$SELECTED" "$CONFIRM" "$FINAL"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
test "$(git config user.name)" = 'github-actions[bot]'
test "$(git config user.email)" = \
  '41898282+github-actions[bot]@users.noreply.github.com'

# Install the corrected parser in the checked-in branch before any selection.
python3 scripts/fa457_patch_metric_parser.py | tee "$FINAL/parser-patch.log"
python3 -m py_compile scripts/fa442_record_direct_metric.py
git add scripts/fa442_record_direct_metric.py
if ! git diff --cached --quiet; then
  git commit -m 'ci: parse coded Lean errors in direct metrics [skip ci]'
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi
PARSER_COMMIT="$(git rev-parse HEAD)"

install_toolchain() {
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
    printf true > "$d/${stem}.artifacts_ok"
  else
    printf false > "$d/${stem}.artifacts_ok"
  fi
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
  python3 scripts/fa442_record_direct_metric.py > "$d/metric-console.log" 2>&1
  cat "$d/metric-console.log"
}

# The selector independently installs Lean and recompiles the exact current baseline.
install_toolchain "$SELBASE"
export PATH="${HOME}/.elan/bin:${PATH}"
python3 scripts/fa457_prepare_true_first.py \
  --variant true_baseline --output-dir "$SELBASE" \
  > "$SELBASE/prepare.log" 2>&1
cat "$SELBASE/prepare.log"
metric_set "$SELBASE" true_baseline "$SELBASE/CANDIDATE.json" "$MAX_ERRORS"

# Select from current-run artifacts only.
python3 scripts/fa457_select_true_first.py > "$SELECTED/selector-console.log" 2>&1
cat "$SELECTED/selector-console.log"

# Matrix baseline and independent selector baseline must be identical.
python3 - <<'PY'
import json
from pathlib import Path
base=Path('build-logs/fa457-true-first')
ind=json.loads((base/'selector-baseline/METRIC.json').read_text())
selection=json.loads((base/'selected/SELECTION.json').read_text())
mat=selection['baseline']
fields=(
  'source_sha256','line_count','target_header_sha256',
  'declaration_sequence_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
  'FA_first_actual_error_line','FA_first_actual_error_col','FA_first_error_code',
  'FA_first_error_declaration','FA_error_declaration_index',
)
mismatch={k:{'matrix':mat.get(k),'independent':ind.get(k)} for k in fields if mat.get(k)!=ind.get(k)}
ok=(
  ind.get('all_required_lean_executed') is True
  and ind.get('source_sha256')=='1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb'
  and ind.get('Mock2_exit')==0 and ind.get('Mock2_Advanced_exit')==0
  and ind.get('FA_exit')==1
  and ind.get('FA_first_actual_error_line')==32035
  and ind.get('FA_first_actual_error_col')==79
  and ind.get('FA_first_error_code')=='lean.invalidField'
  and ind.get('FA_first_error_declaration')=='nativeActualEdgeFluxIntegral_paired_circular'
  and not mismatch
)
result={'classification':'VERIFIED' if ok else 'INFRA_FAILURE','ok':ok,'mismatch':mismatch,'metric':ind}
(base/'selected/INDEPENDENT_BASELINE.json').write_text(
  json.dumps(result,indent=2,ensure_ascii=False)+'\n'
)
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok: raise SystemExit('independent fixed-parser baseline mismatch')
PY

# Materialize the selected source and build confirmation metadata.
cp "$SELECTED/Mock2_FunctionalAnalysis-selected.lean" "$SRC"
python3 - <<'PY'
import json
from pathlib import Path
base=Path('build-logs/fa457-true-first')
selection=json.loads((base/'selected/SELECTION.json').read_text())
chosen=selection['chosen']
metadata={
 'variant':chosen.get('variant','true_baseline'),
 'candidate_sha256':chosen['source_sha256'],
 'baseline_sha256':'1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb',
 'line_count':chosen['line_count'],
 'target_header_sha256':chosen['target_header_sha256'],
 'declaration_sequence_sha256':chosen['declaration_sequence_sha256'],
 'baseline_forbidden_counts':selection['baseline'].get('candidate_forbidden_counts',{}),
 'repairs':chosen.get('repairs',[]),
}
(base/'selected-confirm/CANDIDATE.json').write_text(json.dumps(metadata,indent=2)+'\n')
(base/'selected/SELECTED_METADATA.json').write_text(json.dumps(metadata,indent=2)+'\n')
PY
for file in lean-version.txt lake-version.txt toolchain-install.exit cache-get.exit; do
  cp "$SELBASE/$file" "$CONFIRM/$file"
done
SELECTED_VARIANT="$(python3 -c "import json; print(json.load(open('$SELECTED/SELECTION.json'))['chosen']['variant'])")"
metric_set "$CONFIRM" "$SELECTED_VARIANT" "$CONFIRM/CANDIDATE.json" "$MAX_ERRORS"

# Matrix result must reproduce after materialization.
python3 - <<'PY'
import hashlib,json
from pathlib import Path
base=Path('build-logs/fa457-true-first')
selection=json.loads((base/'selected/SELECTION.json').read_text())
chosen=selection['chosen']
metric=json.loads((base/'selected-confirm/METRIC.json').read_text())
src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
actual=hashlib.sha256(src.read_bytes()).hexdigest()
fields=(
 'source_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
 'FA_first_actual_error_line','FA_first_actual_error_col','FA_first_error_code',
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
(base/'selected-confirm/CONFIRMATION.json').write_text(
 json.dumps(result,indent=2,ensure_ascii=False)+'\n'
)
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok: raise SystemExit('selected source did not reproduce fixed-parser metric')
PY

# Persist the official champion only after direct reproduction.
git add "$SRC" scripts/fa442_record_direct_metric.py
git add -f \
  "$SELECTED/SELECTION.json" \
  "$SELECTED/CANDIDATE_RESULTS.json" \
  "$SELECTED/SELECTED_METADATA.json" \
  "$SELECTED/INDEPENDENT_BASELINE.json" \
  "$CONFIRM/METRIC.json" \
  "$CONFIRM/CONFIRMATION.json"
if ! git diff --cached --quiet; then
  git commit -m "ci: persist FA457 fixed-parser champion ${SELECTED_VARIANT} [skip ci]"
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
export selected_sha worktree_sha head_sha identity_ok SOURCE_COMMIT PARSER_COMMIT
python3 - <<'PY'
import json,os
from pathlib import Path
result={
 'selected_sha':os.environ['selected_sha'],
 'worktree_sha':os.environ['worktree_sha'],
 'HEAD_source_sha':os.environ['head_sha'],
 'identity_ok':os.environ['identity_ok']=='true',
 'source_commit':os.environ['SOURCE_COMMIT'],
 'parser_commit':os.environ['PARSER_COMMIT'],
}
Path('build-logs/fa457-true-first/final/CHECKED_IN_IDENTITY.json').write_text(
 json.dumps(result,indent=2)+'\n'
)
print(json.dumps(result,indent=2))
if not result['identity_ok']: raise SystemExit('checked-in identity mismatch')
PY

# Checked-in FA direct compile run 1 and run 2.
compile_fa_final() {
  local n="$1"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean -DmaxErrors=300 -DwarningAsError=false \
    -o "$o" -i "$i" "$SRC")
  printf '%q ' "${command[@]}" > "$FINAL/FA-run${n}.command"
  printf '\n' >> "$FINAL/FA-run${n}.command"
  touch "$FINAL/FA-run${n}.executed"
  set +e
  "${command[@]}" > "$FINAL/FA-run${n}.log" 2>&1
  local rc=$?
  set -e
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
module=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=module
assert spec.loader is not None
spec.loader.exec_module(module)
base=Path('build-logs/fa457-true-first/final')
audit=module.forbidden_counts(Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text())
r1=int((base/'FA-run1.exit').read_text())
r2=int((base/'FA-run2.exit').read_text())
artifacts={name:(base/name).read_text()=='true' for name in (
 'FA-run1.olean','FA-run1.ilean','FA-run2.olean','FA-run2.ilean'
)}
clean=all(value==0 for value in audit.values())
true_pass=r1==0 and r2==0 and all(artifacts.values()) and clean
result={'run1':r1,'run2':r2,'artifacts':artifacts,'trust_audit':audit,'FA_TRUE_PASS':true_pass}
(base/'FA_FINAL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
PY
FA_TRUE_PASS="$(python3 -c "import json; print(str(json.load(open('$FINAL/FA_FINAL.json'))['FA_TRUE_PASS']).lower())")"

# Downstream remains strictly gated by checked-in FA TRUE PASS x2.
DOWNSTREAM="$FINAL/downstream"
mkdir -p "$DOWNSTREAM"
if test "$FA_TRUE_PASS" = true; then
  downstream_complete=true
  downstream_failure=''
  downstream_compile() {
    local stem="$1" n="$2"
    local src="PrimalitySheafVerification/${stem}.lean"
    local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
    local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
    rm -f "$o" "$i"
    local command=(lake env lean -DmaxErrors=300 -DwarningAsError=false \
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
    downstream_compile "$stem" 1 || { downstream_complete=false; downstream_failure="${stem}-run1"; return 1; }
    downstream_compile "$stem" 2 || { downstream_complete=false; downstream_failure="${stem}-run2"; return 1; }
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
base=Path('build-logs/fa457-true-first/final/downstream')
exits={}
for path in sorted(base.glob('*.exit')):
    try: exits[path.name]=int(path.read_text())
    except ValueError: exits[path.name]=125
result={
 'classification':'TRUE_PASS' if os.environ['downstream_complete']=='true' else 'LEAN_FAILURE',
 'complete':os.environ['downstream_complete']=='true',
 'failure':os.environ['downstream_failure'],
 'ordered_exits':exits,
}
(base/'DOWNSTREAM.json').write_text(json.dumps(result,indent=2)+'\n')
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

# Compact final evidence; upload step later adds artifact identity.
export ACTIVE_BRANCH SOURCE_COMMIT PARSER_COMMIT
python3 - <<'PY'
import json,os
from pathlib import Path
base=Path('build-logs/fa457-true-first')
selection=json.loads((base/'selected/SELECTION.json').read_text())
identity=json.loads((base/'final/CHECKED_IN_IDENTITY.json').read_text())
fa=json.loads((base/'final/FA_FINAL.json').read_text())
downstream=json.loads((base/'final/downstream/DOWNSTREAM.json').read_text())
classification='TRUE PASS' if fa['FA_TRUE_PASS'] else selection['classification']
result={
 'classification':classification,
 'baseline':selection['baseline'],
 'chosen':selection['chosen'],
 'candidate_results':selection['candidate_results'],
 'checked_in':identity,
 'FA_checked_in':fa,
 'downstream':downstream,
 'branch':os.environ['ACTIVE_BRANCH'],
 'source_commit':os.environ['SOURCE_COMMIT'],
 'parser_commit':os.environ['PARSER_COMMIT'],
 'workflow_run_url':f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
 'artifact_id':'PENDING_UPLOAD',
}
(base/'final/FINAL.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
PY

git add -f \
  "$FINAL/CHECKED_IN_IDENTITY.json" \
  "$FINAL/FA_FINAL.json" \
  "$FINAL/downstream/DOWNSTREAM.json" \
  "$FINAL/FINAL.json"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record FA457 fixed-parser checked-in evidence [skip ci]'
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi

test "$identity_ok" = true
test -s "$SELECTED/CANDIDATE_RESULTS.json"
test -s "$CONFIRM/CONFIRMATION.json"
test -s "$FINAL/FINAL.json"
