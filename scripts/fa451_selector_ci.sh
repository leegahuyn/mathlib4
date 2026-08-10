#!/usr/bin/env bash
set -euo pipefail

BASE="build-logs/fa451-trace-deriv"
ROOTBASE="$BASE/root-baseline"
MATRIXBASE="$BASE/selector-matrix-baseline"
SELECTED="$BASE/selected"
CONFIRM="$BASE/selected-confirm"
FINAL="$BASE/final"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
ACTIVE_BRANCH="${ACTIVE_BRANCH:-fix/fa451-trace-deriv-compact-matrix-20260810}"
MAX_ERRORS="${MAX_ERRORS:-150}"
ROOT_SHA="1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a"

rm -rf "$ROOTBASE" "$MATRIXBASE" "$SELECTED" "$CONFIRM" "$FINAL"
mkdir -p "$ROOTBASE" "$MATRIXBASE" "$SELECTED" "$CONFIRM" "$FINAL"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
test "$(git config user.name)" = 'github-actions[bot]'
test "$(git config user.email)" = \
  '41898282+github-actions[bot]@users.noreply.github.com'

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
  local source="PrimalitySheafVerification/${stem}.lean"
  local olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  mkdir -p .lake/build/lib/lean/PrimalitySheafVerification
  rm -f "$olean" "$ilean"
  local command=(
    lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false
    -o "$olean" -i "$ilean" "$source"
  )
  printf '%q ' "${command[@]}" > "$d/${stem}.command"
  printf '\n' >> "$d/${stem}.command"
  touch "$d/${stem}.executed"
  set +e
  "${command[@]}" > "$d/${stem}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$d/${stem}.exit"
  if test "$rc" -eq 0 && test -s "$olean" && test -s "$ilean"; then
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
  export FA442_EXPECTED_LINES
  FA442_EXPECTED_LINES="$(python3 - <<'PY'
from pathlib import Path
data=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_bytes()
print(data.count(b'\n') + (0 if data.endswith(b'\n') else 1))
PY
)"
  export MAX_ERRORS="$cap"
  python3 scripts/fa442_record_direct_metric.py > "$d/metric-console.log" 2>&1
  cat "$d/metric-console.log"
}

# Install once for independent baselines, confirmation, checked-in x2, and downstream.
action_install "$ROOTBASE"
export PATH="${HOME}/.elan/bin:${PATH}"

# Independently compile the exact checked-in root source before candidate patches.
actual_root="$(sha256sum "$SRC" | awk '{print $1}')"
test "$actual_root" = "$ROOT_SHA"
cp "$SRC" "$ROOTBASE/Mock2_FunctionalAnalysis-root-baseline.lean"
python3 - <<'PY'
from __future__ import annotations
import importlib.util, json, sys
from pathlib import Path

root=Path.cwd()
script=root/'scripts/fa449_prepare_first_cluster.py'
spec=importlib.util.spec_from_file_location('fa451_root_meta',script)
if spec is None or spec.loader is None:
    raise SystemExit('cannot import FA449 source utilities')
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)
source=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
data=source.read_bytes()
text=data.decode('utf-8')
if mod.sha256(data) != mod.EXPECTED_SHA:
    raise SystemExit('checked-in root SHA mismatch')
header=mod.declaration_header(text,mod.TARGET_HEADER)
sequence=[m.group(1) for m in mod.DECL_RE.finditer(text)]
audit_spec=importlib.util.spec_from_file_location(
    'fa451_root_audit',root/'scripts/fa442_prepare_same_height_candidate.py'
)
audit_mod=importlib.util.module_from_spec(audit_spec)
sys.modules[audit_spec.name]=audit_mod
assert audit_spec.loader is not None
audit_spec.loader.exec_module(audit_mod)
metadata={
    'variant':'checked_in_root',
    'baseline_sha256':mod.EXPECTED_SHA,
    'candidate_sha256':mod.EXPECTED_SHA,
    'line_count':len(text.splitlines()),
    'baseline_line_count':len(text.splitlines()),
    'target_header_sha256':mod.sha256(header.encode()),
    'declaration_sequence_sha256':mod.sha256(
        json.dumps(sequence,separators=(',',':')).encode()
    ),
    'declaration_count':len(sequence),
    'baseline_forbidden_counts':audit_mod.forbidden_counts(text),
    'repairs':[],
}
Path('build-logs/fa451-trace-deriv/root-baseline/CANDIDATE.json').write_text(
    json.dumps(metadata,indent=2)+'\n',encoding='utf-8'
)
PY
metric_set "$ROOTBASE" checked_in_root "$ROOTBASE/CANDIDATE.json" "$MAX_ERRORS"

# Independently generate and compile the matrix baseline from the same root source.
cp "$ROOTBASE/Mock2_FunctionalAnalysis-root-baseline.lean" "$SRC"
python3 scripts/fa451_prepare_trace_deriv.py \
  --variant known_before_trace --output-dir "$MATRIXBASE" \
  > "$MATRIXBASE/prepare.log" 2>&1
cat "$MATRIXBASE/prepare.log"
for f in lean-version.txt lake-version.txt toolchain-install.exit cache-get.exit; do
  cp "$ROOTBASE/$f" "$MATRIXBASE/$f"
done
metric_set "$MATRIXBASE" known_before_trace "$MATRIXBASE/CANDIDATE.json" "$MAX_ERRORS"

# Download all current-run candidate artifacts and choose by direct Lean evidence.
python3 scripts/fa451_select_trace_deriv.py \
  > "$SELECTED/selector-console.log" 2>&1
cat "$SELECTED/selector-console.log"

# Require matrix baseline and independent matrix baseline to match exactly.
python3 - <<'PY'
import json
from pathlib import Path

base=Path('build-logs/fa451-trace-deriv')
ind=json.loads((base/'selector-matrix-baseline/METRIC.json').read_text())
selection=json.loads((base/'selected/SELECTION.json').read_text())
mat=selection['matrix_baseline']
fields=(
    'source_sha256','line_count','target_header_sha256',
    'declaration_sequence_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
    'FA_first_actual_error_line','FA_first_actual_error_col',
    'FA_first_error_declaration','FA_error_declaration_index',
    'FA_error_declaration_start_line',
)
mismatch={
    key:{'matrix':mat.get(key),'independent':ind.get(key)}
    for key in fields if mat.get(key)!=ind.get(key)
}
ok=(
    ind.get('all_required_lean_executed') is True
    and ind.get('Mock2_exit')==0
    and ind.get('Mock2_Advanced_exit')==0
    and ind.get('forbidden_clean') is True
    and not mismatch
)
result={
    'classification':'VERIFIED' if ok else 'INFRA_FAILURE',
    'ok':ok,
    'mismatch':mismatch,
    'metric':ind,
}
(base/'selected/INDEPENDENT_MATRIX_BASELINE.json').write_text(
    json.dumps(result,indent=2,ensure_ascii=False)+'\n'
)
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok:
    raise SystemExit('independent matrix baseline mismatch')
PY

# Materialize the strict winner, or root source if no strict progress exists.
cp "$SELECTED/Mock2_FunctionalAnalysis-selected.lean" "$SRC"
python3 - <<'PY'
import json
from pathlib import Path

base=Path('build-logs/fa451-trace-deriv')
selection=json.loads((base/'selected/SELECTION.json').read_text())
chosen=selection['chosen']
metadata={
    'variant':chosen.get('variant','checked_in_root'),
    'candidate_sha256':chosen['source_sha256'],
    'baseline_sha256':'1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a',
    'line_count':chosen['line_count'],
    'baseline_line_count':selection['root_baseline']['line_count'],
    'target_header_sha256':chosen['target_header_sha256'],
    'declaration_sequence_sha256':chosen['declaration_sequence_sha256'],
    'baseline_forbidden_counts':selection['root_baseline'].get(
        'candidate_forbidden_counts',{}
    ),
    'repairs':chosen.get('repairs',[]),
}
(base/'selected-confirm/CANDIDATE.json').write_text(
    json.dumps(metadata,indent=2)+'\n'
)
(base/'selected/SELECTED_METADATA.json').write_text(
    json.dumps(metadata,indent=2)+'\n'
)
PY
for f in lean-version.txt lake-version.txt toolchain-install.exit cache-get.exit; do
  cp "$ROOTBASE/$f" "$CONFIRM/$f"
done
SELECTED_VARIANT="$(
  python3 -c "import json; print(json.load(open('$SELECTED/SELECTION.json'))['chosen'].get('variant','checked_in_root'))"
)"
metric_set "$CONFIRM" "$SELECTED_VARIANT" "$CONFIRM/CANDIDATE.json" "$MAX_ERRORS"

# Selected source must reproduce exactly under independent direct Lean CLI.
python3 - <<'PY'
import hashlib,json
from pathlib import Path

base=Path('build-logs/fa451-trace-deriv')
selection=json.loads((base/'selected/SELECTION.json').read_text())
chosen=selection['chosen']
metric=json.loads((base/'selected-confirm/METRIC.json').read_text())
source=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
actual=hashlib.sha256(source.read_bytes()).hexdigest()
fields=(
    'source_sha256','line_count','target_header_sha256',
    'declaration_sequence_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
    'FA_first_actual_error_line','FA_first_actual_error_col',
    'FA_first_error_declaration','FA_error_declaration_index',
    'FA_error_declaration_start_line',
)
mismatch={
    key:{'matrix':chosen.get(key),'confirm':metric.get(key)}
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
    'ok':ok,
    'actual_sha256':actual,
    'mismatch':mismatch,
    'metric':metric,
}
(base/'selected-confirm/CONFIRMATION.json').write_text(
    json.dumps(result,indent=2,ensure_ascii=False)+'\n'
)
print(json.dumps(result,indent=2,ensure_ascii=False))
if not ok:
    raise SystemExit('selected FA451 candidate did not reproduce')
PY

# Persist only directly reproduced source and compact evidence.
git add "$SRC"
git add -f \
  "$ROOTBASE/METRIC.json" \
  "$MATRIXBASE/METRIC.json" \
  "$SELECTED/SELECTION.json" \
  "$SELECTED/CANDIDATE_RESULTS.json" \
  "$SELECTED/SELECTED_METADATA.json" \
  "$SELECTED/INDEPENDENT_MATRIX_BASELINE.json" \
  "$CONFIRM/METRIC.json" \
  "$CONFIRM/CONFIRMATION.json"
if ! git diff --cached --quiet; then
  git commit -m "ci: persist FA451 direct champion ${SELECTED_VARIANT} [skip ci]"
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
Path(
    'build-logs/fa451-trace-deriv/final/CHECKED_IN_IDENTITY.json'
).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
if not result['identity_ok']:
    raise SystemExit('checked-in identity mismatch')
PY

# Recompile checked-in FA twice. Both runs execute even when run 1 fails.
compile_fa_final() {
  local n="$1"
  local olean=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.olean"
  local ilean=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.ilean"
  rm -f "$olean" "$ilean"
  local command=(
    lake env lean -DmaxErrors=200 -DwarningAsError=false
    -o "$olean" -i "$ilean" "$SRC"
  )
  printf '%q ' "${command[@]}" > "$FINAL/FA-run${n}.command"
  printf '\n' >> "$FINAL/FA-run${n}.command"
  touch "$FINAL/FA-run${n}.executed"
  set +e
  "${command[@]}" > "$FINAL/FA-run${n}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$FINAL/FA-run${n}.exit"
  test -s "$olean" && printf true > "$FINAL/FA-run${n}.olean" \
    || printf false > "$FINAL/FA-run${n}.olean"
  test -s "$ilean" && printf true > "$FINAL/FA-run${n}.ilean" \
    || printf false > "$FINAL/FA-run${n}.ilean"
}
compile_fa_final 1
compile_fa_final 2

python3 - <<'PY'
import importlib.util,json,re,sys
from pathlib import Path

base=Path('build-logs/fa451-trace-deriv/final')
source=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
spec=importlib.util.spec_from_file_location(
    'fa451_audit','scripts/fa442_prepare_same_height_candidate.py'
)
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
assert spec.loader is not None
spec.loader.exec_module(mod)
audit=mod.forbidden_counts(source.read_text(encoding='utf-8'))
r1=int((base/'FA-run1.exit').read_text())
r2=int((base/'FA-run2.exit').read_text())
artifacts={
    key:(base/key).read_text()=='true'
    for key in (
        'FA-run1.olean','FA-run1.ilean','FA-run2.olean','FA-run2.ilean'
    )
}
def first_error(n):
    log=(base/f'FA-run{n}.log').read_text(errors='replace')
    match=re.search(
        r'Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+error:\s*(.*)',
        log,
    )
    return {
        'line':int(match.group(1)) if match else 0,
        'column':int(match.group(2)) if match else 0,
        'message':match.group(3)[:1000] if match else '',
    }
clean=all(value==0 for value in audit.values())
true_pass=r1==0 and r2==0 and all(artifacts.values()) and clean
result={
    'run1':r1,
    'run2':r2,
    'run1_first_error':first_error(1),
    'run2_first_error':first_error(2),
    'artifacts':artifacts,
    'trust_audit':audit,
    'forbidden_clean':clean,
    'FA_TRUE_PASS':true_pass,
}
(base/'FA_FINAL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
PY

FA_TRUE_PASS="$(
  python3 -c "import json; print(str(json.load(open('$FINAL/FA_FINAL.json'))['FA_TRUE_PASS']).lower())"
)"

# Downstream stays blocked unless checked-in FA passes twice with artifacts.
mkdir -p "$FINAL/downstream"
if test "$FA_TRUE_PASS" != true; then
  printf '%s\n' \
    '{"classification":"SKIPPED_FA_NOT_TRUE_PASS","Integrated":"SKIPPED","Mock3_bridges":"SKIPPED","QYM":"SKIPPED"}' \
    > "$FINAL/downstream/DOWNSTREAM.json"
else
  downstream_ok=true
  downstream_failure=""
  compile_downstream() {
    local stem="$1" n="$2"
    local source="PrimalitySheafVerification/${stem}.lean"
    local olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
    local ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
    local prefix="$FINAL/downstream/${stem}-run${n}"
    rm -f "$olean" "$ilean"
    local command=(
      lake env lean -DmaxErrors=100 -DwarningAsError=false
      -o "$olean" -i "$ilean" "$source"
    )
    printf '%q ' "${command[@]}" > "${prefix}.command"
    printf '\n' >> "${prefix}.command"
    touch "${prefix}.executed"
    set +e
    "${command[@]}" > "${prefix}.log" 2>&1
    local rc=$?
    set -e
    printf '%s' "$rc" > "${prefix}.exit"
    if test "$rc" -ne 0 || ! test -s "$olean" || ! test -s "$ilean"; then
      return 1
    fi
    return 0
  }

  if ! test -f PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean; then
    downstream_ok=false
    downstream_failure="Integrated source missing"
  fi
  if test "$downstream_ok" = true; then
    for n in 1 2; do
      if ! compile_downstream Mock2_FunctionalAnalysis_Integrated "$n"; then
        downstream_ok=false
        downstream_failure="Integrated run${n} failed"
        break
      fi
    done
  fi

  shopt -s nullglob
  mock3_sources=(PrimalitySheafVerification/Mock3*.lean)
  if test "$downstream_ok" = true && test "${#mock3_sources[@]}" -eq 0; then
    downstream_ok=false
    downstream_failure="Mock3 bridge sources missing"
  fi
  if test "$downstream_ok" = true; then
    for source in "${mock3_sources[@]}"; do
      stem="$(basename "$source" .lean)"
      for n in 1 2; do
        if ! compile_downstream "$stem" "$n"; then
          downstream_ok=false
          downstream_failure="${stem} run${n} failed"
          break 2
        fi
      done
    done
  fi

  if test "$downstream_ok" = true && \
     ! test -f PrimalitySheafVerification/QYM.lean; then
    downstream_ok=false
    downstream_failure="QYM source missing"
  fi
  if test "$downstream_ok" = true; then
    for n in 1 2; do
      if ! compile_downstream QYM "$n"; then
        downstream_ok=false
        downstream_failure="QYM run${n} failed"
        break
      fi
    done
  fi

  export downstream_ok downstream_failure
  python3 - <<'PY'
import json,os
from pathlib import Path

ok=os.environ['downstream_ok']=='true'
result={
    'classification':'TRUE_PASS' if ok else 'LEAN_FAILURE',
    'Integrated':'PASS_X2' if ok else 'SEE_LOGS',
    'Mock3_bridges':'PASS_X2' if ok else 'NOT_COMPLETE',
    'QYM':'PASS_X2' if ok else 'NOT_COMPLETE',
    'failure':os.environ.get('downstream_failure',''),
}
Path(
    'build-logs/fa451-trace-deriv/final/downstream/DOWNSTREAM.json'
).write_text(json.dumps(result,indent=2)+'\n')
PY
fi

# Compact machine-readable and text reports.
python3 - <<'PY'
import json,os
from pathlib import Path

base=Path('build-logs/fa451-trace-deriv')
selection=json.loads((base/'selected/SELECTION.json').read_text())
identity=json.loads((base/'final/CHECKED_IN_IDENTITY.json').read_text())
fa=json.loads((base/'final/FA_FINAL.json').read_text())
downstream=json.loads((base/'final/downstream/DOWNSTREAM.json').read_text())
final_classification=(
    'TRUE PASS'
    if fa['FA_TRUE_PASS']
    else selection['classification']
)
result={
    'classification':final_classification,
    'branch':os.environ.get(
        'ACTIVE_BRANCH','fix/fa451-trace-deriv-compact-matrix-20260810'
    ),
    'workflow_run_id':int(os.environ['GITHUB_RUN_ID']),
    'workflow_run_url':(
        f"https://github.com/{os.environ['GITHUB_REPOSITORY']}"
        f"/actions/runs/{os.environ['GITHUB_RUN_ID']}"
    ),
    'root_baseline':selection['root_baseline'],
    'matrix_baseline':selection['matrix_baseline'],
    'chosen':selection['chosen'],
    'candidate_results':selection['candidate_results'],
    'checked_in_identity':identity,
    'FA_checked_in':fa,
    'downstream':downstream,
    'evidence_artifact_id':None,
}
(base/'final/FINAL.json').write_text(
    json.dumps(result,indent=2,ensure_ascii=False)+'\n'
)
chosen=result['chosen']
rows=result['candidate_results']
lines=[
    'FA MATRIX PIPELINE REPAIR REPORT',
    '',
    'Baseline:',
    f"source SHA256: {result['root_baseline'].get('source_sha256','')}",
    f"line count: {result['root_baseline'].get('line_count','')}",
    f"direct Lean exit: {result['root_baseline'].get('FA_exit','')}",
    (
        f"first error: {result['root_baseline'].get('FA_first_actual_error_line',0)}:"
        f"{result['root_baseline'].get('FA_first_actual_error_col',0)}"
    ),
    f"declaration: {result['root_baseline'].get('FA_first_error_declaration','')}",
    '',
    'Pipeline issue found:',
    'root cause: FA451 was initially committed with [skip ci]; this run uses a real trigger, complete direct candidate metrics, an independent root baseline, selector confirmation, checked-in identity, and x2 verification.',
    'workflow files changed: .github/workflows/pre-commit.yml',
    'scripts changed: scripts/fa451_candidate_ci.sh; scripts/fa451_prepare_trace_deriv.py; scripts/fa451_select_trace_deriv.py; scripts/fa451_selector_ci.sh',
    '',
    'Candidate results:',
    'variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification',
]
for row in rows:
    lines.append(
        f"{row.get('variant')} | {row.get('SHA256')} | "
        f"{row.get('all_required_lean_executed')} | {row.get('FA_exit')} | "
        f"{row.get('first_line')}:{row.get('first_col')} | "
        f"{row.get('declaration')} | {row.get('classification')}"
    )
lines += [
    '',
    'Best direct-verified candidate:',
    f"variant: {chosen.get('variant','')}",
    f"SHA256: {chosen.get('source_sha256','')}",
    f"exit: {chosen.get('FA_exit','')}",
    (
        f"first error: {chosen.get('FA_first_actual_error_line',0)}:"
        f"{chosen.get('FA_first_actual_error_col',0)}"
    ),
    f"declaration: {chosen.get('FA_first_error_declaration','')}",
    f"strictly better than 33624: {selection['classification']=='STRICT_PROMOTION'}",
    '',
    'Checked-in identity:',
    f"selected SHA: {identity.get('selected_sha','')}",
    f"worktree SHA: {identity.get('worktree_sha','')}",
    f"HEAD source SHA: {identity.get('HEAD_source_sha','')}",
    f"identity_ok: {identity.get('identity_ok')}",
    '',
    'Trust audit:',
]
for key,value in fa.get('trust_audit',{}).items():
    lines.append(f"{key}: {value}")
lines += [
    '',
    'FA checked-in verification:',
    f"run1: {fa.get('run1')}",
    f"run2: {fa.get('run2')}",
    f"FA_TRUE_PASS: {fa.get('FA_TRUE_PASS')}",
    '',
    'Downstream:',
    f"Integrated: {downstream.get('Integrated')}",
    f"Mock3 bridges: {downstream.get('Mock3_bridges')}",
    f"QYM: {downstream.get('QYM')}",
    '',
    f"Final classification: {final_classification}",
    '',
    'Branches/commits:',
    f"branch: {result['branch']}",
    f"source commit: {identity.get('commit','')}",
    f"Workflow run URL: {result['workflow_run_url']}",
    'Artifact ID: PENDING_UPLOAD_PATCH',
]
(base/'final/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt').write_text(
    '\n'.join(lines)+'\n',encoding='utf-8'
)
print(json.dumps(result,indent=2,ensure_ascii=False))
PY

git add -f \
  "$FINAL/CHECKED_IN_IDENTITY.json" \
  "$FINAL/FA_FINAL.json" \
  "$FINAL/downstream/DOWNSTREAM.json" \
  "$FINAL/FINAL.json" \
  "$FINAL/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record FA451 checked-in verification [skip ci]'
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi
