#!/usr/bin/env bash
set -euo pipefail

BASE="build-logs/fa452-compact-energy"
ROOTBASE="$BASE/selector-root-baseline"
SELECTED="$BASE/selected"
CONFIRM="$BASE/selected-confirm"
FINAL="$BASE/final"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
ACTIVE_BRANCH="${ACTIVE_BRANCH:-fix/fa452-compact-support-energy-matrix-20260810}"
MAX_ERRORS="${MAX_ERRORS:-220}"
mkdir -p "$ROOTBASE" "$SELECTED" "$CONFIRM" "$FINAL" "$FINAL/downstream"

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
  printf '%s' "$(test -s "$o" && stat -c%s "$o" || echo 0)" > "$d/${stem}.olean.size"
  printf '%s' "$(test -s "$i" && stat -c%s "$i" || echo 0)" > "$d/${stem}.ilean.size"
}

metric_set() {
  local d="$1"
  local variant="$2"
  local metadata="$3"
  local cap="$4"
  compile_one "$d" Mock2 60
  compile_one "$d" Mock2_Advanced 60
  compile_one "$d" Mock2_FunctionalAnalysis "$cap"
  export VARIANT="$variant"
  export FA442_OUT_DIR="$d"
  export FA442_SOURCE="$SRC"
  export FA442_METADATA="$metadata"
  export FA442_EXPECTED_LINES="$(python3 - <<'PY'
from pathlib import Path
p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
d=p.read_bytes()
print(d.count(b'\n') + (0 if d.endswith(b'\n') else 1))
PY
)"
  export MAX_ERRORS="$cap"
  python3 scripts/fa442_record_direct_metric.py > "$d/metric-console.log" 2>&1
  cat "$d/metric-console.log"
}

# Independent current-run root baseline, compiled exactly as every candidate.
action_install "$ROOTBASE"
export PATH="${HOME}/.elan/bin:${PATH}"
python3 scripts/fa452_prepare_compact_energy_v2.py \
  --variant root_baseline --output-dir "$ROOTBASE" > "$ROOTBASE/prepare.log" 2>&1
cat "$ROOTBASE/prepare.log"
metric_set "$ROOTBASE" root_baseline "$ROOTBASE/CANDIDATE.json" "$MAX_ERRORS"

python3 - <<'PY'
import json
from pathlib import Path
p=Path('build-logs/fa452-compact-energy/selector-root-baseline/METRIC.json')
m=json.loads(p.read_text())
ok=(
  m.get('all_required_lean_executed') is True
  and m.get('source_sha256')=='1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a'
  and m.get('Mock2_exit')==0 and m.get('Mock2_Advanced_exit')==0
  and m.get('FA_exit')==1
  and m.get('FA_first_actual_error_line')==33624
  and m.get('FA_first_actual_error_col')==57
  and m.get('FA_first_error_declaration')=='selectedCuspRestrictionRepresentative_add'
  and m.get('FA_error_declaration_index')==2720
  and m.get('forbidden_clean') is True
)
r={'classification':'VERIFIED' if ok else 'INFRA_FAILURE','ok':ok,'metric':m}
Path('build-logs/fa452-compact-energy/selected/INDEPENDENT_ROOT_BASELINE.json').write_text(
  json.dumps(r,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(r,indent=2,ensure_ascii=False))
if not ok:
  raise SystemExit('independent root baseline did not reproduce 33624:57')
PY

# Select only from the complete current-run direct matrix.
python3 scripts/fa452_select_compact_energy.py > "$SELECTED/selector-console.log" 2>&1
cat "$SELECTED/selector-console.log"

# Matrix root baseline and independent selector baseline must agree exactly.
python3 - <<'PY'
import json
from pathlib import Path
base=Path('build-logs/fa452-compact-energy')
ind=json.loads((base/'selector-root-baseline/METRIC.json').read_text())
selection=json.loads((base/'selected/SELECTION.json').read_text())
mat=selection['baseline']
fields=(
  'source_sha256','line_count','target_header_sha256',
  'declaration_sequence_sha256','Mock2_exit','Mock2_Advanced_exit','FA_exit',
  'FA_first_actual_error_line','FA_first_actual_error_col',
  'FA_first_error_declaration','FA_error_declaration_index',
)
mismatch={k:{'matrix':mat.get(k),'independent':ind.get(k)} for k in fields if mat.get(k)!=ind.get(k)}
r={'classification':'VERIFIED' if not mismatch else 'INFRA_FAILURE','mismatch':mismatch}
(base/'selected/BASELINE_IDENTITY.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
if mismatch:
  raise SystemExit('matrix baseline and independent baseline disagree')
PY

# Materialize selected source at the real repository path and create confirmation metadata.
cp "$SELECTED/Mock2_FunctionalAnalysis-selected.lean" "$SRC"
python3 - <<'PY'
import json
from pathlib import Path
base=Path('build-logs/fa452-compact-energy')
selection=json.loads((base/'selected/SELECTION.json').read_text())
chosen=selection['chosen']
metadata={
  'variant':chosen.get('variant','root_baseline'),
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
  cp "$ROOTBASE/$f" "$CONFIRM/$f"
done
SELECTED_VARIANT="$(python3 -c "import json; print(json.load(open('$SELECTED/SELECTION.json'))['chosen']['variant'])")"
metric_set "$CONFIRM" "$SELECTED_VARIANT" "$CONFIRM/CANDIDATE.json" "$MAX_ERRORS"

# Confirmation must byte-for-byte and metric-for-metric reproduce the selected matrix result.
python3 - <<'PY'
import hashlib
import json
from pathlib import Path
base=Path('build-logs/fa452-compact-energy')
selection=json.loads((base/'selected/SELECTION.json').read_text())
chosen=selection['chosen']
metric=json.loads((base/'selected-confirm/METRIC.json').read_text())
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
  and metric.get('forbidden_clean') is True
  and not mismatch
)
r={'classification':'VERIFIED' if ok else 'INFRA_FAILURE','ok':ok,
   'actual_sha256':actual,'mismatch':mismatch,'metric':metric}
(base/'selected-confirm/CONFIRMATION.json').write_text(
  json.dumps(r,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(r,indent=2,ensure_ascii=False))
if not ok:
  raise SystemExit('selected source did not reproduce under independent direct Lean CLI')
PY

# Persist source and compact selection evidence. Never touch master.
git add "$SRC"
git add -f \
  "$SELECTED/SELECTION.json" \
  "$SELECTED/CANDIDATE_RESULTS.json" \
  "$SELECTED/SELECTED_METADATA.json" \
  "$SELECTED/INDEPENDENT_ROOT_BASELINE.json" \
  "$SELECTED/BASELINE_IDENTITY.json" \
  "$CONFIRM/METRIC.json" \
  "$CONFIRM/CONFIRMATION.json"
if ! git diff --cached --quiet; then
  git commit -m "fix: persist FA452 direct champion ${SELECTED_VARIANT} [skip ci]"
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
import json
import os
from pathlib import Path
r={
  'selected_sha':os.environ['selected_sha'],
  'worktree_sha':os.environ['worktree_sha'],
  'HEAD_source_sha':os.environ['head_sha'],
  'identity_ok':os.environ['identity_ok']=='true',
  'commit':os.environ['SOURCE_COMMIT'],
}
Path('build-logs/fa452-compact-energy/final/CHECKED_IN_IDENTITY.json').write_text(
  json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
if not r['identity_ok']:
  raise SystemExit('checked-in source identity mismatch')
PY

# Checked-in FA direct compile twice. Both output artifacts are mandatory.
compile_fa_final() {
  local n="$1"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/Mock2_FunctionalAnalysis.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean -DmaxErrors=260 -DwarningAsError=false \
    -o "$o" -i "$i" "$SRC")
  printf '%q ' "${command[@]}" > "$FINAL/FA-run${n}.command"
  printf '\n' >> "$FINAL/FA-run${n}.command"
  touch "$FINAL/FA-run${n}.executed"
  set +e
  "${command[@]}" > "$FINAL/FA-run${n}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$FINAL/FA-run${n}.exit"
  printf '%s' "$(test -s "$o" && stat -c%s "$o" || echo 0)" > "$FINAL/FA-run${n}.olean.size"
  printf '%s' "$(test -s "$i" && stat -c%s "$i" || echo 0)" > "$FINAL/FA-run${n}.ilean.size"
}
compile_fa_final 1
compile_fa_final 2

python3 - <<'PY'
import importlib.util
import json
import sys
from pathlib import Path
spec=importlib.util.spec_from_file_location(
  'fa452audit','scripts/fa452_prepare_compact_energy_v2.py')
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
assert spec.loader is not None
spec.loader.exec_module(mod)
base=Path('build-logs/fa452-compact-energy/final')
source=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text()
audit=mod.forbidden_counts(source)
r1=int((base/'FA-run1.exit').read_text())
r2=int((base/'FA-run2.exit').read_text())
sizes={
  'run1_olean':int((base/'FA-run1.olean.size').read_text()),
  'run1_ilean':int((base/'FA-run1.ilean.size').read_text()),
  'run2_olean':int((base/'FA-run2.olean.size').read_text()),
  'run2_ilean':int((base/'FA-run2.ilean.size').read_text()),
}
clean=all(v==0 for v in audit.values())
true_pass=r1==0 and r2==0 and all(v>0 for v in sizes.values()) and clean
r={'run1':r1,'run2':r2,'artifact_sizes':sizes,'trust_audit':audit,
   'forbidden_clean':clean,'FA_TRUE_PASS':true_pass}
(base/'FA_FINAL.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
PY
FA_TRUE_PASS="$(python3 -c "import json; print(str(json.load(open('$FINAL/FA_FINAL.json'))['FA_TRUE_PASS']).lower())")"

# Ordered downstream gate: Integrated x2 -> all checked-in Mock3 bridges x2 -> QYM x2.
python3 - <<'PY'
import json
from pathlib import Path
p=Path('build-logs/fa452-compact-energy/final/FA_FINAL.json')
fa=json.loads(p.read_text())
result={
  'classification':'PENDING_ORDERED_DOWNSTREAM' if fa['FA_TRUE_PASS'] else 'SKIPPED_FA_NOT_TRUE_PASS',
  'FA_TRUE_PASS':fa['FA_TRUE_PASS'],
  'Integrated':'PENDING' if fa['FA_TRUE_PASS'] else 'SKIPPED',
  'Mock3_bridges':'PENDING' if fa['FA_TRUE_PASS'] else 'SKIPPED',
  'QYM':'PENDING' if fa['FA_TRUE_PASS'] else 'SKIPPED',
  'targets':[],
}
Path('build-logs/fa452-compact-energy/final/downstream/DOWNSTREAM.json').write_text(
  json.dumps(result,indent=2)+'\n')
PY

if test "$FA_TRUE_PASS" = true; then
  DOWN="$FINAL/downstream"
  complete=true
  classification=TRUE_PASS
  compile_downstream() {
    local stem="$1"
    local n="$2"
    local src="PrimalitySheafVerification/${stem}.lean"
    local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
    local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
    rm -f "$o" "$i"
    local command=(lake env lean -DmaxErrors=1 -DwarningAsError=false \
      -o "$o" -i "$i" "$src")
    printf '%q ' "${command[@]}" > "$DOWN/${stem}-run${n}.command"
    printf '\n' >> "$DOWN/${stem}-run${n}.command"
    touch "$DOWN/${stem}-run${n}.executed"
    set +e
    "${command[@]}" > "$DOWN/${stem}-run${n}.log" 2>&1
    local rc=$?
    set -e
    printf '%s' "$rc" > "$DOWN/${stem}-run${n}.exit"
    test "$rc" -eq 0 && test -s "$o" && test -s "$i"
  }

  if test -f PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean; then
    compile_downstream Mock2_FunctionalAnalysis_Integrated 1 || complete=false
    if test "$complete" = true; then
      compile_downstream Mock2_FunctionalAnalysis_Integrated 2 || complete=false
    fi
  else
    complete=false
    classification=INFRA_FAILURE
    printf 'missing\n' > "$DOWN/Integrated-missing.txt"
  fi

  if test "$complete" = true; then
    shopt -s nullglob
    mock3_sources=(PrimalitySheafVerification/Mock3*.lean)
    if test "${#mock3_sources[@]}" -eq 0; then
      complete=false
      classification=INFRA_FAILURE
      printf 'missing\n' > "$DOWN/Mock3-missing.txt"
    else
      for source in "${mock3_sources[@]}"; do
        stem="$(basename "$source" .lean)"
        compile_downstream "$stem" 1 || { complete=false; break; }
        compile_downstream "$stem" 2 || { complete=false; break; }
      done
    fi
  fi

  if test "$complete" = true; then
    if test -f PrimalitySheafVerification/QYM.lean; then
      compile_downstream QYM 1 || complete=false
      if test "$complete" = true; then
        compile_downstream QYM 2 || complete=false
      fi
    else
      complete=false
      classification=INFRA_FAILURE
      printf 'missing\n' > "$DOWN/QYM-missing.txt"
    fi
  fi

  export complete classification
  python3 - <<'PY'
import json
import os
from pathlib import Path
base=Path('build-logs/fa452-compact-energy/final/downstream')
rows=[]
for path in sorted(base.glob('*-run*.exit')):
    rows.append({'file':path.name,'exit':int(path.read_text())})
r={
  'classification':'TRUE_PASS' if os.environ['complete']=='true' else os.environ['classification'],
  'FA_TRUE_PASS':True,
  'Integrated':'TRUE_PASS_X2' if os.environ['complete']=='true' else 'FAILED_OR_BLOCKED',
  'Mock3_bridges':'TRUE_PASS_X2' if os.environ['complete']=='true' else 'FAILED_OR_BLOCKED',
  'QYM':'TRUE_PASS_X2' if os.environ['complete']=='true' else 'FAILED_OR_BLOCKED',
  'targets':rows,
}
(base/'DOWNSTREAM.json').write_text(json.dumps(r,indent=2)+'\n')
PY
fi

# Compact machine-readable final result and requested human report.
python3 - <<'PY'
import json
import os
from pathlib import Path
base=Path('build-logs/fa452-compact-energy')
selection=json.loads((base/'selected/SELECTION.json').read_text())
identity=json.loads((base/'final/CHECKED_IN_IDENTITY.json').read_text())
fa=json.loads((base/'final/FA_FINAL.json').read_text())
down=json.loads((base/'final/downstream/DOWNSTREAM.json').read_text())
classification='TRUE PASS' if fa['FA_TRUE_PASS'] else selection['classification']
result={
  'classification':classification,
  'baseline':selection['baseline'],
  'chosen':selection['chosen'],
  'candidate_results':selection['candidate_results'],
  'checked_in':identity,
  'FA_checked_in':fa,
  'downstream':down,
  'workflow_run_url':f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
  'evidence_artifact_id':'PENDING_UPLOAD_PATCH',
}
(base/'final/FINAL.json').write_text(
  json.dumps(result,indent=2,ensure_ascii=False)+'\n')

chosen=result['chosen']
rows=result['candidate_results']
lines=[]
for row in rows:
  lines.append(
    f"{row.get('variant')} | {row.get('SHA256')} | {row.get('Lean_executed')} | "
    f"{row.get('FA_exit')} | {row.get('first_line')}:{row.get('first_col')} | "
    f"{row.get('declaration')} | {row.get('classification')}"
  )
audit=fa['trust_audit']
report=f'''FA MATRIX PIPELINE REPAIR REPORT

Baseline:
source SHA256: {selection['baseline'].get('source_sha256')}
line count: {selection['baseline'].get('line_count')}
direct Lean exit: {selection['baseline'].get('FA_exit')}
first error: {selection['baseline'].get('FA_first_actual_error_line')}:{selection['baseline'].get('FA_first_actual_error_col')}
declaration: {selection['baseline'].get('FA_first_error_declaration')}

Pipeline issue found:
root cause: FA442 compile steps were conditionally skipped after candidate preparation output became false; FA452 requires direct execution markers and complete current-run metrics for every cell.
workflow files changed: .github/workflows/pre-commit.yml
scripts changed: scripts/fa452_prepare_compact_energy.py; scripts/fa452_prepare_compact_energy_v2.py; scripts/fa452_candidate_ci.sh; scripts/fa452_select_compact_energy.py; scripts/fa452_selector_ci.sh

Candidate results:
variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification
{chr(10).join(lines)}

Best direct-verified candidate:
variant: {chosen.get('variant')}
SHA256: {chosen.get('source_sha256')}
exit: {chosen.get('FA_exit')}
first error: {chosen.get('FA_first_actual_error_line')}:{chosen.get('FA_first_actual_error_col')} {chosen.get('FA_first_error_message','')}
declaration: {chosen.get('FA_first_error_declaration')}
strictly better than 33624: {selection['classification']=='STRICT_PROMOTION' or int(chosen.get('FA_exit',125))==0}

Checked-in identity:
selected SHA: {identity.get('selected_sha')}
worktree SHA: {identity.get('worktree_sha')}
HEAD source SHA: {identity.get('HEAD_source_sha')}
identity_ok: {identity.get('identity_ok')}

Trust audit:
sorry: {audit.get('sorry')}
admit: {audit.get('admit')}
global axiom: {audit.get('new_global_axiom')}
unsafe: {audit.get('unsafe')}
native_decide: {audit.get('native_decide')}
Lean.ofReduceBool: {audit.get('Lean.ofReduceBool')}

FA checked-in verification:
run1: {fa.get('run1')}
run2: {fa.get('run2')}
FA_TRUE_PASS: {fa.get('FA_TRUE_PASS')}

Downstream:
Integrated: {down.get('Integrated')}
Mock3 bridges: {down.get('Mock3_bridges')}
QYM: {down.get('QYM')}

Final classification: {classification}

Branches/commits:
branch: fix/fa452-compact-support-energy-matrix-20260810
source commit: {identity.get('commit')}
Workflow run URL: {result['workflow_run_url']}
Artifact ID: PENDING_UPLOAD_PATCH
'''
(base/'final/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt').write_text(report)
print(report)
PY

git add -f \
  "$FINAL/CHECKED_IN_IDENTITY.json" \
  "$FINAL/FA_FINAL.json" \
  "$FINAL/downstream/DOWNSTREAM.json" \
  "$FINAL/FINAL.json" \
  "$FINAL/FA_MATRIX_PIPELINE_REPAIR_REPORT.txt"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record FA452 checked-in and downstream evidence [skip ci]'
  git push origin "HEAD:${ACTIVE_BRANCH}"
fi
