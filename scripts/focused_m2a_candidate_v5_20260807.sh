#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"; cd "$ROOT"
LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/m2a-candidate-v5}"
MARKER_OUT="${FOCUSED_MARKER_OUT:-/tmp/m2a_candidate_v5.json}"
BUNDLE_OUT="${FOCUSED_BUNDLE_OUT:-/tmp/m2a-candidate-v5-proof.tar.gz}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
MOCK2='PrimalitySheafVerification/Mock2.lean'
TARGET='PrimalitySheafVerification/Mock2_Advanced.lean'
AUDITOR='scripts/focused_source_audit_20260807.py'
mkdir -p "$LOGDIR" "$OUT"

git status --porcelain=v1 > "$LOGDIR/initial-status.txt"
test ! -s "$LOGDIR/initial-status.txt"
cp "$TARGET" /tmp/m2a-v5-baseline.lean
BASE_SIG="$(python3 "$AUDITOR" signature /tmp/m2a-v5-baseline.lean)"
START_HEAD="$(git rev-parse HEAD)"

printf '%s\n' \
  "head=${START_HEAD}" \
  "master=$(git ls-remote origin refs/heads/master | awk '{print $1}')" \
  "mock2_blob=$(git hash-object "$MOCK2")" \
  "m2a_start_blob=$(git hash-object "$TARGET")" \
  "m2a_start_sha256=$(sha256sum "$TARGET" | awk '{print $1}')" \
  > "$LOGDIR/snapshot.txt"

LAST_CODE=0
compile_module() {
  local module="$1" label="$2" log="$LOGDIR/$label.log"
  rm -f "$OUT/$module.olean" "$OUT/$module.ilean" "$OUT/$module.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/$module.lean" \
    -o "$OUT/$module.olean" -i "$OUT/$module.ilean" > "$log" 2>&1
  LAST_CODE=$?
  set -e
  echo "$LAST_CODE" > "$LOGDIR/$label.exit"
  return "$LAST_CODE"
}

require_success() {
  local module="$1" label="$2" log="$LOGDIR/$label.log"
  test "$LAST_CODE" -eq 0
  test -s "$OUT/$module.olean"; test -s "$OUT/$module.ilean"
  test "$(grep -c 'error:' "$log" || true)" -eq 0
  ! grep -Eqi "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" "$log"
  ! grep -a -q sorryAx "$OUT/$module.olean"
}

failure_report() {
  local label="$1" log="$LOGDIR/$label.log"
  {
    echo "label=$label"; echo "exit_code=$LAST_CODE"
    echo "first_error=$(grep -n 'error:' "$log" | head -1 || true)"
    echo "total_errors=$(grep -c 'error:' "$log" || true)"
    echo "last_error=$(grep -n 'error:' "$log" | tail -1 || true)"
    echo "maximum_error_limit=$(grep -Eci 'maximum number of errors' "$log" || true)"
  } > "$LOGDIR/first-failure.env"
  grep -n 'error:' "$log" | head -10 > "$LOGDIR/$label.first-ten-errors.txt" || true
  tail -200 "$log" > "$LOGDIR/$label.tail.txt" || true
}

restore_unrelated() {
  while IFS= read -r changed; do
    [[ -z "$changed" || "$changed" == "$TARGET" ]] || git restore --source=HEAD --worktree -- "$changed"
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "$TARGET"
  git diff --check
}

compile_module Mock2 'mock2-prerequisite'; require_success Mock2 'mock2-prerequisite'
MODE='checked-in'; REPAIRS='none'
if compile_module Mock2_Advanced 'm2a-checked-in-smoke'; then
  require_success Mock2_Advanced 'm2a-checked-in-smoke'
else
  failure_report 'm2a-checked-in-smoke'
  MODE='v61-v68'; REPAIRS='v61,v62,v63,v64,v65,v66,v67,v68'
  primary_ok=1
  for version in $(seq 61 68); do
    script="scripts/repair_mock2_advanced_v${version}.py"
    if [[ ! -f "$script" ]] || ! python3 "$script" >> "$LOGDIR/v61-v68-application.log" 2>&1; then
      primary_ok=0; break
    fi
  done
  if [[ "$primary_ok" -eq 1 ]]; then
    restore_unrelated
    if compile_module Mock2_Advanced 'm2a-v61-v68-smoke'; then
      require_success Mock2_Advanced 'm2a-v61-v68-smoke'
    else
      failure_report 'm2a-v61-v68-smoke'; primary_ok=0
    fi
  fi
  if [[ "$primary_ok" -eq 0 ]]; then
    cp /tmp/m2a-v5-baseline.lean "$TARGET"
    MODE='legacy-289-through-312-plus-316'
    REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,316'
    scripts=(
      apply_two_hundred_eighty_ninth_pass_repairs.py
      apply_two_hundred_ninetieth_pass_repairs.py
      apply_two_hundred_ninety_first_pass_repairs.py
      apply_two_hundred_ninety_second_pass_repairs.py
      apply_two_hundred_ninety_third_pass_repairs.py
      apply_two_hundred_ninety_fourth_pass_repairs.py
      apply_two_hundred_ninety_fifth_pass_repairs.py
      apply_two_hundred_ninety_seventh_pass_repairs.py
      apply_two_hundred_ninety_eighth_pass_repairs.py
      apply_two_hundred_ninety_ninth_pass_repairs.py
      apply_three_hundredth_pass_repairs.py
      apply_three_hundred_ninth_pass_repairs.py
      apply_three_hundred_tenth_pass_repairs.py
      apply_three_hundred_eleventh_pass_repairs.py
      apply_three_hundred_twelfth_pass_repairs.py
      apply_three_hundred_sixteenth_pass_repairs.py
    )
    for script in "${scripts[@]}"; do
      test -f "scripts/$script"
      python3 "scripts/$script" >> "$LOGDIR/legacy-316-application.log" 2>&1
    done
    restore_unrelated
    if ! compile_module Mock2_Advanced 'm2a-legacy-316-smoke'; then
      failure_report 'm2a-legacy-316-smoke'; exit "$LAST_CODE"
    fi
    require_success Mock2_Advanced 'm2a-legacy-316-smoke'
  fi
fi

CANDIDATE_SIG="$(python3 "$AUDITOR" signature "$TARGET")"
if [[ "$CANDIDATE_SIG" != "$BASE_SIG" ]]; then
  python3 "$AUDITOR" compare /tmp/m2a-v5-baseline.lean "$TARGET" > "$LOGDIR/theorem-interface-mismatch.json" || true
  exit 1
fi
python3 "$AUDITOR" audit "$TARGET" > "$LOGDIR/static-trust.json"
git diff --check

for pass in 1 2; do
  if ! compile_module Mock2_Advanced "m2a-candidate-pass${pass}"; then
    failure_report "m2a-candidate-pass${pass}"; exit "$LAST_CODE"
  fi
  require_success Mock2_Advanced "m2a-candidate-pass${pass}"
done
compile_module Mock2 'mock2-final-regression'; require_success Mock2 'mock2-final-regression'

sha256sum "$MOCK2" "$TARGET" "$OUT/Mock2.olean" "$OUT/Mock2.ilean" \
  "$OUT/Mock2_Advanced.olean" "$OUT/Mock2_Advanced.ilean" > "$LOGDIR/source-and-artifact-sha256.txt"

python3 - "$MARKER_OUT" "$MODE" "$REPAIRS" "$CANDIDATE_SIG" <<'PY'
from pathlib import Path
import hashlib,json,subprocess,sys
out,mode,repairs,sig=sys.argv[1:]
target=Path('PrimalitySheafVerification/Mock2_Advanced.lean')
obj=Path('.lake/build/lib/lean/PrimalitySheafVerification')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
x={
 'phase':'Mock2_Advanced-candidate-v5','status':'PASS',
 'constructed_from_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 'base_master_sha':subprocess.check_output(['git','ls-remote','origin','refs/heads/master'],text=True).split()[0],
 'mode':mode,'repair_scripts':repairs,
 'source_blob':subprocess.check_output(['git','hash-object',str(target)],text=True).strip(),
 'source_sha256':sha(target),'theorem_signature_sha256':sig,
 'olean_sha256':sha(obj/'Mock2_Advanced.olean'),'ilean_sha256':sha(obj/'Mock2_Advanced.ilean'),
 'candidate_clean_pass_1':0,'candidate_clean_pass_2':0,'error_count':0,
 'maximum_error_limit':False,'forbidden_tokens':0,'sorryAx':0,'new_global_axioms':0,
 'theorem_statements_changed':False,'assumptions_changed':False,'mock2_regression':'PASS'
}
Path(out).write_text(json.dumps(x,indent=2)+'\n')
PY
cp "$MARKER_OUT" "$LOGDIR/m2a_candidate_v5.json"
tar -czf "$BUNDLE_OUT" -C "$(dirname "$LOGDIR")" "$(basename "$LOGDIR")"
echo M2A_CANDIDATE_V5_PASS
