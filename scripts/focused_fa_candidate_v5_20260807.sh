#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"; cd "$ROOT"
LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/fa-candidate-v5}"
M2A_PASS="${FOCUSED_M2A_PASS_MARKER:-.ci/focused/m2a_direct_pass_v5.json}"
MARKER_OUT="${FOCUSED_MARKER_OUT:-/tmp/fa_candidate_v5.json}"
BUNDLE_OUT="${FOCUSED_BUNDLE_OUT:-/tmp/fa-candidate-v5-proof.tar.gz}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
MOCK2='PrimalitySheafVerification/Mock2.lean'
M2A='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
AUDITOR='scripts/focused_source_audit_20260807.py'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
mkdir -p "$LOGDIR" "$OUT"
test -f "$M2A_PASS"
git status --porcelain=v1 > "$LOGDIR/initial-status.txt"; test ! -s "$LOGDIR/initial-status.txt"

python3 - "$M2A_PASS" <<'PY' > "$LOGDIR/m2a-pass-verification.txt"
from pathlib import Path
import hashlib,json,sys
x=json.load(open(sys.argv[1])); assert x['status']=='PASS'; assert x['runtime_source_repair'] is False
p=Path('PrimalitySheafVerification/Mock2_Advanced.lean'); actual=hashlib.sha256(p.read_bytes()).hexdigest()
print(actual); assert actual==x['source_sha256']
PY

if [[ -f "$INTEGRATED" ]] && grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "$FA" && [[ $(wc -l < "$INTEGRATED") -gt 500 ]]; then
  cp "$INTEGRATED" /tmp/fa-v5-baseline.lean
else
  cp "$FA" /tmp/fa-v5-baseline.lean
fi
BASE_SIG="$(python3 "$AUDITOR" signature /tmp/fa-v5-baseline.lean)"
printf '%s\n' \
  "head=$(git rev-parse HEAD)" \
  "master=$(git ls-remote origin refs/heads/master | awk '{print $1}')" \
  "m2a_sha256=$(sha256sum "$M2A" | awk '{print $1}')" \
  "fa_start_blob=$(git hash-object "$FA")" \
  "integrated_exists=$([[ -f "$INTEGRATED" ]] && echo yes || echo no)" \
  > "$LOGDIR/snapshot.txt"

LAST=0
compile(){
  local mod="$1" label="$2" log="$LOGDIR/$label.log"
  rm -f "$OUT/$mod.olean" "$OUT/$mod.ilean" "$OUT/$mod.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/$mod.lean" -o "$OUT/$mod.olean" -i "$OUT/$mod.ilean" > "$log" 2>&1
  LAST=$?; set -e; echo "$LAST" > "$LOGDIR/$label.exit"
  if [[ "$LAST" -ne 0 ]]; then
    { echo "label=$label"; echo "exit_code=$LAST"; echo "first_error=$(grep -n 'error:' "$log" | head -1 || true)"; echo "total_errors=$(grep -c 'error:' "$log" || true)"; echo "last_error=$(grep -n 'error:' "$log" | tail -1 || true)"; echo "maximum_error_limit=$(grep -Eci 'maximum number of errors' "$log" || true)"; } > "$LOGDIR/first-failure.env"
    grep -n 'error:' "$log" | head -10 > "$LOGDIR/$label.first-ten-errors.txt" || true
    tail -200 "$log" > "$LOGDIR/$label.tail.txt" || true
    return "$LAST"
  fi
  test -s "$OUT/$mod.olean"; test -s "$OUT/$mod.ilean"
  test "$(grep -c 'error:' "$log" || true)" -eq 0
  ! grep -Eqi "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" "$log"
  ! grep -a -q sorryAx "$OUT/$mod.olean"
}

compile Mock2 'Mock2-prerequisite'
compile Mock2_Advanced 'M2A-prerequisite'
MODE='checked-in-split'; REPAIRS='none'; split_ok=0
if [[ -f "$INTEGRATED" ]] && grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "$FA"; then
  if compile Mock2_FunctionalAnalysis_Integrated 'Integrated-checked-in-smoke' && compile Mock2_FunctionalAnalysis 'FA-wrapper-checked-in-smoke'; then
    split_ok=1
  fi
fi

if [[ "$split_ok" -ne 1 ]]; then
  MODE='repair-289-through-315'; REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,313,314,315'
  if [[ -f "$INTEGRATED" ]] && [[ $(wc -l < "$INTEGRATED") -gt 500 ]]; then cp "$INTEGRATED" "$FA"; fi
  cp "$M2A" /tmp/fa-v5-verified-m2a.lean
  git fetch --depth=1 origin "$ADVANCED_BASELINE_COMMIT"
  git show "$ADVANCED_BASELINE_COMMIT:$M2A" > "$M2A"
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
    apply_three_hundred_thirteenth_pass_repairs.py
    apply_three_hundred_fourteenth_pass_repairs.py
    apply_three_hundred_fifteenth_pass_repairs.py
  )
  for script in "${scripts[@]}"; do test -f "scripts/$script"; python3 "scripts/$script" >> "$LOGDIR/repair-application.log" 2>&1; done
  cp /tmp/fa-v5-verified-m2a.lean "$M2A"
  while IFS= read -r changed; do
    case "$changed" in "$FA"|"$M2A"|"$INTEGRATED") ;; *) git restore --source=HEAD --worktree -- "$changed" ;; esac
  done < <(git diff --name-only)
  cmp -s "$M2A" /tmp/fa-v5-verified-m2a.lean
  CAND_SIG="$(python3 "$AUDITOR" signature "$FA")"
  if [[ "$CAND_SIG" != "$BASE_SIG" ]]; then python3 "$AUDITOR" compare /tmp/fa-v5-baseline.lean "$FA" > "$LOGDIR/theorem-interface-mismatch.json" || true; exit 1; fi
  python3 "$AUDITOR" audit "$FA" > "$LOGDIR/unsplit-static-trust.json"
  cp "$FA" "$INTEGRATED"
  cat > "$FA" <<'LEAN'
/-!
# Mock2 FunctionalAnalysis compatibility entry point

The complete source-level implementation is stored in
`PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated`.
This historical module path re-exports the same public declarations.
-/
import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated
LEAN
fi

FINAL_SIG="$(python3 "$AUDITOR" signature "$INTEGRATED")"
if [[ "$FINAL_SIG" != "$BASE_SIG" ]]; then python3 "$AUDITOR" compare /tmp/fa-v5-baseline.lean "$INTEGRATED" > "$LOGDIR/integrated-interface-mismatch.json" || true; exit 1; fi
python3 "$AUDITOR" audit "$M2A" "$INTEGRATED" "$FA" > "$LOGDIR/static-trust.json"
git diff --check

for pass in 1 2; do
  compile Mock2_FunctionalAnalysis_Integrated "Integrated-pass${pass}"
  compile Mock2_FunctionalAnalysis "FA-wrapper-pass${pass}"
done
compile Mock2_Advanced 'M2A-final-regression'

sha256sum "$M2A" "$INTEGRATED" "$FA" "$OUT/Mock2_Advanced.olean" "$OUT/Mock2_Advanced.ilean" \
  "$OUT/Mock2_FunctionalAnalysis_Integrated.olean" "$OUT/Mock2_FunctionalAnalysis_Integrated.ilean" \
  "$OUT/Mock2_FunctionalAnalysis.olean" "$OUT/Mock2_FunctionalAnalysis.ilean" > "$LOGDIR/source-and-artifact-sha256.txt"
python3 - "$MARKER_OUT" "$MODE" "$REPAIRS" "$FINAL_SIG" <<'PY'
from pathlib import Path
import hashlib,json,subprocess,sys
out,mode,repairs,sig=sys.argv[1:]; obj=Path('.lake/build/lib/lean/PrimalitySheafVerification')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(p): return subprocess.check_output(['git','hash-object',str(p)],text=True).strip()
integ=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'); fa=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'); adv=Path('PrimalitySheafVerification/Mock2_Advanced.lean')
x={'phase':'FunctionalAnalysis-candidate-v5','status':'PASS','constructed_from_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
'base_master_sha':subprocess.check_output(['git','ls-remote','origin','refs/heads/master'],text=True).split()[0],
'mode':mode,'repair_scripts':repairs,'mock2_advanced_source_sha256':sha(adv),
'integrated_source_blob':blob(integ),'integrated_source_sha256':sha(integ),'compatibility_source_blob':blob(fa),'compatibility_source_sha256':sha(fa),
'theorem_signature_sha256':sig,'integrated_olean_sha256':sha(obj/'Mock2_FunctionalAnalysis_Integrated.olean'),'integrated_ilean_sha256':sha(obj/'Mock2_FunctionalAnalysis_Integrated.ilean'),
'compatibility_olean_sha256':sha(obj/'Mock2_FunctionalAnalysis.olean'),'compatibility_ilean_sha256':sha(obj/'Mock2_FunctionalAnalysis.ilean'),
'candidate_clean_pass_1':0,'candidate_clean_pass_2':0,'error_count':0,'maximum_error_limit':False,'forbidden_tokens':0,'sorryAx':0,
'new_global_axioms':0,'theorem_statements_changed':False,'assumptions_changed':False,'m2a_regression':'PASS',
'integrated_boundary':'substantive full source implementation with historical compatibility entry'}
Path(out).write_text(json.dumps(x,indent=2)+'\n')
PY
cp "$MARKER_OUT" "$LOGDIR/fa_candidate_v5.json"
tar -czf "$BUNDLE_OUT" -C "$(dirname "$LOGDIR")" "$(basename "$LOGDIR")"
echo FA_CANDIDATE_V5_PASS
