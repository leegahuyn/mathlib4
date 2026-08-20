#!/usr/bin/env bash
set -euo pipefail

: "${SOURCE_SHA:?}"
: "${BRANCH:?}"
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_TOKEN:?}"

MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
BASELINE_COMMIT='402e2b7aa053b9c43d95f24e6146efbc5ccf714b'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
EXPECTED_ADVANCED_BASELINE_BLOB='54bbfa432f1b8a6554d25104a0c29d4f41999984'
EXPECTED_FA_BASELINE_BLOB='4eedc43d57f96b45897990bbeaada01ee0fd3b84'
EXPECTED_PRE313_SHA256='7048e0cd364ff150a79b4696b08db0c3a29aa29dc252d623650818f59f6162ca'
EXPECTED_CANDIDATE_SHA256='36258b062cf8caef1f07cb28111cf0d6293897515b0cc49565f177eb2195de69'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
LOGDIR='/tmp/materialize-mock2-functional-analysis'
mkdir -p "${OUTDIR}" "${LOGDIR}/logs" "${LOGDIR}/source" "${LOGDIR}/artifacts"

echo 'stage,exit_code,error_count,warning_count' > "${LOGDIR}/compile-summary.csv"

compile_one() {
  local path="$1" label="$2" module log code errors warnings
  module="$(basename "${path}" .lean)"
  log="${LOGDIR}/logs/${label}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "${path}" -o "${OUTDIR}/${module}.olean" \
    -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s\n' "${label}" "${code}" "${errors}" "${warnings}" \
    >> "${LOGDIR}/compile-summary.csv"
  echo "${code}" > "${LOGDIR}/${label}.exit-code.txt"
  if [[ "${code}" -eq 0 ]]; then
    test "${errors}" -eq 0
    test -s "${OUTDIR}/${module}.olean"
    test -s "${OUTDIR}/${module}.ilean"
    if grep -Eqi \
      "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" \
      "${log}"; then
      return 90
    fi
  fi
  return "${code}"
}

audit_source() {
  python3 - "$1" <<'PY'
from pathlib import Path
import re
import sys

src=Path(sys.argv[1]).read_text(encoding='utf-8')
out=[]; i=0; depth=0; string=False; escaped=False
while i < len(src):
    if depth:
        if src.startswith('/-',i): depth+=1; out.extend('  '); i+=2
        elif src.startswith('-/',i): depth-=1; out.extend('  '); i+=2
        else: out.append('\n' if src[i]=='\n' else ' '); i+=1
    elif string:
        char=src[i]; out.append('\n' if char=='\n' else ' ')
        if escaped: escaped=False
        elif char=='\\': escaped=True
        elif char=='"': string=False
        i+=1
    elif src.startswith('/-',i): depth=1; out.extend('  '); i+=2
    elif src.startswith('--',i):
        while i < len(src) and src[i] != '\n': out.append(' '); i+=1
    elif src[i]=='"': string=True; out.append(' '); i+=1
    else: out.append(src[i]); i+=1
if depth or string: raise SystemExit('unterminated comment or string')
code=''.join(out)
checks={
  'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
  'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b',
  'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
for name,pattern in checks.items():
    count=len(re.findall(pattern,code)); print(f'{name}={count}'); bad |= count != 0
if bad: raise SystemExit(1)
PY
}

printf '%s\n' \
  "source_sha=${SOURCE_SHA}" \
  "fa_start_blob=$(git hash-object "${FA}")" \
  "fa_start_sha256=$(sha256sum "${FA}" | awk '{print $1}')" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${LOGDIR}/snapshot.txt"
cp "${FA}" "${LOGDIR}/source/Mock2_FunctionalAnalysis-before.lean"

audit_source "${MOCK2}" | tee "${LOGDIR}/Mock2-trust-audit.txt"
audit_source "${ADVANCED}" | tee "${LOGDIR}/Mock2_Advanced-trust-audit.txt"
compile_one "${MOCK2}" Mock2-direct
compile_one "${ADVANCED}" Advanced-direct

set +e
compile_one "${FA}" FunctionalAnalysis-checked-in-direct1
direct_code=$?
set -e
if [[ "${direct_code}" -eq 0 ]]; then
  compile_one "${FA}" FunctionalAnalysis-checked-in-direct2
  audit_source "${FA}" | tee "${LOGDIR}/FunctionalAnalysis-trust-audit.txt"
  cp "${FA}" "${LOGDIR}/source/Mock2_FunctionalAnalysis-verified.lean"
  cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
    "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" "${LOGDIR}/artifacts/"
  echo 'checked-in FunctionalAnalysis already passes twice' | tee "${LOGDIR}/status.txt"
  exit 0
fi

# Reproduce the already bounded pass-315 candidate from a fixed source snapshot.
git fetch --depth=1 origin "${BASELINE_COMMIT}" "${ADVANCED_BASELINE_COMMIT}"
git show "${BASELINE_COMMIT}:${FA}" > "${FA}"
test "$(git hash-object "${FA}")" = "${EXPECTED_FA_BASELINE_BLOB}"
cp "${ADVANCED}" /tmp/current-Mock2_Advanced.lean
git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"
test "$(git hash-object "${ADVANCED}")" = "${EXPECTED_ADVANCED_BASELINE_BLOB}"

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
)
: > "${LOGDIR}/logs/pre313-repair-application.log"
for script in "${scripts[@]}"; do
  echo "===== ${script} =====" | tee -a "${LOGDIR}/logs/pre313-repair-application.log"
  python3 "scripts/${script}" 2>&1 | tee -a "${LOGDIR}/logs/pre313-repair-application.log"
done
pre313_sha="$(sha256sum "${FA}" | awk '{print $1}')"
test "${pre313_sha}" = "${EXPECTED_PRE313_SHA256}"

: > "${LOGDIR}/logs/pass313-315-application.log"
for script in \
  apply_three_hundred_thirteenth_pass_repairs.py \
  apply_three_hundred_fourteenth_pass_repairs.py \
  apply_three_hundred_fifteenth_pass_repairs.py; do
  echo "===== ${script} =====" | tee -a "${LOGDIR}/logs/pass313-315-application.log"
  python3 "scripts/${script}" 2>&1 | tee -a "${LOGDIR}/logs/pass313-315-application.log"
done

cp /tmp/current-Mock2_Advanced.lean "${ADVANCED}"
while IFS= read -r changed; do
  if [[ -n "${changed}" && "${changed}" != "${FA}" ]]; then
    git restore --source=HEAD --worktree -- "${changed}"
  fi
done < <(git diff --name-only)
test "$(git diff --name-only)" = "${FA}"
git diff --check
candidate_sha="$(sha256sum "${FA}" | awk '{print $1}')"
test "${candidate_sha}" = "${EXPECTED_CANDIDATE_SHA256}"
printf '%s\n' \
  "pre313_sha256=${pre313_sha}" \
  "candidate_sha256=${candidate_sha}" \
  | tee -a "${LOGDIR}/snapshot.txt"

audit_source "${FA}" | tee "${LOGDIR}/FunctionalAnalysis-candidate-trust-audit.txt"
cp "${FA}" "${LOGDIR}/source/Mock2_FunctionalAnalysis-candidate.lean"
compile_one "${MOCK2}" Mock2-regression-after-repair
compile_one "${ADVANCED}" Advanced-regression-after-repair
compile_one "${FA}" FunctionalAnalysis-candidate-clean1
compile_one "${FA}" FunctionalAnalysis-candidate-clean2

test "$(git diff --name-only)" = "${FA}"
sha256sum "${FA}" "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  | tee "${LOGDIR}/provenance-sha256.txt"
cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" "${LOGDIR}/artifacts/"

remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
printf '%s\n' "trigger_head=${SOURCE_SHA}" "remote_head=${remote_head}" \
  | tee "${LOGDIR}/materialization.txt"
test "${remote_head}" = "${SOURCE_SHA}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}"
test "$(git diff --cached --name-only)" = "${FA}"
git commit -m 'fix: materialize verified Mock2 FunctionalAnalysis source'
git push origin "HEAD:${BRANCH}"
echo 'FunctionalAnalysis candidate passed twice and was materialized' \
  | tee "${LOGDIR}/status.txt"
