#!/usr/bin/env bash
set -euo pipefail

: "${SOURCE_SHA:?}"
: "${BRANCH:?}"
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_TOKEN:?}"

TARGET='PrimalitySheafVerification/Mock2_Advanced.lean'
MOCK2='PrimalitySheafVerification/Mock2.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
LOGDIR='/tmp/adaptive-mock2-advanced-probe-v7'
HELPER='scripts/adaptive_mock2_advanced_universe_probe_v7.py'
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
  "source_blob=$(git hash-object "${TARGET}")" \
  "source_sha256=$(sha256sum "${TARGET}" | awk '{print $1}')" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${LOGDIR}/snapshot.txt"
cp "${TARGET}" "${LOGDIR}/source/Mock2_Advanced-before.lean"

audit_source "${MOCK2}" | tee "${LOGDIR}/Mock2-trust-audit.txt"
compile_one "${MOCK2}" Mock2-regression

set +e
compile_one "${TARGET}" Advanced-checked-in-direct1
direct_code=$?
set -e
if [[ "${direct_code}" -eq 0 ]]; then
  compile_one "${TARGET}" Advanced-checked-in-direct2
  audit_source "${TARGET}" | tee "${LOGDIR}/Mock2_Advanced-trust-audit.txt"
  cp "${TARGET}" "${LOGDIR}/source/Mock2_Advanced-verified.lean"
  cp "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
    "${LOGDIR}/artifacts/"
  echo 'checked-in source already passes twice' | tee "${LOGDIR}/status.txt"
  exit 0
fi

git restore --source=HEAD --worktree -- "${TARGET}"
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
  apply_three_hundred_thirteenth_pass_mock2_advanced_repairs.py
  apply_three_hundred_fourteenth_pass_mock2_advanced_repairs.py
)
: > "${LOGDIR}/logs/known-repair-application.log"
for script in "${scripts[@]}"; do
  echo "===== ${script} =====" | tee -a "${LOGDIR}/logs/known-repair-application.log"
  python3 "scripts/${script}" 2>&1 | tee -a "${LOGDIR}/logs/known-repair-application.log"
done

while IFS= read -r changed; do
  if [[ -n "${changed}" && "${changed}" != "${TARGET}" ]]; then
    git restore --source=HEAD --worktree -- "${changed}"
  fi
done < <(git diff --name-only)
test "$(git diff --name-only)" = "${TARGET}"
git diff --check

success=0
: > "${LOGDIR}/logs/probe-application.log"
for round in $(seq 1 6); do
  label="Advanced-probe-round-${round}"
  set +e
  compile_one "${TARGET}" "${label}"
  code=$?
  set -e
  if [[ "${code}" -eq 0 ]]; then
    success=1
    echo "candidate succeeded before probe round ${round}" \
      | tee -a "${LOGDIR}/logs/probe-application.log"
    break
  fi
  log="${LOGDIR}/logs/${label}.log"
  if ! grep -Eq \
    'Section7WorkaroundLedger\.RequirementEvidence|P0RepairLedger\.RequirementEvidence' \
    "${log}"; then
    echo 'candidate failed outside the two bounded RequirementEvidence declarations' >&2
    grep -n 'error:' "${log}" | head -30 >&2 || true
    exit "${code}"
  fi

  probe="/tmp/Mock2_Advanced-universe-probe-${round}.lean"
  mapping="${LOGDIR}/probe-map-${round}.json"
  probe_log="${LOGDIR}/logs/universe-probe-${round}.log"
  mode='explicit'
  set +e
  python3 "${HELPER}" prepare "${TARGET}" "${probe}" "${mapping}" \
    2>&1 | tee -a "${LOGDIR}/logs/probe-application.log"
  prepare_code=${PIPESTATUS[0]}
  set -e
  if [[ "${prepare_code}" -ne 0 ]]; then
    mode='bare'
    python3 "${HELPER}" prepare "${TARGET}" "${probe}" "${mapping}" --include-bare \
      2>&1 | tee -a "${LOGDIR}/logs/probe-application.log"
  fi

  set +e
  lake env lean "${probe}" >"${probe_log}" 2>&1
  probe_code=$?
  set -e
  echo "round=${round} mode=${mode} probe_exit=${probe_code}" \
    | tee -a "${LOGDIR}/logs/probe-application.log"

  set +e
  python3 "${HELPER}" apply "${TARGET}" "${mapping}" "${probe_log}" \
    2>&1 | tee -a "${LOGDIR}/logs/probe-application.log"
  apply_code=${PIPESTATUS[0]}
  set -e
  if [[ "${apply_code}" -ne 0 && "${mode}" = explicit ]]; then
    mode='bare'
    python3 "${HELPER}" prepare "${TARGET}" "${probe}" "${mapping}" --include-bare \
      2>&1 | tee -a "${LOGDIR}/logs/probe-application.log"
    set +e
    lake env lean "${probe}" >"${probe_log}" 2>&1
    probe_code=$?
    set -e
    echo "round=${round} mode=${mode} probe_exit=${probe_code}" \
      | tee -a "${LOGDIR}/logs/probe-application.log"
    python3 "${HELPER}" apply "${TARGET}" "${mapping}" "${probe_log}" \
      2>&1 | tee -a "${LOGDIR}/logs/probe-application.log"
  elif [[ "${apply_code}" -ne 0 ]]; then
    exit "${apply_code}"
  fi
  git diff --check
done

test "${success}" -eq 1

audit_source "${TARGET}" | tee "${LOGDIR}/Mock2_Advanced-candidate-trust-audit.txt"
cp "${TARGET}" "${LOGDIR}/source/Mock2_Advanced-candidate.lean"
compile_one "${MOCK2}" Mock2-regression-after-repair
compile_one "${TARGET}" Advanced-candidate-clean1
compile_one "${TARGET}" Advanced-candidate-clean2

test "$(git diff --name-only)" = "${TARGET}"
sha256sum "${MOCK2}" "${TARGET}" \
  "${OUTDIR}/Mock2.olean" "${OUTDIR}/Mock2.ilean" \
  "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
  | tee "${LOGDIR}/provenance-sha256.txt"
cp "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
  "${LOGDIR}/artifacts/"

remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
printf '%s\n' "trigger_head=${SOURCE_SHA}" "remote_head=${remote_head}" \
  | tee "${LOGDIR}/materialization.txt"
test "${remote_head}" = "${SOURCE_SHA}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${TARGET}"
test "$(git diff --cached --name-only)" = "${TARGET}"
git commit -m 'fix: materialize Lean-probed Mock2 Advanced source'
git push origin "HEAD:${BRANCH}"
echo 'Lean-probed candidate passed twice and was materialized' \
  | tee "${LOGDIR}/status.txt"
