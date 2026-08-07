#!/usr/bin/env bash
set -euo pipefail

: "${BRANCH:?}"
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_TOKEN:?}"

MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
LOGDIR='/tmp/priority-m2a-fa-qym-v2'

mkdir -p "${OUTDIR}" "${LOGDIR}/logs" "${LOGDIR}/source"
echo 'module,stage,exit_code,error_count,warning_count' > "${LOGDIR}/compile-summary.csv"

compile_one() {
  local module="$1" stage="$2" log code errors warnings
  log="${LOGDIR}/logs/${stage}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/${module}.lean" \
    -o "${OUTDIR}/${module}.olean" \
    -i "${OUTDIR}/${module}.ilean" \
    >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' \
    "${module}" "${stage}" "${code}" "${errors}" "${warnings}" \
    >> "${LOGDIR}/compile-summary.csv"
  if [[ "${code}" -ne 0 ]]; then
    {
      echo "module=${module}"
      echo "stage=${stage}"
      echo "exit_code=${code}"
      echo "error_count=${errors}"
      echo 'first_errors:'
      grep -n 'error:' "${log}" | head -20 || true
      echo 'last_error:'
      grep -n 'error:' "${log}" | tail -1 || true
      echo 'tail:'
      tail -240 "${log}" || true
    } | tee "${LOGDIR}/${stage}-failure.txt"
    return "${code}"
  fi
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  if grep -Eqi \
    "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" \
    "${log}"; then
    grep -nEi \
      "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" \
      "${log}" || true
    return 1
  fi
}

compile_twice() {
  local module="$1" prefix="$2"
  compile_one "${module}" "${prefix}-pass1" || return $?
  compile_one "${module}" "${prefix}-pass2"
}

audit_source() {
  TARGET_SCAN="$1" python3 - <<'PY'
from pathlib import Path
import os, re
path = Path(os.environ['TARGET_SCAN'])
src = path.read_text(encoding='utf-8')
out=[]; i=0; depth=0; string=False; esc=False
while i < len(src):
    if depth:
        if src.startswith('/-', i): depth += 1; out.extend('  '); i += 2
        elif src.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
        else: out.append('\n' if src[i] == '\n' else ' '); i += 1
    elif string:
        c=src[i]; out.append('\n' if c == '\n' else ' ')
        if esc: esc=False
        elif c == '\\': esc=True
        elif c == '"': string=False
        i += 1
    elif src.startswith('/-', i): depth=1; out.extend('  '); i += 2
    elif src.startswith('--', i):
        while i < len(src) and src[i] != '\n': out.append(' '); i += 1
    elif src[i] == '"': string=True; out.append(' '); i += 1
    else: out.append(src[i]); i += 1
if depth or string: raise SystemExit('unterminated comment or string')
code=''.join(out)
patterns={
    'sorry':r'\bsorry\b', 'admit':r'\badmit\b',
    'global_axiom':r'(?m)^\s*axiom\b', 'unsafe':r'\bunsafe\b',
    'native_decide':r'\bnative_decide\b',
    'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
print(f'[{path}]')
for name, pat in patterns.items():
    count=len(re.findall(pat, code)); print(f'{name}={count}'); bad |= count != 0
if bad: raise SystemExit(1)
PY
}

commit_one_file() {
  local path="$1" message="$2" desired_sha parent remote remote_file_sha
  desired_sha="$(sha256sum "${path}" | awk '{print $1}')"
  git add "${path}"
  test "$(git diff --cached --name-only)" = "${path}"
  git commit -m "${message}"
  parent="$(git rev-parse HEAD^)"

  for attempt in 1 2 3 4; do
    remote="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
    if [[ "${remote}" = "${parent}" ]]; then
      git push origin "HEAD:${BRANCH}"
      return 0
    fi

    git fetch --depth=50 origin "refs/heads/${BRANCH}"
    remote_file_sha="$(git show "FETCH_HEAD:${path}" | sha256sum | awk '{print $1}')"
    if [[ "${remote_file_sha}" = "${desired_sha}" ]]; then
      git reset --hard FETCH_HEAD
      return 0
    fi

    if git rebase FETCH_HEAD; then
      parent="$(git rev-parse HEAD^)"
      continue
    fi
    git rebase --abort || true
    echo "Concurrent incompatible change to ${path}" >&2
    return 1
  done
  echo "Could not push ${path} after four attempts" >&2
  return 1
}

printf '%s\n' \
  "repository=${GITHUB_REPOSITORY}" \
  "start_head=$(git rev-parse HEAD)" \
  "utc_started=$(date -u +%FT%TZ)" \
  > "${LOGDIR}/snapshot.txt"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

audit_source "${MOCK2}" | tee "${LOGDIR}/Mock2-audit.txt"
compile_twice Mock2 Mock2-direct

# 1. Mock2 Advanced
if compile_one Mock2_Advanced Advanced-checked-in-probe; then
  compile_one Mock2_Advanced Advanced-checked-in-confirm
  echo 'advanced_source=already_direct' | tee -a "${LOGDIR}/snapshot.txt"
else
  git restore --source=HEAD --worktree -- .
  advanced_scripts=(
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
  for script in "${advanced_scripts[@]}"; do
    echo "===== scripts/${script} ====="
    python3 "scripts/${script}"
  done 2>&1 | tee "${LOGDIR}/logs/advanced-repair-application.log"
  while IFS= read -r changed; do
    if [[ -n "${changed}" && "${changed}" != "${ADVANCED}" ]]; then
      git restore --source=HEAD --worktree -- "${changed}"
    fi
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${ADVANCED}"
  git diff --check
  audit_source "${ADVANCED}" | tee "${LOGDIR}/Advanced-candidate-audit.txt"
  compile_twice Mock2 Mock2-before-advanced
  compile_twice Mock2_Advanced Advanced-candidate
  cp "${ADVANCED}" "${LOGDIR}/source/Mock2_Advanced.lean"
  commit_one_file "${ADVANCED}" 'fix: materialize verified Mock2 Advanced source'
  echo "advanced_materialized_head=$(git rev-parse HEAD)" | tee -a "${LOGDIR}/snapshot.txt"
  compile_one Mock2_Advanced Advanced-materialized-direct
fi

# 2. Mock2 FunctionalAnalysis
if compile_one Mock2_FunctionalAnalysis FA-checked-in-probe; then
  compile_one Mock2_FunctionalAnalysis FA-checked-in-confirm
  echo 'fa_source=already_direct' | tee -a "${LOGDIR}/snapshot.txt"
else
  git restore --source=HEAD --worktree -- .
  git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
  git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"
  shared_scripts=(
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
  for script in "${shared_scripts[@]}"; do
    echo "===== scripts/${script} ====="
    python3 "scripts/${script}"
  done 2>&1 | tee "${LOGDIR}/logs/fa-shared-repair-application.log"
  for script in \
    apply_three_hundred_thirteenth_pass_repairs.py \
    apply_three_hundred_fourteenth_pass_repairs.py \
    apply_three_hundred_fifteenth_pass_repairs.py; do
    echo "===== scripts/${script} ====="
    python3 "scripts/${script}"
  done 2>&1 | tee "${LOGDIR}/logs/fa-final-repair-application.log"
  cp "${FA}" /tmp/Mock2_FunctionalAnalysis-candidate.lean
  git restore --source=HEAD --worktree -- .
  cp /tmp/Mock2_FunctionalAnalysis-candidate.lean "${FA}"
  test "$(git diff --name-only)" = "${FA}"
  git diff --check
  audit_source "${FA}" | tee "${LOGDIR}/FA-candidate-audit.txt"
  compile_twice Mock2 Mock2-before-fa
  compile_twice Mock2_Advanced Advanced-before-fa
  compile_twice Mock2_FunctionalAnalysis FA-candidate
  cp "${FA}" "${LOGDIR}/source/Mock2_FunctionalAnalysis.lean"
  commit_one_file "${FA}" 'fix: materialize verified Mock2 FunctionalAnalysis source'
  echo "fa_materialized_head=$(git rev-parse HEAD)" | tee -a "${LOGDIR}/snapshot.txt"
  compile_one Mock2_FunctionalAnalysis FA-materialized-direct
fi

# 3. Integrated boundary, then Mock3/QYM.
audit_source "${INTEGRATED}" | tee "${LOGDIR}/Integrated-audit.txt"
compile_twice Mock2_FunctionalAnalysis_Integrated Integrated-direct

audit_source "${QYM}" | tee "${LOGDIR}/QYM-audit.txt"
compile_twice QYM QYM-direct

sha256sum \
  "${MOCK2}" "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  "${OUTDIR}/Mock2.olean" "${OUTDIR}/Mock2_Advanced.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUTDIR}/QYM.olean" \
  | tee "${LOGDIR}/provenance-sha256.txt"

cat > "${LOGDIR}/PASS.txt" <<EOF
Mock2_Advanced=PASS
Mock2_FunctionalAnalysis=PASS
Mock2_FunctionalAnalysis_Integrated=PASS
QYM=PASS
head=$(git rev-parse HEAD)
utc=$(date -u +%FT%TZ)
EOF
cat "${LOGDIR}/PASS.txt" | tee -a "${LOGDIR}/snapshot.txt"
