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
LOGDIR='/tmp/priority-m2a-fa-qym-atomic'

mkdir -p "${OUTDIR}" "${LOGDIR}/logs" "${LOGDIR}/source"
echo 'module,stage,exit_code,error_count,warning_count' > "${LOGDIR}/summary.csv"

compile_one() {
  local module="$1" stage="$2" log code errors warnings
  log="${LOGDIR}/logs/${stage}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/${module}.lean" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" \
    >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' \
    "${module}" "${stage}" "${code}" "${errors}" "${warnings}" \
    | tee -a "${LOGDIR}/summary.csv"
  if [[ "${code}" -ne 0 ]]; then
    {
      echo "FAILED: module=${module} stage=${stage} exit=${code} errors=${errors}"
      grep -n 'error:' "${log}" | head -30 || true
      grep -n 'error:' "${log}" | tail -1 || true
      tail -260 "${log}" || true
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
path=Path(os.environ['TARGET_SCAN'])
src=path.read_text(encoding='utf-8')
out=[]; i=0; depth=0; string=False; esc=False
while i < len(src):
    if depth:
        if src.startswith('/-',i): depth+=1; out.extend('  '); i+=2
        elif src.startswith('-/',i): depth-=1; out.extend('  '); i+=2
        else: out.append('\n' if src[i]=='\n' else ' '); i+=1
    elif string:
        c=src[i]; out.append('\n' if c=='\n' else ' ')
        if esc: esc=False
        elif c=='\\': esc=True
        elif c=='"': string=False
        i+=1
    elif src.startswith('/-',i): depth=1; out.extend('  '); i+=2
    elif src.startswith('--',i):
        while i < len(src) and src[i]!='\n': out.append(' '); i+=1
    elif src[i]=='"': string=True; out.append(' '); i+=1
    else: out.append(src[i]); i+=1
if depth or string: raise SystemExit('unterminated comment or string')
code=''.join(out)
checks={
  'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
  'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b',
  'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
print(f'[{path}]')
for name,pat in checks.items():
    n=len(re.findall(pat,code)); print(f'{name}={n}'); bad |= n != 0
if bad: raise SystemExit(1)
PY
}

printf '%s\n' \
  "start_head=$(git rev-parse HEAD)" \
  "utc_started=$(date -u +%FT%TZ)" \
  > "${LOGDIR}/snapshot.txt"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

# Mock2 is already materialized and is the first concrete dependency.
audit_source "${MOCK2}" | tee "${LOGDIR}/Mock2-audit.txt"
compile_twice Mock2 Mock2-base

# Build the final Advanced source in /tmp without committing anything yet.
git restore --source=HEAD --worktree -- .
if compile_one Mock2_Advanced Advanced-current-probe; then
  cp "${ADVANCED}" /tmp/Mock2_Advanced-final.lean
  echo 'advanced_candidate=current_checked_in' | tee -a "${LOGDIR}/snapshot.txt"
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
  done 2>&1 | tee "${LOGDIR}/logs/advanced-repair.log"
  while IFS= read -r changed; do
    if [[ -n "${changed}" && "${changed}" != "${ADVANCED}" ]]; then
      git restore --source=HEAD --worktree -- "${changed}"
    fi
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${ADVANCED}"
  cp "${ADVANCED}" /tmp/Mock2_Advanced-final.lean
  echo 'advanced_candidate=numbered_repairs' | tee -a "${LOGDIR}/snapshot.txt"
fi

# Probe the current FA against the final Advanced candidate.
git restore --source=HEAD --worktree -- .
cp /tmp/Mock2_Advanced-final.lean "${ADVANCED}"
compile_one Mock2 Mock2-before-fa-probe
compile_one Mock2_Advanced Advanced-before-fa-probe
if compile_one Mock2_FunctionalAnalysis FA-current-probe; then
  cp "${FA}" /tmp/Mock2_FunctionalAnalysis-final.lean
  echo 'fa_candidate=current_checked_in' | tee -a "${LOGDIR}/snapshot.txt"
else
  # Reproduce the accumulated FA repair in isolation.  The shared repair
  # scripts expect the historical Advanced baseline, so use it only while
  # producing the FA candidate and restore the final Advanced afterwards.
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
  done 2>&1 | tee "${LOGDIR}/logs/fa-shared-repair.log"
  for script in \
    apply_three_hundred_thirteenth_pass_repairs.py \
    apply_three_hundred_fourteenth_pass_repairs.py \
    apply_three_hundred_fifteenth_pass_repairs.py; do
    echo "===== scripts/${script} ====="
    python3 "scripts/${script}"
  done 2>&1 | tee "${LOGDIR}/logs/fa-final-repair.log"
  cp "${FA}" /tmp/Mock2_FunctionalAnalysis-final.lean
  echo 'fa_candidate=numbered_repairs' | tee -a "${LOGDIR}/snapshot.txt"
fi

# Install both final candidates together and verify every dependent module twice.
git restore --source=HEAD --worktree -- .
cp /tmp/Mock2_Advanced-final.lean "${ADVANCED}"
cp /tmp/Mock2_FunctionalAnalysis-final.lean "${FA}"
git diff --check
audit_source "${ADVANCED}" | tee "${LOGDIR}/Advanced-final-audit.txt"
audit_source "${FA}" | tee "${LOGDIR}/FA-final-audit.txt"
audit_source "${INTEGRATED}" | tee "${LOGDIR}/Integrated-audit.txt"
audit_source "${QYM}" | tee "${LOGDIR}/QYM-audit.txt"

for pass in 1 2; do
  compile_one Mock2 "final-Mock2-pass${pass}"
  compile_one Mock2_Advanced "final-Advanced-pass${pass}"
  compile_one Mock2_FunctionalAnalysis "final-FA-pass${pass}"
  compile_one Mock2_FunctionalAnalysis_Integrated "final-Integrated-pass${pass}"
  compile_one QYM "final-QYM-pass${pass}"
done

cp "${ADVANCED}" "${LOGDIR}/source/Mock2_Advanced.lean"
cp "${FA}" "${LOGDIR}/source/Mock2_FunctionalAnalysis.lean"
sha256sum \
  "${MOCK2}" "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  "${OUTDIR}/Mock2.olean" "${OUTDIR}/Mock2_Advanced.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUTDIR}/QYM.olean" \
  | tee "${LOGDIR}/provenance-sha256.txt"

changed="$(git diff --name-only | sort)"
allowed="$(printf '%s\n%s\n' "${ADVANCED}" "${FA}" | sort)"
if [[ -n "${changed}" ]]; then
  while IFS= read -r path; do
    [[ "${path}" = "${ADVANCED}" || "${path}" = "${FA}" ]] || {
      echo "Unexpected changed path: ${path}" >&2; exit 1;
    }
  done <<< "${changed}"
  git add "${ADVANCED}" "${FA}"
  git commit -m 'fix: materialize verified Advanced and FunctionalAnalysis sources'

  desired_advanced="$(sha256sum "${ADVANCED}" | awk '{print $1}')"
  desired_fa="$(sha256sum "${FA}" | awk '{print $1}')"
  for attempt in 1 2 3 4; do
    remote="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
    parent="$(git rev-parse HEAD^)"
    if [[ "${remote}" = "${parent}" ]]; then
      git push origin "HEAD:${BRANCH}"
      break
    fi
    git fetch --depth=50 origin "refs/heads/${BRANCH}"
    remote_advanced="$(git show "FETCH_HEAD:${ADVANCED}" | sha256sum | awk '{print $1}')"
    remote_fa="$(git show "FETCH_HEAD:${FA}" | sha256sum | awk '{print $1}')"
    if [[ "${remote_advanced}" = "${desired_advanced}" && "${remote_fa}" = "${desired_fa}" ]]; then
      git reset --hard FETCH_HEAD
      break
    fi
    git rebase FETCH_HEAD || { git rebase --abort || true; exit 1; }
    if [[ "${attempt}" -eq 4 ]]; then
      git push origin "HEAD:${BRANCH}"
    fi
  done
fi

printf '%s\n' \
  "final_head=$(git rev-parse HEAD)" \
  "Mock2_Advanced=PASS" \
  "Mock2_FunctionalAnalysis=PASS" \
  "Mock2_FunctionalAnalysis_Integrated=PASS" \
  "QYM=PASS" \
  "utc_completed=$(date -u +%FT%TZ)" \
  | tee -a "${LOGDIR}/snapshot.txt"
