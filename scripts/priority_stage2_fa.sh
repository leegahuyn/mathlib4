#!/usr/bin/env bash
set -euo pipefail

: "${BRANCH:?}"
: "${GITHUB_TOKEN:?}"

MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
LOGDIR='/tmp/priority-stage2-fa'
RESULT='build-logs/priority-stage2-fa-result.txt'

mkdir -p "${OUTDIR}" "${LOGDIR}/logs" "$(dirname "${RESULT}")"
echo 'module,pass,exit_code,error_count,warning_count' > "${LOGDIR}/summary.csv"

compile_one() {
  local module="$1" pass="$2" log code errors warnings
  log="${LOGDIR}/logs/${module}-${pass}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/${module}.lean" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' "${module}" "${pass}" "${code}" "${errors}" "${warnings}" \
    | tee -a "${LOGDIR}/summary.csv"
  if [[ "${code}" -ne 0 || "${errors}" -ne 0 || ! -s "${OUTDIR}/${module}.olean" || ! -s "${OUTDIR}/${module}.ilean" ]]; then
    {
      echo "FAILED: ${module} ${pass}"
      grep -n 'error:' "${log}" | head -60 || true
      grep -n 'error:' "${log}" | tail -1 || true
      tail -400 "${log}" || true
    } > "${LOGDIR}/failure.txt"
    return 1
  fi
  if grep -Eqi "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" "${log}"; then
    grep -nEi "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" "${log}" \
      > "${LOGDIR}/failure.txt" || true
    return 1
  fi
}

compile_twice() {
  compile_one "$1" pass1
  compile_one "$1" pass2
}

audit_source() {
  TARGET_SCAN="$1" python3 - <<'PY'
from pathlib import Path
import os,re
p=Path(os.environ['TARGET_SCAN']); s=p.read_text(encoding='utf-8')
out=[];i=0;depth=0;string=False;esc=False
while i<len(s):
  if depth:
    if s.startswith('/-',i): depth+=1;out.extend('  ');i+=2
    elif s.startswith('-/',i): depth-=1;out.extend('  ');i+=2
    else: out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
    c=s[i];out.append('\n' if c=='\n' else ' ')
    if esc: esc=False
    elif c=='\\': esc=True
    elif c=='"': string=False
    i+=1
  elif s.startswith('/-',i): depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
    while i<len(s) and s[i]!='\n': out.append(' ');i+=1
  elif s[i]=='"': string=True;out.append(' ');i+=1
  else: out.append(s[i]);i+=1
if depth or string: raise SystemExit(1)
code=''.join(out)
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*axiom\b',r'\bunsafe\b',r'\bnative_decide\b',r'\bLean\.ofReduceBool\b']:
  if re.search(pat,code): raise SystemExit(1)
PY
}

push_commit() {
  for attempt in 1 2 3 4; do
    remote="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
    parent="$(git rev-parse HEAD^)"
    if [[ "${remote}" = "${parent}" ]]; then
      git push origin "HEAD:${BRANCH}"
      return 0
    fi
    git fetch --depth=50 origin "refs/heads/${BRANCH}"
    git rebase FETCH_HEAD
  done
  git push origin "HEAD:${BRANCH}"
}

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

compile_twice Mock2
compile_twice Mock2_Advanced
if ! compile_one Mock2_FunctionalAnalysis current-probe; then
  cp "${ADVANCED}" /tmp/priority-final-advanced.lean
  git restore --source=HEAD --worktree -- .
  git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
  git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"
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
  for script in "${scripts[@]}"; do python3 "scripts/${script}"; done \
    >"${LOGDIR}/shared-repair.log" 2>&1
  for script in \
    apply_three_hundred_thirteenth_pass_repairs.py \
    apply_three_hundred_fourteenth_pass_repairs.py \
    apply_three_hundred_fifteenth_pass_repairs.py; do
    python3 "scripts/${script}"
  done >"${LOGDIR}/final-repair.log" 2>&1
  cp "${FA}" /tmp/priority-final-fa.lean
  git restore --source=HEAD --worktree -- .
  cp /tmp/priority-final-fa.lean "${FA}"
  cp /tmp/priority-final-advanced.lean "${ADVANCED}"
  while IFS= read -r changed; do
    [[ -z "${changed}" || "${changed}" = "${FA}" ]] || git restore --source=HEAD --worktree -- "${changed}"
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${FA}"
fi

git diff --check
audit_source "${FA}"
compile_twice Mock2
compile_twice Mock2_Advanced
compile_twice Mock2_FunctionalAnalysis

source_sha="$(sha256sum "${FA}" | awk '{print $1}')"
if ! git diff --quiet -- "${FA}"; then
  git add "${FA}"
  git commit -m 'fix: materialize isolated Mock2 FunctionalAnalysis verified source'
  push_commit
fi

git fetch --depth=50 origin "refs/heads/${BRANCH}"
git reset --hard FETCH_HEAD
rm -rf "${OUTDIR}"; mkdir -p "${OUTDIR}"
compile_twice Mock2
compile_twice Mock2_Advanced
compile_twice Mock2_FunctionalAnalysis
verified_head="$(git rev-parse HEAD)"
{
  echo 'stage=Mock2_FunctionalAnalysis'
  echo 'status=PASS'
  echo "verified_source_head=${verified_head}"
  echo "source_sha256=${source_sha}"
  echo 'runtime_repair_during_final_direct=0'
  cat "${LOGDIR}/summary.csv"
} > /tmp/priority-stage2-result.txt
mkdir -p "$(dirname "${RESULT}")"; cp /tmp/priority-stage2-result.txt "${RESULT}"
git add "${RESULT}"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record isolated FunctionalAnalysis PASS'
  push_commit
fi
