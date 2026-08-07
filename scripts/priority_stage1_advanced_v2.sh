#!/usr/bin/env bash
set -euo pipefail

: "${BRANCH:?}"
: "${GITHUB_TOKEN:?}"

MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
LOGDIR='/tmp/priority-stage1-advanced-v2'
RESULT='build-logs/priority-stage1-advanced-result.txt'

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
      grep -n 'error:' "${log}" | head -80 || true
      grep -n 'error:' "${log}" | tail -1 || true
      tail -500 "${log}" || true
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
p=Path(os.environ['TARGET_SCAN']);s=p.read_text(encoding='utf-8')
out=[];i=0;depth=0;string=False;esc=False
while i<len(s):
  if depth:
    if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
    elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
    else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
    c=s[i];out.append('\n' if c=='\n' else ' ')
    if esc:esc=False
    elif c=='\\':esc=True
    elif c=='"':string=False
    i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
    while i<len(s) and s[i]!='\n':out.append(' ');i+=1
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
if depth or string:raise SystemExit(1)
code=''.join(out)
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*axiom\b',r'\bunsafe\b',r'\bnative_decide\b',r'\bLean\.ofReduceBool\b']:
  if re.search(pat,code):raise SystemExit(1)
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
if ! compile_one Mock2_Advanced current-probe; then
  git restore --source=HEAD --worktree -- .
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
    apply_three_hundred_seventeenth_pass_mock2_advanced_repairs.py
  )
  for script in "${scripts[@]}"; do
    echo "===== scripts/${script} ====="
    python3 "scripts/${script}"
  done >"${LOGDIR}/repair.log" 2>&1
  while IFS= read -r changed; do
    [[ -z "${changed}" || "${changed}" = "${ADVANCED}" ]] || git restore --source=HEAD --worktree -- "${changed}"
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${ADVANCED}"
fi

git diff --check
audit_source "${ADVANCED}"
compile_twice Mock2
compile_twice Mock2_Advanced

candidate_sha="$(sha256sum "${ADVANCED}" | awk '{print $1}')"
if ! git diff --quiet -- "${ADVANCED}"; then
  git add "${ADVANCED}"
  git commit -m 'fix: materialize Mock2 Advanced pass 317 source'
  push_commit
fi

git fetch --depth=50 origin "refs/heads/${BRANCH}"
git reset --hard FETCH_HEAD
git clean -fd
rm -rf "${OUTDIR}";mkdir -p "${OUTDIR}"
compile_twice Mock2
compile_twice Mock2_Advanced
verified_head="$(git rev-parse HEAD)"
{
  echo 'stage=Mock2_Advanced'
  echo 'status=PASS'
  echo "verified_source_head=${verified_head}"
  echo "source_sha256=${candidate_sha}"
  echo 'repair_frontier=317'
  echo 'runtime_repair_during_final_direct=0'
  cat "${LOGDIR}/summary.csv"
} >/tmp/priority-stage1-advanced-v2-result.txt
cp /tmp/priority-stage1-advanced-v2-result.txt "${RESULT}"
git add "${RESULT}"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record Mock2 Advanced pass 317 PASS'
  push_commit
fi
