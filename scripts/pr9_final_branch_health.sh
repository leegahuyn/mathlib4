#!/usr/bin/env bash
set -euo pipefail

BRANCH='ci/fa319-isolated-20260807'
MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pr9-final-branch-health'
STATUS='build-logs/pr9-final-branch-health.txt'
PASS_MARKER='build-logs/PR9_BRANCH_FIXED_PASS320_FA_QYM'
FAIL_MARKER='build-logs/PR9_BRANCH_NOT_FIXED_PASS320_FA_QYM'
mkdir -p "${OUTDIR}" "${EVIDENCE}/logs" "${EVIDENCE}/artifacts" build-logs

# The branch must contain the latest base after the synchronization repair.
git fetch --no-tags origin \
  '+refs/heads/fix/primality-sheaf-clean-build:refs/remotes/origin/fix/primality-sheaf-clean-build'
git merge-base --is-ancestor origin/fix/primality-sheaf-clean-build HEAD

export GH_TOKEN="${GITHUB_TOKEN:?GITHUB_TOKEN is required}"
gh api "/repos/${GITHUB_REPOSITORY}/pulls/9" > "${EVIDENCE}/pr9.json"
python3 - <<'PY'
import json
p=json.load(open('/tmp/pr9-final-branch-health/pr9.json',encoding='utf-8'))
assert p['state']=='open',p
assert p['merged'] is False,p
assert p['draft'] is True,p
assert p['head']['ref']=='ci/fa319-isolated-20260807',p
assert p['base']['ref']=='fix/primality-sheaf-clean-build',p
PY

audit() {
  python3 - "$1" <<'PY'
from pathlib import Path
import re,sys
p=Path(sys.argv[1]);s=p.read_text(encoding='utf-8')
out=[];i=0;d=0;q=False;e=False
while i<len(s):
    if d:
        if s.startswith('/-',i):d+=1;out+=[' ',' '];i+=2
        elif s.startswith('-/',i):d-=1;out+=[' ',' '];i+=2
        else:out.append('\n' if s[i]=='\n' else ' ');i+=1
    elif q:
        c=s[i];out.append('\n' if c=='\n' else ' ')
        if e:e=False
        elif c=='\\':e=True
        elif c=='"':q=False
        i+=1
    elif s.startswith('/-',i):d=1;out+=[' ',' '];i+=2
    elif s.startswith('--',i):
        while i<len(s) and s[i]!='\n':out.append(' ');i+=1
    elif s[i]=='"':q=True;out.append(' ');i+=1
    else:out.append(s[i]);i+=1
if d or q:raise SystemExit(1)
code=''.join(out)
checks={'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
        'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b',
        'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
print(f'[{p}]')
for name,pat in checks.items():
    n=len(re.findall(pat,code));print(f'{name}={n}')
    if n:raise SystemExit(1)
PY
}

printf 'stage,exit_code,error_count,warning_count,source_sha256\n' > "${EVIDENCE}/compile-summary.csv"
compile_one() {
  local path="$1" label="$2" module log rc errors warnings sha
  module="$(basename "${path}" .lean)"
  log="${EVIDENCE}/logs/${label}.log"
  sha="$(sha256sum "${path}" | awk '{print $1}')"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean -DmaxErrors=500 "${path}" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" \
    >"${log}" 2>&1
  rc=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' "${label}" "${rc}" "${errors}" "${warnings}" "${sha}" \
    | tee -a "${EVIDENCE}/compile-summary.csv"
  grep -n 'error:' "${log}" | head -120 > "${EVIDENCE}/logs/${label}.errors.txt" || true
  test "${rc}" -eq 0
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  ! grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" "${log}"
}

for path in "${MOCK2}" "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}"; do
  audit "${path}" | tee -a "${EVIDENCE}/forbidden-token-audit.txt"
done

compile_one "${MOCK2}" Mock2-pass1
compile_one "${MOCK2}" Mock2-pass2
compile_one "${ADVANCED}" Advanced-pass1
compile_one "${ADVANCED}" Advanced-pass2
compile_one "${FA}" FunctionalAnalysis-pass1
compile_one "${FA}" FunctionalAnalysis-pass2
compile_one "${INTEGRATED}" Integrated-pass1
compile_one "${INTEGRATED}" Integrated-pass2
compile_one "${QYM}" QYM-pass1
compile_one "${QYM}" QYM-pass2

cp "${OUTDIR}/Mock2.olean" "${OUTDIR}/Mock2.ilean" \
   "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" \
   "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" \
   "${EVIDENCE}/artifacts/"
sha256sum "${EVIDENCE}/artifacts/"* | tee "${EVIDENCE}/artifact-sha256.txt"

{
  echo "utc=$(date -u +%FT%TZ)"
  echo 'result=PASS'
  echo 'authority_run=31159696948'
  echo 'authority_job=92827136991'
  echo "head=$(git rev-parse HEAD)"
  echo "base=$(git rev-parse origin/fix/primality-sheaf-clean-build)"
  echo 'runtime_source_repair=0'
  echo
  cat "${EVIDENCE}/compile-summary.csv"
  echo
  cat "${EVIDENCE}/forbidden-token-audit.txt"
  echo
  cat "${EVIDENCE}/artifact-sha256.txt"
} > "${STATUS}"
touch "${PASS_MARKER}"
rm -f "${FAIL_MARKER}"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${STATUS}" "${PASS_MARKER}"
git add -u "${FAIL_MARKER}" 2>/dev/null || true
git diff --cached --check
if ! git diff --cached --quiet; then
  git commit -m 'ci: mark PR9 PASS 320 FA Integrated QYM direct-source PASS'
  git push origin "HEAD:${BRANCH}"
fi

comment="${EVIDENCE}/comment.md"
{
  echo '<!-- pr9-final-branch-health -->'
  echo '## PR #9 branch repair: PASS'
  echo
  echo '- Branch contains latest `fix/primality-sheaf-clean-build` base.'
  echo '- Authority: `31159696948 / 92827136991`.'
  echo '- Runtime source repair during the final gate: `0`.'
  echo '- `Mock2`, `Mock2_Advanced`, `Mock2_FunctionalAnalysis`, `Mock2_FunctionalAnalysis_Integrated`, and `QYM` each passed twice from checked-in source.'
  echo '- PR remains draft and unmerged.'
  echo
  echo '```csv'
  cat "${EVIDENCE}/compile-summary.csv"
  echo '```'
} > "${comment}"
existing="$(gh api "/repos/${GITHUB_REPOSITORY}/issues/9/comments?per_page=100" \
  --jq '.[] | select(.body | contains("<!-- pr9-final-branch-health -->")) | .id' | tail -1)"
if [[ -n "${existing}" ]]; then
  gh api --method PATCH "/repos/${GITHUB_REPOSITORY}/issues/comments/${existing}" \
    -F body=@"${comment}" >/dev/null
else
  gh api --method POST "/repos/${GITHUB_REPOSITORY}/issues/9/comments" \
    -F body=@"${comment}" >/dev/null
fi
