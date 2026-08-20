#!/usr/bin/env bash
set -uo pipefail

BRANCH='ci/fa319-isolated-20260807'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pr9-exact-pass320'
RECOVERY='/tmp/pr9-pass320-remote-recovery'
mkdir -p "${RECOVERY}/logs" "${OUTDIR}"

set +e
bash scripts/pr9_apply_exact_pass320_and_qym.sh
code=$?
set -e
if [[ "${code}" -eq 0 ]]; then
  exit 0
fi

candidate="${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass320.lean"
summary="${EVIDENCE}/compile-summary.csv"
if [[ ! -s "${candidate}" || ! -s "${summary}" ]]; then
  echo "exact PASS 320 reconstruction failed before a verified candidate existed" >&2
  exit "${code}"
fi

python3 - "${summary}" <<'PY'
import csv,sys
rows=list(csv.DictReader(open(sys.argv[1],encoding='utf-8')))
required={
 'FunctionalAnalysis-pass1','FunctionalAnalysis-pass2',
 'FunctionalAnalysis_Integrated-pass1','FunctionalAnalysis_Integrated-pass2',
 'QYM-pass1','QYM-pass2'}
seen={r['stage'] for r in rows if r['exit_code']=='0' and r['error_count']=='0'}
missing=sorted(required-seen)
if missing:
    raise SystemExit(f'candidate was not fully verified before branch changed: {missing}')
PY

cp "${candidate}" "${RECOVERY}/Mock2_FunctionalAnalysis-pass320.lean"
verified_sha="$(sha256sum "${candidate}" | awk '{print $1}')"
printf '%s\n' "initial_exit=${code}" "verified_candidate_sha256=${verified_sha}" \
  > "${RECOVERY}/recovery-status.txt"

# Refresh to the newest remote PR9 head, then re-run the complete direct checks
# against that exact head before materializing the candidate.
git fetch --no-tags origin \
  "+refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}"
git reset --hard "origin/${BRANCH}"
cp "${RECOVERY}/Mock2_FunctionalAnalysis-pass320.lean" "${FA}"

audit() {
  python3 - "$1" <<'PY'
from pathlib import Path
import re,sys
p=Path(sys.argv[1]); s=p.read_text(encoding='utf-8')
out=[];i=0;depth=0;string=False;esc=False
while i<len(s):
    if depth:
        if s.startswith('/-',i):depth+=1;out+=[' ',' '];i+=2
        elif s.startswith('-/',i):depth-=1;out+=[' ',' '];i+=2
        else:out.append('\n' if s[i]=='\n' else ' ');i+=1
    elif string:
        c=s[i];out.append('\n' if c=='\n' else ' ')
        if esc:esc=False
        elif c=='\\':esc=True
        elif c=='"':string=False
        i+=1
    elif s.startswith('/-',i):depth=1;out+=[' ',' '];i+=2
    elif s.startswith('--',i):
        while i<len(s) and s[i]!='\n':out.append(' ');i+=1
    elif s[i]=='"':string=True;out.append(' ');i+=1
    else:out.append(s[i]);i+=1
if depth or string:raise SystemExit(1)
code=''.join(out)
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*axiom\b',r'\bunsafe\b',
            r'\bnative_decide\b',r'\bLean\.ofReduceBool\b']:
    if re.search(pat,code):raise SystemExit(f'forbidden token {pat} in {p}')
PY
}

printf 'stage,exit_code,error_count,warning_count\n' > "${RECOVERY}/compile-summary.csv"
compile() {
  local path="$1" label="$2" module log rc errors warnings
  module="$(basename "${path}" .lean)"
  log="${RECOVERY}/logs/${label}.log"
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
  printf '%s,%s,%s,%s\n' "${label}" "${rc}" "${errors}" "${warnings}" \
    | tee -a "${RECOVERY}/compile-summary.csv"
  test "${rc}" -eq 0
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  ! grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" "${log}"
}

audit "${MOCK2}"
audit "${ADVANCED}"
audit "${FA}"
audit "${INTEGRATED}"
audit "${QYM}"
compile "${MOCK2}" Mock2-recovery
compile "${ADVANCED}" Advanced-recovery
compile "${FA}" FunctionalAnalysis-recovery-pass1
compile "${FA}" FunctionalAnalysis-recovery-pass2
compile "${INTEGRATED}" Integrated-recovery-pass1
compile "${INTEGRATED}" Integrated-recovery-pass2
compile "${QYM}" QYM-recovery-pass1
compile "${QYM}" QYM-recovery-pass2

test "$(sha256sum "${FA}" | awk '{print $1}')" = "${verified_sha}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}"
test "$(git diff --cached --name-only)" = "${FA}"
git diff --cached --check
if ! git diff --cached --quiet; then
  git commit -m 'fix: materialize resilient exact PASS 320 FunctionalAnalysis source'
  git push origin "HEAD:${BRANCH}"
fi

echo 'remote-head recovery completed after full revalidation' \
  | tee -a "${RECOVERY}/recovery-status.txt"
