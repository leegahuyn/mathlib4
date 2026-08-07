#!/usr/bin/env bash
set -uo pipefail

BRANCH='ci/fa319-isolated-20260807'
PASS_RUN='31159696948'
PASS_JOB='92827136991'
FAIL_MARKER='build-logs/PR9_ADAPTIVE_POST320_FA_QYM_FAIL'
PASS_MARKER='build-logs/PR9_ADAPTIVE_POST320_FA_QYM_PASS'
MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pr9-pass320-artifact-fallback'
mkdir -p "${EVIDENCE}/downloaded" "${EVIDENCE}/logs" \
  "${EVIDENCE}/source" "${EVIDENCE}/artifacts" "${OUTDIR}" build-logs

if [[ -e "${PASS_MARKER}" ]]; then
  echo 'adaptive PASS already exists; artifact fallback not needed' \
    | tee "${EVIDENCE}/status.txt"
  exit 0
fi
if [[ ! -e "${FAIL_MARKER}" ]]; then
  echo 'adaptive result is not a failure; artifact fallback not armed' \
    | tee "${EVIDENCE}/status.txt"
  exit 0
fi

export GH_TOKEN="${GITHUB_TOKEN:?GITHUB_TOKEN is required}"
gh api "/repos/${GITHUB_REPOSITORY}/actions/jobs/${PASS_JOB}" \
  > "${EVIDENCE}/authority-job.json"
python3 - <<'PY'
import json
p=json.load(open('/tmp/pr9-pass320-artifact-fallback/authority-job.json',encoding='utf-8'))
assert p['id']==92827136991,p
assert p['run_id']==31159696948,p
assert p['status']=='completed' and p['conclusion']=='success',p
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
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*axiom\b',r'\bunsafe\b',
            r'\bnative_decide\b',r'\bLean\.ofReduceBool\b']:
    if re.search(pat,code):raise SystemExit(f'forbidden token {pat} in {p}')
PY
}

printf 'stage,exit_code,error_count,warning_count,sha256\n' > "${EVIDENCE}/compile-summary.csv"
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
  return "${rc}"
}

# Compile the exact checked-in PASS dependencies.
audit "${MOCK2}"; audit "${ADVANCED}"
compile_one "${MOCK2}" Mock2-dependency
compile_one "${ADVANCED}" Advanced-dependency

# Download only artifacts attached to the exact authority run.
gh api "/repos/${GITHUB_REPOSITORY}/actions/runs/${PASS_RUN}/artifacts?per_page=100" \
  > "${EVIDENCE}/artifacts.json"
python3 - "${EVIDENCE}/artifacts.json" > "${EVIDENCE}/artifacts.tsv" <<'PY'
import json,sys
p=json.load(open(sys.argv[1],encoding='utf-8'))
for a in p.get('artifacts',[]):
    if not a.get('expired'):
        print(f"{a['id']}\t{a['name']}")
PY
while IFS=$'\t' read -r aid name; do
  [[ -n "${aid}" ]] || continue
  safe="$(printf '%s' "${name}" | tr -c 'A-Za-z0-9._-' '_')"
  dest="${EVIDENCE}/downloaded/${aid}-${safe}"
  mkdir -p "${dest}"
  gh api "/repos/${GITHUB_REPOSITORY}/actions/artifacts/${aid}/zip" \
    > "${dest}.zip"
  unzip -q "${dest}.zip" -d "${dest}"
done < "${EVIDENCE}/artifacts.tsv"

mapfile -t candidates < <(
  find "${EVIDENCE}/downloaded" -type f -size +200k \
    \( -iname '*Mock2*FunctionalAnalysis*.lean' \
       -o -iname '*FunctionalAnalysis*.lean' \
       -o -iname 'repaired-source.lean' \
       -o -iname 'candidate*.lean' \) -print | sort -u
)
printf '%s\n' "${candidates[@]}" > "${EVIDENCE}/candidate-list.txt"
test "${#candidates[@]}" -gt 0

cp "${FA}" /tmp/pr9-artifact-fallback-original-fa.lean
selected=''
index=0
for candidate in "${candidates[@]}"; do
  index=$((index+1))
  if ! grep -qE 'namespace[[:space:]]+Mock2FA|AutomorphicSobolev|Mock2_FunctionalAnalysis' \
      "${candidate}"; then
    continue
  fi
  cp "${candidate}" "${FA}"
  if ! audit "${FA}" > "${EVIDENCE}/logs/candidate-${index}-audit.txt" 2>&1; then
    continue
  fi
  set +e
  compile_one "${FA}" "FA-candidate-${index}"
  rc=$?
  set -e
  if [[ "${rc}" -eq 0 ]]; then
    selected="${candidate}"
    break
  fi
done

test -n "${selected}"
printf 'selected=%s\n' "${selected}" | tee "${EVIDENCE}/selection.txt"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-selected.lean"

# Full direct verification twice, then QYM twice.
audit "${FA}"; audit "${INTEGRATED}"; audit "${QYM}"
compile_one "${FA}" FA-final-pass1
compile_one "${FA}" FA-final-pass2
compile_one "${INTEGRATED}" Integrated-final-pass1
compile_one "${INTEGRATED}" Integrated-final-pass2
compile_one "${QYM}" QYM-final-pass1
compile_one "${QYM}" QYM-final-pass2

cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" \
   "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" \
   "${EVIDENCE}/artifacts/"
sha256sum "${EVIDENCE}/artifacts/"* | tee "${EVIDENCE}/artifact-sha256.txt"

verified="${EVIDENCE}/source/Mock2_FunctionalAnalysis-selected.lean"
verified_sha="$(sha256sum "${verified}" | awk '{print $1}')"
git fetch --no-tags origin "+refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}"
git reset --hard "origin/${BRANCH}"
cp "${verified}" "${FA}"
# Recompile at newest head before source push.
compile_one "${MOCK2}" Mock2-new-head
compile_one "${ADVANCED}" Advanced-new-head
compile_one "${FA}" FA-new-head-pass1
compile_one "${FA}" FA-new-head-pass2
compile_one "${INTEGRATED}" Integrated-new-head-pass1
compile_one "${INTEGRATED}" Integrated-new-head-pass2
compile_one "${QYM}" QYM-new-head-pass1
compile_one "${QYM}" QYM-new-head-pass2

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}"
test "$(git diff --cached --name-only)" = "${FA}"
git diff --cached --check
if ! git diff --cached --quiet; then
  git commit -m 'fix: materialize PASS 320 artifact-verified FunctionalAnalysis source'
  git push origin "HEAD:${BRANCH}"
fi
echo "artifact fallback PASS sha256=${verified_sha}" | tee "${EVIDENCE}/status.txt"
