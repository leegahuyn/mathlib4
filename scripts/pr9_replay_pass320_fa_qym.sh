#!/usr/bin/env bash
set -euo pipefail

BRANCH='ci/fa319-isolated-20260807'
PASS320_RUN='31159696948'
PASS320_JOB='92827136991'
ROOT="$(pwd)"
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pr9-pass320-replay'
ARTROOT="${EVIDENCE}/downloaded"
LOGDIR="${EVIDENCE}/logs"
mkdir -p "${OUTDIR}" "${ARTROOT}" "${LOGDIR}" "${EVIDENCE}/selected"

source_head="$(git rev-parse HEAD)"
remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
printf '%s\n' \
  "branch=${BRANCH}" \
  "source_head=${source_head}" \
  "remote_head=${remote_head}" \
  "pass320_run=${PASS320_RUN}" \
  "pass320_job=${PASS320_JOB}" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/snapshot.txt"

test "${source_head}" = "${remote_head}"

compile_module() {
  local path="$1" label="$2" module log code errors warnings
  module="$(basename "${path}" .lean)"
  log="${LOGDIR}/${label}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean -DmaxErrors=500 "${path}" \
    -o "${OUTDIR}/${module}.olean" \
    -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s\n' "${label}" "${code}" "${errors}" "${warnings}" \
    >> "${EVIDENCE}/compile-summary.csv"
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

path = Path(sys.argv[1])
source = path.read_text(encoding='utf-8')
out=[]; i=0; depth=0; string=False; escaped=False
while i < len(source):
    if depth:
        if source.startswith('/-', i): depth += 1; out.extend('  '); i += 2
        elif source.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
        else: out.append('\n' if source[i] == '\n' else ' '); i += 1
    elif string:
        c=source[i]; out.append('\n' if c == '\n' else ' ')
        if escaped: escaped=False
        elif c == '\\': escaped=True
        elif c == '"': string=False
        i += 1
    elif source.startswith('/-', i): depth=1; out.extend('  '); i += 2
    elif source.startswith('--', i):
        while i < len(source) and source[i] != '\n': out.append(' '); i += 1
    elif source[i] == '"': string=True; out.append(' '); i += 1
    else: out.append(source[i]); i += 1
if depth or string:
    raise SystemExit(f'unterminated comment or string in {path}')
code=''.join(out)
checks={
  'sorry':r'\bsorry\b',
  'admit':r'\badmit\b',
  'global_axiom':r'(?m)^\s*axiom\b',
  'unsafe':r'\bunsafe\b',
  'native_decide':r'\bnative_decide\b',
  'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b',
}
bad=False
print(f'[{path}]')
for name, pattern in checks.items():
    count=len(re.findall(pattern, code))
    print(f'{name}={count}')
    bad |= count != 0
if bad:
    raise SystemExit(1)
PY
}

printf 'stage,exit_code,error_count,warning_count\n' > "${EVIDENCE}/compile-summary.csv"

# Establish the exact checked-in PASS dependencies first.
audit_source PrimalitySheafVerification/Mock2.lean \
  | tee "${EVIDENCE}/Mock2-audit.txt"
audit_source PrimalitySheafVerification/Mock2_Advanced.lean \
  | tee "${EVIDENCE}/Mock2_Advanced-audit.txt"
compile_module PrimalitySheafVerification/Mock2.lean Mock2-dependency
compile_module PrimalitySheafVerification/Mock2_Advanced.lean Mock2_Advanced-dependency

# Download every artifact attached to the exact PASS 320 run. No older run is consulted.
export GH_TOKEN="${GITHUB_TOKEN:?GITHUB_TOKEN is required}"
gh api \
  -H 'Accept: application/vnd.github+json' \
  "/repos/${GITHUB_REPOSITORY}/actions/runs/${PASS320_RUN}/artifacts?per_page=100" \
  > "${EVIDENCE}/pass320-artifacts.json"

python3 - "${EVIDENCE}/pass320-artifacts.json" > "${EVIDENCE}/artifact-ids.tsv" <<'PY'
import json, sys
obj=json.load(open(sys.argv[1], encoding='utf-8'))
arts=[a for a in obj.get('artifacts', []) if not a.get('expired')]
if not arts:
    raise SystemExit('PASS 320 run has no live artifacts')
for a in arts:
    print(f"{a['id']}\t{a['name']}")
PY

while IFS=$'\t' read -r artifact_id artifact_name; do
  safe_name="$(printf '%s' "${artifact_name}" | tr -c 'A-Za-z0-9._-' '_')"
  zip_path="${ARTROOT}/${artifact_id}-${safe_name}.zip"
  dest="${ARTROOT}/${artifact_id}-${safe_name}"
  mkdir -p "${dest}"
  gh api \
    -H 'Accept: application/vnd.github+json' \
    "/repos/${GITHUB_REPOSITORY}/actions/artifacts/${artifact_id}/zip" \
    > "${zip_path}"
  unzip -q "${zip_path}" -d "${dest}"
done < "${EVIDENCE}/artifact-ids.tsv"

# Preserve the exact PASS 320 job log as provenance.
gh api \
  -H 'Accept: application/vnd.github+json' \
  "/repos/${GITHUB_REPOSITORY}/actions/jobs/${PASS320_JOB}/logs" \
  > "${EVIDENCE}/pass320-job.log" || true

cp "${FA}" /tmp/Mock2_FunctionalAnalysis.checked-in.lean
cp "${QYM}" /tmp/QYM.checked-in.lean

# Try the checked-in branch source first. If it fails, only candidates contained in
# the exact PASS 320 artifacts are considered.
selected_fa=''
set +e
audit_source "${FA}" > "${EVIDENCE}/checked-in-fa-audit.txt" 2>&1
fa_audit_code=$?
if [[ "${fa_audit_code}" -eq 0 ]]; then
  compile_module "${FA}" FunctionalAnalysis-checked-in-probe
  fa_direct_code=$?
else
  fa_direct_code=1
fi
set -e
if [[ "${fa_direct_code}" -eq 0 ]]; then
  selected_fa='checked-in'
else
  mapfile -t candidates < <(
    find "${ARTROOT}" -type f -size +200k \
      \( -iname '*Mock2*FunctionalAnalysis*.lean' \
         -o -iname '*FunctionalAnalysis*.lean' \
         -o -iname 'repaired-source.lean' \
         -o -iname 'candidate*.lean' \) -print | sort -u
  )
  printf '%s\n' "${candidates[@]}" > "${EVIDENCE}/fa-candidates.txt"
  test "${#candidates[@]}" -gt 0

  index=0
  for candidate in "${candidates[@]}"; do
    index=$((index + 1))
    if ! grep -qE 'namespace[[:space:]]+Mock2FA|Mock2_FunctionalAnalysis|AutomorphicSobolev' \
        "${candidate}"; then
      continue
    fi
    cp "${candidate}" "${FA}"
    if ! audit_source "${FA}" > "${LOGDIR}/candidate-${index}-audit.log" 2>&1; then
      continue
    fi
    set +e
    compile_module "${FA}" "FunctionalAnalysis-pass320-candidate-${index}"
    code=$?
    set -e
    if [[ "${code}" -eq 0 ]]; then
      selected_fa="${candidate}"
      break
    fi
  done
fi

test -n "${selected_fa}"
printf 'selected_fa=%s\n' "${selected_fa}" | tee "${EVIDENCE}/selection.txt"
cp "${FA}" "${EVIDENCE}/selected/Mock2_FunctionalAnalysis.lean"
sha256sum "${FA}" | tee "${EVIDENCE}/selected-fa-sha256.txt"

# Final direct-source verification: delete project artifacts and compile twice.
compile_module "${FA}" FunctionalAnalysis-final-pass1
compile_module "${FA}" FunctionalAnalysis-final-pass2
compile_module "${INTEGRATED}" FunctionalAnalysis_Integrated-pass1
compile_module "${INTEGRATED}" FunctionalAnalysis_Integrated-pass2

# QYM normally becomes buildable once the verified FA/Integrated objects exist.
# If it does not, only a QYM candidate from the same PASS 320 run may replace it.
selected_qym='checked-in'
set +e
compile_module "${QYM}" QYM-checked-in-probe
qym_code=$?
set -e
if [[ "${qym_code}" -ne 0 ]]; then
  selected_qym=''
  mapfile -t qym_candidates < <(
    find "${ARTROOT}" -type f -size +10k \
      \( -iname 'QYM.lean' -o -iname '*QYM*candidate*.lean' \
         -o -iname '*Mock3*.lean' \) -print | sort -u
  )
  printf '%s\n' "${qym_candidates[@]}" > "${EVIDENCE}/qym-candidates.txt"
  index=0
  for candidate in "${qym_candidates[@]}"; do
    index=$((index + 1))
    cp "${candidate}" "${QYM}"
    if ! audit_source "${QYM}" > "${LOGDIR}/qym-candidate-${index}-audit.log" 2>&1; then
      continue
    fi
    set +e
    compile_module "${QYM}" "QYM-pass320-candidate-${index}"
    code=$?
    set -e
    if [[ "${code}" -eq 0 ]]; then
      selected_qym="${candidate}"
      break
    fi
  done
fi

test -n "${selected_qym}"
printf 'selected_qym=%s\n' "${selected_qym}" | tee -a "${EVIDENCE}/selection.txt"
cp "${QYM}" "${EVIDENCE}/selected/QYM.lean"
compile_module "${QYM}" QYM-final-pass1
compile_module "${QYM}" QYM-final-pass2

audit_source "${FA}" | tee "${EVIDENCE}/final-fa-audit.txt"
audit_source "${INTEGRATED}" | tee "${EVIDENCE}/final-integrated-audit.txt"
audit_source "${QYM}" | tee "${EVIDENCE}/final-qym-audit.txt"

sha256sum \
  "${FA}" "${INTEGRATED}" "${QYM}" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" \
  "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" \
  | tee "${EVIDENCE}/provenance-sha256.txt"

# Push only after every direct compile and audit above has succeeded.
remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
test "${remote_head}" = "${source_head}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}" "${QYM}"
if git diff --cached --quiet; then
  echo 'PASS 320 sources already match the verified branch files.' \
    | tee "${EVIDENCE}/materialization.txt"
else
  git diff --cached --check
  git commit -m 'fix: materialize PASS 320 verified FunctionalAnalysis and QYM'
  git push origin "HEAD:${BRANCH}"
  git rev-parse HEAD | tee "${EVIDENCE}/materialized-commit.txt"
fi
