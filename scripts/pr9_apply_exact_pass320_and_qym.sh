#!/usr/bin/env bash
set -euo pipefail

BRANCH='ci/fa319-isolated-20260807'
PASS320_RUN='31159696948'
PASS320_JOB='92827136991'
BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pr9-exact-pass320'
mkdir -p "${OUTDIR}" "${EVIDENCE}/logs" "${EVIDENCE}/source" "${EVIDENCE}/artifacts"

export GH_TOKEN="${GITHUB_TOKEN:?GITHUB_TOKEN is required}"
source_head="$(git rev-parse HEAD)"
remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
test "${source_head}" = "${remote_head}"

# The user designated this exact successful job as the sole PASS 320 authority.
gh api "/repos/${GITHUB_REPOSITORY}/actions/jobs/${PASS320_JOB}" \
  > "${EVIDENCE}/pass320-job.json"
python3 - <<'PY'
import json
p=json.load(open('/tmp/pr9-exact-pass320/pass320-job.json', encoding='utf-8'))
assert p['run_id'] == 31159696948, p
assert p['id'] == 92827136991, p
assert p['status'] == 'completed', p
assert p['conclusion'] == 'success', p
print(f"PASS320 authority verified: run={p['run_id']} job={p['id']} conclusion={p['conclusion']}")
PY
gh api "/repos/${GITHUB_REPOSITORY}/actions/jobs/${PASS320_JOB}/logs" \
  > "${EVIDENCE}/pass320-job.log" || true

printf '%s\n' \
  "branch=${BRANCH}" \
  "source_head=${source_head}" \
  "remote_head=${remote_head}" \
  "pass320_run=${PASS320_RUN}" \
  "pass320_job=${PASS320_JOB}" \
  "baseline_commit=${BASELINE_COMMIT}" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/snapshot.txt"

strip_audit() {
  python3 - "$1" <<'PY'
from pathlib import Path
import re, sys
path=Path(sys.argv[1]); src=path.read_text(encoding='utf-8')
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
        while i<len(src) and src[i]!='\n': out.append(' '); i+=1
    elif src[i]=='"': string=True; out.append(' '); i+=1
    else: out.append(src[i]); i+=1
if depth or string: raise SystemExit(f'unterminated comment/string in {path}')
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

printf 'stage,exit_code,error_count,warning_count\n' > "${EVIDENCE}/compile-summary.csv"
compile_module() {
  local path="$1" label="$2" module log code errors warnings
  module="$(basename "${path}" .lean)"
  log="${EVIDENCE}/logs/${label}.log"
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
    | tee -a "${EVIDENCE}/compile-summary.csv"
  if [[ "${code}" -ne 0 ]]; then
    grep -n 'error:' "${log}" | head -100 > "${EVIDENCE}/logs/${label}.errors.txt" || true
    tail -500 "${log}" > "${EVIDENCE}/logs/${label}.tail.txt" || true
    return "${code}"
  fi
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  if grep -Eqi \
    "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" \
    "${log}"; then
    return 90
  fi
}

# Preserve the already verified current dependencies.
cp "${ADVANCED}" /tmp/pr9-current-Mock2_Advanced.lean
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-before.lean"
strip_audit "${MOCK2}" | tee "${EVIDENCE}/Mock2-audit.txt"
strip_audit "${ADVANCED}" | tee "${EVIDENCE}/Mock2_Advanced-audit.txt"
compile_module "${MOCK2}" Mock2-dependency
compile_module "${ADVANCED}" Mock2_Advanced-dependency

# Recreate the exact pre-320 FunctionalAnalysis source from a fixed historical
# baseline and the checked-in numbered repair chain. No run other than PASS 320
# is consulted as validation authority.
git fetch --no-tags --depth=1 origin "${BASELINE_COMMIT}"
git show "${BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"
git show "${BASELINE_COMMIT}:${FA}" > "${FA}"

pre313_scripts=(
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
)
for script in "${pre313_scripts[@]}"; do
  echo "===== ${script} ====="
  python3 "scripts/${script}"
done 2>&1 | tee "${EVIDENCE}/logs/pre313-application.log"

for script in \
  apply_three_hundred_thirteenth_pass_repairs.py \
  apply_three_hundred_fourteenth_pass_repairs.py \
  apply_three_hundred_fifteenth_pass_repairs.py; do
  echo "===== ${script} ====="
  python3 "scripts/${script}"
done 2>&1 | tee "${EVIDENCE}/logs/pass313-315-application.log"

python3 scripts/fa316_driver.py 2>&1 | tee "${EVIDENCE}/logs/pass316-application.log"

# The reconstruction scripts above also edit Advanced. Restore the already
# checked-in PASS source before continuing with FA-only passes.
cp /tmp/pr9-current-Mock2_Advanced.lean "${ADVANCED}"
while IFS= read -r changed; do
  if [[ -n "${changed}" && "${changed}" != "${FA}" ]]; then
    git restore --source=HEAD --worktree -- "${changed}"
  fi
done < <(git diff --name-only)
test "$(git diff --name-only)" = "${FA}"

after316="$(sha256sum "${FA}" | awk '{print $1}')"
echo "after_pass316_sha256=${after316}" | tee "${EVIDENCE}/repair-hashes.txt"

for pass in seventeenth eighteenth nineteenth twentieth; do
  script="scripts/apply_three_hundred_${pass}_pass_functional_analysis_repairs.py"
  test -f "${script}"
  echo "===== ${script} ====="
  python3 "${script}" 2>&1 | tee "${EVIDENCE}/logs/pass-${pass}-application.log"
  sha256sum "${FA}" | tee -a "${EVIDENCE}/repair-hashes.txt"
done

# Ensure this is exactly the source emitted by the 320th repair script.
pass320_expected="$(python3 - <<'PY'
import ast
from pathlib import Path
p=Path('scripts/apply_three_hundred_twentieth_pass_functional_analysis_repairs.py')
t=ast.parse(p.read_text(encoding='utf-8'))
for node in t.body:
    if isinstance(node,(ast.Assign,ast.AnnAssign)):
        targets=node.targets if isinstance(node,ast.Assign) else [node.target]
        for target in targets:
            if isinstance(target,ast.Name) and target.id=='EXPECTED_OUTPUT_SHA256':
                print(ast.literal_eval(node.value)); raise SystemExit
raise SystemExit('EXPECTED_OUTPUT_SHA256 not found in pass320 script')
PY
)"
actual_pass320="$(sha256sum "${FA}" | awk '{print $1}')"
printf '%s\n' "expected_pass320_sha256=${pass320_expected}" \
  "actual_pass320_sha256=${actual_pass320}" | tee -a "${EVIDENCE}/repair-hashes.txt"
test "${actual_pass320}" = "${pass320_expected}"

strip_audit "${FA}" | tee "${EVIDENCE}/FunctionalAnalysis-audit.txt"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass320.lean"

# Final patch-free direct verification, twice per requested module.
compile_module "${MOCK2}" Mock2-regression
compile_module "${ADVANCED}" Mock2_Advanced-regression
compile_module "${FA}" FunctionalAnalysis-pass1
compile_module "${FA}" FunctionalAnalysis-pass2
compile_module "${INTEGRATED}" FunctionalAnalysis_Integrated-pass1
compile_module "${INTEGRATED}" FunctionalAnalysis_Integrated-pass2
strip_audit "${INTEGRATED}" | tee "${EVIDENCE}/Integrated-audit.txt"
compile_module "${QYM}" QYM-pass1
compile_module "${QYM}" QYM-pass2
strip_audit "${QYM}" | tee "${EVIDENCE}/QYM-audit.txt"

cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" \
   "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" \
   "${EVIDENCE}/artifacts/"
sha256sum "${EVIDENCE}/artifacts/"* | tee "${EVIDENCE}/artifact-sha256.txt"

# Materialize only after the exact PASS 320 source and QYM chain both pass twice.
remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
test "${remote_head}" = "${source_head}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}"
test "$(git diff --cached --name-only)" = "${FA}" || git diff --cached --name-only
if ! git diff --cached --quiet; then
  git diff --cached --check
  git commit -m 'fix: materialize exact PASS 320 Mock2 FunctionalAnalysis source'
  git push origin "HEAD:${BRANCH}"
  git rev-parse HEAD | tee "${EVIDENCE}/materialized-commit.txt"
else
  echo 'Exact PASS 320 FunctionalAnalysis source was already materialized.' \
    | tee "${EVIDENCE}/materialization.txt"
fi
