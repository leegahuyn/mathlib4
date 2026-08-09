#!/usr/bin/env bash
set -euo pipefail

BRANCH="${SOURCE_BRANCH:-${GITHUB_REF_NAME:-ci/fa319-isolated-20260807}}"
SOURCE_SHA="${SOURCE_SHA:-$(git rev-parse HEAD)}"
MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/fa320-unpinned-qym'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'

mkdir -p "${OUTDIR}" "${EVIDENCE}/logs" "${EVIDENCE}/source" "${EVIDENCE}/artifacts"
printf '%s\n' \
  "branch=${BRANCH}" \
  "source_sha=${SOURCE_SHA}" \
  "actual_head=$(git rev-parse HEAD)" \
  "fa_start_blob=$(git hash-object "${FA}")" \
  "fa_start_sha256=$(sha256sum "${FA}" | awk '{print $1}')" \
  "advanced_blob=$(git hash-object "${ADVANCED}")" \
  "utc_started=$(date -u +%FT%TZ)" | tee "${EVIDENCE}/snapshot.txt"

test "$(git rev-parse HEAD)" = "${SOURCE_SHA}"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.checked-in.lean"
cp "${ADVANCED}" /tmp/Mock2_Advanced.verified.lean

strip_audit() {
  python3 - "$1" <<'PY'
from pathlib import Path
import re, sys
path = Path(sys.argv[1])
src = path.read_text(encoding='utf-8')
out=[]; i=0; depth=0; string=False; esc=False
while i < len(src):
    if depth:
        if src.startswith('/-', i): depth += 1; out += [' ',' ']; i += 2
        elif src.startswith('-/', i): depth -= 1; out += [' ',' ']; i += 2
        else: out.append('\n' if src[i] == '\n' else ' '); i += 1
    elif string:
        c=src[i]; out.append('\n' if c == '\n' else ' ')
        if esc: esc=False
        elif c == '\\': esc=True
        elif c == '"': string=False
        i += 1
    elif src.startswith('/-', i): depth=1; out += [' ',' ']; i += 2
    elif src.startswith('--', i):
        while i < len(src) and src[i] != '\n': out.append(' '); i += 1
    elif src[i] == '"': string=True; out.append(' '); i += 1
    else: out.append(src[i]); i += 1
if depth or string: raise SystemExit(f'{path}: unterminated comment or string')
code=''.join(out)
checks={
  'sorry':r'\bsorry\b', 'admit':r'\badmit\b',
  'global_axiom':r'(?m)^\s*axiom\b', 'unsafe':r'\bunsafe\b',
  'native_decide':r'\bnative_decide\b',
  'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b',
}
bad=False
print(f'[{path}]')
for name, pat in checks.items():
    n=len(re.findall(pat, code)); print(f'{name}={n}'); bad |= n != 0
if bad: raise SystemExit(1)
PY
}

printf '%s\n' 'module,pass,exit_code,error_count,warning_count' > "${EVIDENCE}/compile-summary.csv"
compile_module() {
  local path="$1" pass="$2" module log code errors warnings
  module="$(basename "${path}" .lean)"
  log="${EVIDENCE}/logs/${module}-${pass}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean -DmaxErrors=1000 "${path}" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' "${module}" "${pass}" "${code}" "${errors}" "${warnings}" \
    | tee -a "${EVIDENCE}/compile-summary.csv"
  if [[ "${code}" -ne 0 ]]; then
    {
      echo "module=${module} pass=${pass} exit_code=${code} error_count=${errors}"
      echo '--- first errors ---'
      grep -n 'error:' "${log}" | head -100 || true
      echo '--- last errors ---'
      grep -n 'error:' "${log}" | tail -100 || true
      echo '--- log tail ---'
      tail -800 "${log}" || true
    } > "${EVIDENCE}/logs/${module}-${pass}.summary.txt"
    return "${code}"
  fi
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  if grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" "${log}"; then
    echo "forbidden diagnostic in ${log}" >&2
    return 97
  fi
}

strip_audit "${MOCK2}" | tee "${EVIDENCE}/Mock2-audit.txt"
strip_audit "${ADVANCED}" | tee "${EVIDENCE}/Mock2_Advanced-audit.txt"
compile_module "${MOCK2}" dependency
compile_module "${ADVANCED}" dependency

set +e
compile_module "${FA}" checked-in
fa_direct_code=$?
set -e

if [[ "${fa_direct_code}" -ne 0 ]]; then
  echo 'checked-in FunctionalAnalysis failed; reconstructing the PASS-320 candidate without branch/source hash pinning' \
    | tee "${EVIDENCE}/candidate-mode.txt"

  git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
  git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"

  common_scripts=(
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
    apply_three_hundred_thirteenth_pass_repairs.py
    apply_three_hundred_fourteenth_pass_repairs.py
    apply_three_hundred_fifteenth_pass_repairs.py
  )
  : > "${EVIDENCE}/logs/repair-application.log"
  for name in "${common_scripts[@]}"; do
    test -f "scripts/${name}"
    echo "===== ${name} =====" | tee -a "${EVIDENCE}/logs/repair-application.log"
    python3 "scripts/${name}" 2>&1 | tee -a "${EVIDENCE}/logs/repair-application.log"
  done

  test -f scripts/fa316_driver.py
  python3 scripts/fa316_driver.py 2>&1 | tee "${EVIDENCE}/logs/pass316-application.log"

  fa_scripts=(
    apply_three_hundred_seventeenth_pass_functional_analysis_repairs.py
    apply_three_hundred_eighteenth_pass_functional_analysis_repairs.py
    apply_three_hundred_nineteenth_pass_functional_analysis_repairs.py
  )
  for name in "${fa_scripts[@]}"; do
    test -f "scripts/${name}"
    python3 "scripts/${name}" 2>&1 | tee "${EVIDENCE}/logs/${name%.py}.log"
  done

  pass320=''
  for candidate in \
    scripts/apply_three_hundred_twentieth_pass_functional_analysis_repairs.py \
    scripts/apply_three_hundred_twentieth_pass_mock2_functional_analysis_repairs.py \
    scripts/apply_three_hundred_twentieth_pass_repairs.py; do
    if [[ -f "${candidate}" ]]; then pass320="${candidate}"; break; fi
  done
  if [[ -z "${pass320}" ]]; then
    echo 'PASS-320 FunctionalAnalysis repair script not found' >&2
    find scripts -maxdepth 1 -type f -iname '*twentieth*' -o -iname '*320*' \
      | sort | tee "${EVIDENCE}/logs/pass320-search.txt"
    exit 91
  fi
  echo "pass320_script=${pass320}" | tee "${EVIDENCE}/pass320-selection.txt"
  python3 "${pass320}" 2>&1 | tee "${EVIDENCE}/logs/pass320-application.log"

  cp /tmp/Mock2_Advanced.verified.lean "${ADVANCED}"
  while IFS= read -r changed; do
    if [[ -n "${changed}" && "${changed}" != "${FA}" ]]; then
      git restore --source=HEAD --worktree -- "${changed}"
    fi
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${FA}"
  git diff --check
  cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.pass320-candidate.lean"
fi

strip_audit "${FA}" | tee "${EVIDENCE}/Mock2_FunctionalAnalysis-audit.txt"
strip_audit "${INTEGRATED}" | tee "${EVIDENCE}/Mock2_FunctionalAnalysis_Integrated-audit.txt"
strip_audit "${QYM}" | tee "${EVIDENCE}/QYM-audit.txt"

compile_module "${MOCK2}" regression
compile_module "${ADVANCED}" regression
compile_module "${FA}" pass1
compile_module "${FA}" pass2
compile_module "${INTEGRATED}" pass1
compile_module "${INTEGRATED}" pass2
compile_module "${QYM}" pass1
compile_module "${QYM}" pass2

if [[ -f PrimalitySheafVerification/Mock3.lean ]]; then
  strip_audit PrimalitySheafVerification/Mock3.lean | tee "${EVIDENCE}/Mock3-audit.txt"
  compile_module PrimalitySheafVerification/Mock3.lean pass1
  compile_module PrimalitySheafVerification/Mock3.lean pass2
fi

for module in Mock2 Mock2_Advanced Mock2_FunctionalAnalysis Mock2_FunctionalAnalysis_Integrated QYM Mock3; do
  for ext in olean ilean; do
    if [[ -s "${OUTDIR}/${module}.${ext}" ]]; then
      cp "${OUTDIR}/${module}.${ext}" "${EVIDENCE}/artifacts/"
    fi
  done
done
sha256sum "${FA}" "${INTEGRATED}" "${QYM}" "${EVIDENCE}/artifacts/"* \
  | tee "${EVIDENCE}/sha256.txt"

if git diff --quiet -- "${FA}"; then
  echo 'checked-in FunctionalAnalysis, Integrated, and QYM already pass twice' \
    | tee "${EVIDENCE}/status.txt"
  exit 0
fi

remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
printf '%s\n' "trigger_head=${SOURCE_SHA}" "remote_head=${remote_head}" \
  | tee "${EVIDENCE}/materialization.txt"
test "${remote_head}" = "${SOURCE_SHA}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}"
test "$(git diff --cached --name-only)" = "${FA}"
git commit -m 'fix: materialize FunctionalAnalysis PASS 320 candidate after FA Integrated QYM verification'
git push origin "HEAD:${BRANCH}"
echo 'PASS-320 candidate materialized after FA, Integrated, and QYM all passed twice' \
  | tee "${EVIDENCE}/status.txt"
