#!/usr/bin/env bash
set -euo pipefail

BRANCH='fix/primality-sheaf-clean-build'
MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/fa316-qym-x86'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
EXPECTED_MOCK2_BLOB='94f8894b5f866701955a105044b8958a8deb7734'
EXPECTED_ADVANCED_BLOB='a60fa47ebcd8c1fb6037d705e81b54c80910657a'
EXPECTED_ADVANCED_SHA256='cf44063abca1d5b47331a9001a3cff45a86b5e889865812fe4e7826c6af41526'
EXPECTED_ADVANCED_BASELINE_BLOB='54bbfa432f1b8a6554d25104a0c29d4f41999984'
EXPECTED_FA_BASELINE_BLOB='4eedc43d57f96b45897990bbeaada01ee0fd3b84'
EXPECTED_PRE313_SHA256='7048e0cd364ff150a79b4696b08db0c3a29aa29dc252d623650818f59f6162ca'
EXPECTED_FA_PASS315_SHA256='36258b062cf8caef1f07cb28111cf0d6293897515b0cc49565f177eb2195de69'
EXPECTED_FA_PASS316_SHA256='ac23d9918a1daf9b534345ec4ef7eb382d081514c52bfb0dceda92d6e3633ade'

mkdir -p "${EVIDENCE}/logs" "${EVIDENCE}/source" "${EVIDENCE}/artifacts" "${OUTDIR}"
SOURCE_SHA="$(git rev-parse HEAD)"
SOURCE_BRANCH="${SOURCE_BRANCH:-${GITHUB_HEAD_REF:-${GITHUB_REF_NAME:-}}}"
test "${SOURCE_BRANCH}" = "${BRANCH}"
test "$(git hash-object "${MOCK2}")" = "${EXPECTED_MOCK2_BLOB}"
test "$(git hash-object "${ADVANCED}")" = "${EXPECTED_ADVANCED_BLOB}"
test "$(sha256sum "${ADVANCED}" | awk '{print $1}')" = "${EXPECTED_ADVANCED_SHA256}"

fa_blob="$(git hash-object "${FA}")"
fa_sha="$(sha256sum "${FA}" | awk '{print $1}')"
if [[ "${fa_blob}" = "${EXPECTED_FA_BASELINE_BLOB}" ]]; then
  source_state='baseline'
elif [[ "${fa_sha}" = "${EXPECTED_FA_PASS316_SHA256}" ]]; then
  source_state='materialized'
else
  echo "unexpected FA source blob=${fa_blob} sha256=${fa_sha}" >&2
  exit 1
fi
printf '%s\n' \
  "source_sha=${SOURCE_SHA}" \
  "source_branch=${SOURCE_BRANCH}" \
  "source_state=${source_state}" \
  "fa_start_blob=${fa_blob}" \
  "fa_start_sha256=${fa_sha}" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/snapshot.txt"

if [[ "${source_state}" = 'baseline' ]]; then
  cp "${ADVANCED}" /tmp/Mock2_Advanced.final.lean
  git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
  git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"
  test "$(git hash-object "${ADVANCED}")" = "${EXPECTED_ADVANCED_BASELINE_BLOB}"

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
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_PRE313_SHA256}"

  for script in \
    apply_three_hundred_thirteenth_pass_repairs.py \
    apply_three_hundred_fourteenth_pass_repairs.py \
    apply_three_hundred_fifteenth_pass_repairs.py; do
    echo "===== ${script} ====="
    python3 "scripts/${script}"
  done 2>&1 | tee "${EVIDENCE}/logs/pass313-315-application.log"
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS315_SHA256}"
  python3 scripts/fa316_driver.py 2>&1 | tee "${EVIDENCE}/logs/pass316-application.log"

  cp /tmp/Mock2_Advanced.final.lean "${ADVANCED}"
  while IFS= read -r changed; do
    if [[ -n "${changed}" && "${changed}" != "${FA}" ]]; then
      git restore --source=HEAD --worktree -- "${changed}"
    fi
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${FA}"
  git diff --check
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS316_SHA256}"
fi
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.pass316.lean"

python3 - <<'PY' | tee "${EVIDENCE}/forbidden-token-audit.txt"
from pathlib import Path
import re
files = [
    Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'),
    Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'),
    Path('PrimalitySheafVerification/QYM.lean'),
]
def strip(src: str) -> str:
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
    if depth or string: raise SystemExit('unterminated comment or string')
    return ''.join(out)
checks={
    'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
    'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b',
    'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
for path in files:
    code=strip(path.read_text(encoding='utf-8'))
    print(f'[{path}]')
    for name, pat in checks.items():
        n=len(re.findall(pat,code)); print(f'{name}: {n}'); bad |= n != 0
if bad: raise SystemExit('forbidden executable token detected')
PY

printf '%s\n' 'module,pass,exit_code,error_count,warning_count' > "${EVIDENCE}/compile-summary.csv"
compile_module() {
  local module="$1" pass="$2" log code errors warnings
  log="${EVIDENCE}/logs/${module}-pass${pass}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/${module}.lean" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' "${module}" "${pass}" "${code}" "${errors}" "${warnings}" \
    >> "${EVIDENCE}/compile-summary.csv"
  if [[ "${code}" -ne 0 ]]; then
    {
      echo "module=${module} pass=${pass} exit_code=${code} error_count=${errors}"
      grep -n 'error:' "${log}" | head -30 || true
      echo 'last_error:'
      grep -n 'error:' "${log}" | tail -1 || true
      tail -300 "${log}" || true
    } | tee "${EVIDENCE}/logs/${module}-pass${pass}.summary.txt"
    return "${code}"
  fi
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  if grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" "${log}"; then
    return 1
  fi
}

compile_module Mock2 dependency
compile_module Mock2_Advanced dependency
compile_module Mock2_FunctionalAnalysis 1
compile_module Mock2_FunctionalAnalysis 2
cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  "${EVIDENCE}/artifacts/"

if [[ "${source_state}" = 'baseline' ]]; then
  remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
  printf '%s\n' "trigger_head=${SOURCE_SHA}" "remote_head=${remote_head}" \
    | tee "${EVIDENCE}/materialization.txt"
  test "${remote_head}" = "${SOURCE_SHA}"
  git config user.name 'github-actions[bot]'
  git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
  git add "${FA}"
  test "$(git diff --cached --name-only)" = "${FA}"
  git commit -m 'fix: materialize Mock2 FunctionalAnalysis pass 316 source'
  materialized_sha="$(git rev-parse HEAD)"
  git push origin "HEAD:${BRANCH}"
  echo "materialized_sha=${materialized_sha}" | tee -a "${EVIDENCE}/materialization.txt"
fi

for pass in 1 2; do
  compile_module Mock2_FunctionalAnalysis_Integrated "${pass}"
  compile_module QYM "${pass}"
done
cp "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" \
  "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" "${EVIDENCE}/artifacts/"
sha256sum "${EVIDENCE}/artifacts/"* | tee "${EVIDENCE}/artifact-sha256.txt"
