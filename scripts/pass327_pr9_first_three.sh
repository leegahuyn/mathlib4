#!/usr/bin/env bash
set -euo pipefail

: "${SOURCE_SHA:?SOURCE_SHA is required}"
: "${TARGET_BRANCH:?TARGET_BRANCH is required}"
: "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required}"

MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pass327-pr9-first-three'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
FA_BASELINE_COMMIT='402e2b7aa053b9c43d95f24e6146efbc5ccf714b'

mkdir -p "${EVIDENCE}/logs" "${EVIDENCE}/source" "${EVIDENCE}/artifacts" "${OUTDIR}"
echo 'phase,pass,module,exit_code,error_count,warning_count,source_sha256' > "${EVIDENCE}/compile-summary.csv"

compile_module() {
  local phase="$1" pass="$2" module="$3"
  local source="PrimalitySheafVerification/${module}.lean"
  local log="${EVIDENCE}/logs/${phase}-${module}-pass${pass}.log"
  local code errors warnings source_sha

  mkdir -p "${OUTDIR}"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  source_sha="$(sha256sum "${source}" | awk '{print $1}')"

  set +e
  lake env lean -DmaxErrors=1000 "${source}" \
    -o "${OUTDIR}/${module}.olean" \
    -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e

  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s,%s,%s\n' \
    "${phase}" "${pass}" "${module}" "${code}" "${errors}" "${warnings}" "${source_sha}" \
    >> "${EVIDENCE}/compile-summary.csv"

  if [[ "${code}" -ne 0 ]]; then
    {
      echo "phase=${phase} pass=${pass} module=${module} exit=${code} errors=${errors}"
      echo "source_sha256=${source_sha}"
      echo '--- first errors ---'
      grep -n 'error:' "${log}" | head -100 || true
      echo '--- last errors ---'
      grep -n 'error:' "${log}" | tail -40 || true
      echo '--- log tail ---'
      tail -600 "${log}" || true
    } > "${EVIDENCE}/logs/${phase}-${module}-pass${pass}-failure-summary.txt"
    return "${code}"
  fi

  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  if grep -Eqi \
    "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" \
    "${log}"; then
    echo "forbidden compiler diagnostic in ${log}" >&2
    return 91
  fi
}

apply_script() {
  local script="$1"
  test -f "scripts/${script}"
  echo "===== ${script} =====" | tee -a "${EVIDENCE}/logs/fa-repair-chain.log"
  python3 "scripts/${script}" 2>&1 | tee -a "${EVIDENCE}/logs/fa-repair-chain.log"
  printf '%s,%s\n' "${script}" "$(sha256sum "${FA}" | awk '{print $1}')" \
    >> "${EVIDENCE}/repair-source-sha256.csv"
}

audit_source() {
  python3 - "$@" <<'PY'
from pathlib import Path
import re
import sys

def strip(source: str) -> str:
    out = []
    i = 0
    depth = 0
    string = False
    escaped = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif string:
            ch = source[i]
            out.append('\n' if ch == '\n' else ' ')
            if escaped:
                escaped = False
            elif ch == '\\':
                escaped = True
            elif ch == '"':
                string = False
            i += 1
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                out.append(' '); i += 1
        elif source[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(source[i]); i += 1
    if depth or string:
        raise SystemExit('unterminated comment or string')
    return ''.join(out)

checks = {
    'sorry': r'\bsorry\b',
    'admit': r'\badmit\b',
    'global_axiom': r'(?m)^\s*axiom\b',
    'unsafe': r'\bunsafe\b',
    'native_decide': r'\bnative_decide\b',
    'Lean.ofReduceBool': r'\bLean\.ofReduceBool\b',
}
bad = False
for raw in sys.argv[1:]:
    path = Path(raw)
    code = strip(path.read_text(encoding='utf-8'))
    print(f'[{path}]')
    for name, pattern in checks.items():
        count = len(re.findall(pattern, code))
        print(f'{name}={count}')
        bad |= count != 0
if bad:
    raise SystemExit('forbidden executable token detected')
PY
}

printf '%s\n' \
  "authority=PASS327" \
  "authority_controller_run=31160331279" \
  "authority_failed_child_run=31169357849" \
  "source_sha=${SOURCE_SHA}" \
  "target_branch=${TARGET_BRANCH}" \
  "checked_out_head=$(git rev-parse HEAD)" \
  "advanced_start_sha256=$(sha256sum "${ADVANCED}" | awk '{print $1}')" \
  "fa_start_sha256=$(sha256sum "${FA}" | awk '{print $1}')" \
  "qym_start_sha256=$(sha256sum "${QYM}" | awk '{print $1}')" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/snapshot.txt"

test "$(git rev-parse HEAD)" = "${SOURCE_SHA}"
cp "${ADVANCED}" "${EVIDENCE}/source/Mock2_Advanced-before.lean"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-before.lean"
cp "${INTEGRATED}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis_Integrated-before.lean"
cp "${QYM}" "${EVIDENCE}/source/QYM-before.lean"

# Stage 1: the PASS327 child run proved these checked-in sources directly.
compile_module Advanced 1 Mock2
compile_module Advanced 1 Mock2_Advanced
compile_module Advanced 2 Mock2_Advanced
cp "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
  "${EVIDENCE}/artifacts/"
echo 'advanced_mode=checked-in-direct-two-passes' | tee -a "${EVIDENCE}/snapshot.txt"

# Stage 2: first accept a genuinely direct checked-in FA/Integrated pair.
fa_direct=0
if compile_module FA checked-in1 Mock2_FunctionalAnalysis; then
  if compile_module FA checked-in1 Mock2_FunctionalAnalysis_Integrated; then
    compile_module FA checked-in2 Mock2_FunctionalAnalysis
    compile_module FA checked-in2 Mock2_FunctionalAnalysis_Integrated
    fa_direct=1
  fi
fi

if [[ "${fa_direct}" -eq 1 ]]; then
  fa_mode='checked-in-direct-two-passes'
else
  # Reconstruct the exact historical source expected by the hash-chained repair
  # scripts, then apply every available FA pass through PASS324. PASS327 is the
  # controller authority; older pass numbers here are transformations only.
  cp "${ADVANCED}" /tmp/pass327-final-advanced.lean
  git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
  git fetch --depth=1 origin "${FA_BASELINE_COMMIT}"
  git show "${FA_BASELINE_COMMIT}:${FA}" > "${FA}"
  git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"

  : > "${EVIDENCE}/logs/fa-repair-chain.log"
  echo 'script,fa_source_sha256' > "${EVIDENCE}/repair-source-sha256.csv"
  repair_scripts=(
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
  for script in "${repair_scripts[@]}"; do
    apply_script "${script}"
  done

  apply_script fa316_driver.py
  for script in \
    apply_three_hundred_seventeenth_pass_functional_analysis_repairs.py \
    apply_three_hundred_eighteenth_pass_functional_analysis_repairs.py \
    apply_three_hundred_nineteenth_pass_functional_analysis_repairs.py \
    apply_three_hundred_twentieth_pass_functional_analysis_repairs.py \
    apply_three_hundred_twenty_first_pass_functional_analysis_repairs.py \
    apply_three_hundred_twenty_second_pass_functional_analysis_repairs.py \
    apply_three_hundred_twenty_third_pass_functional_analysis_repairs.py \
    apply_three_hundred_twenty_fourth_pass_functional_analysis_repairs.py; do
    apply_script "${script}"
  done

  cp /tmp/pass327-final-advanced.lean "${ADVANCED}"
  while IFS= read -r changed; do
    case "${changed}" in
      "${ADVANCED}"|"${FA}"|"${INTEGRATED}") ;;
      *) git restore --source=HEAD --worktree -- "${changed}" ;;
    esac
  done < <(git diff --name-only)
  git diff --check

  compile_module FA repaired-full1 Mock2_FunctionalAnalysis
  compile_module FA repaired-full2 Mock2_FunctionalAnalysis

  cp "${FA}" "${INTEGRATED}"
  printf '%s\n' \
    '/-!' \
    '# Mock2 FunctionalAnalysis compatibility entry point' \
    '' \
    'The complete source-level implementation is stored in' \
    '`PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated`.' \
    'This module preserves the historical import path and re-exports the' \
    'same public declarations without duplicating their definitions.' \
    '-/' \
    'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' \
    > "${FA}"

  git diff --check
  compile_module FA integrated1 Mock2_FunctionalAnalysis_Integrated
  compile_module FA wrapper1 Mock2_FunctionalAnalysis
  compile_module FA integrated2 Mock2_FunctionalAnalysis_Integrated
  compile_module FA wrapper2 Mock2_FunctionalAnalysis
  fa_mode='pass324-repaired-and-split'
fi

echo "functional_analysis_mode=${fa_mode}" | tee -a "${EVIDENCE}/snapshot.txt"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-final.lean"
cp "${INTEGRATED}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis_Integrated-final.lean"
cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" \
  "${EVIDENCE}/artifacts/"

# Stage 3: delete all project dependency artifacts and rebuild the chain twice.
modules=(
  Mock2 Mock2_Advanced
  Mock2_FunctionalAnalysis_Integrated
  Mock2_FunctionalAnalysis QYM
)
for pass in 1 2; do
  rm -rf "${OUTDIR}"
  mkdir -p "${OUTDIR}"
  for module in "${modules[@]}"; do
    compile_module QYM-chain "${pass}" "${module}"
  done
done
cp "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" "${EVIDENCE}/artifacts/"

audit_source "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  | tee "${EVIDENCE}/trust-audit.txt"
git diff --check
sha256sum "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  "${EVIDENCE}/artifacts/"* | tee "${EVIDENCE}/provenance-sha256.txt"

# Only a completely verified FA/Integrated materialization may change PR9.
allowed=("${FA}" "${INTEGRATED}")
while IFS= read -r changed; do
  [[ -z "${changed}" ]] && continue
  ok=0
  for path in "${allowed[@]}"; do
    [[ "${changed}" = "${path}" ]] && ok=1
  done
  if [[ "${ok}" -ne 1 ]]; then
    echo "unexpected changed path before materialization: ${changed}" >&2
    exit 92
  fi
done < <(git diff --name-only)

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}" "${INTEGRATED}"
if git diff --cached --quiet; then
  echo 'materialized=false' | tee "${EVIDENCE}/materialization.txt"
else
  remote_head="$(git ls-remote origin "refs/heads/${TARGET_BRANCH}" | awk '{print $1}')"
  test "${remote_head}" = "${SOURCE_SHA}"
  git commit -m 'fix: materialize PASS 327 verified FunctionalAnalysis source'
  verified_commit="$(git rev-parse HEAD)"
  printf '%s\n' \
    'materialized=true' \
    "trigger_head=${SOURCE_SHA}" \
    "verified_commit=${verified_commit}" \
    | tee "${EVIDENCE}/materialization.txt"
  git push origin "HEAD:${TARGET_BRANCH}"
fi

echo 'PASS327 first-three chain completed successfully' | tee "${EVIDENCE}/status.txt"
