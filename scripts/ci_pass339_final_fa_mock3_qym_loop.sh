#!/usr/bin/env bash
set -euo pipefail

: "${TARGET_BRANCH:=ci/fa319-isolated-20260807}"
: "${SOURCE_SHA:=$(git rev-parse HEAD)}"
: "${GITHUB_REPOSITORY:=leegahuyn/mathlib4}"

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pass339-final-fa-mock3-qym'
PASS339_SHA='57f084029aff8e8a4b95d13e0daa9890eaa036716da48b3a3352ac3023be1c25'

mkdir -p "${EVIDENCE}/logs" "${EVIDENCE}/source" "${EVIDENCE}/artifacts" "${OUTDIR}"
echo 'phase,pass,module,exit_code,error_count,warning_count,source_sha256' > "${EVIDENCE}/compile-summary.csv"

compile_module() {
  local phase="$1" pass="$2" module="$3"
  local source="PrimalitySheafVerification/${module}.lean"
  local log="${EVIDENCE}/logs/${phase}-${module}-${pass}.log"
  local code errors warnings source_sha
  test -f "${source}"
  mkdir -p "${OUTDIR}"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  source_sha="$(sha256sum "${source}" | awk '{print $1}')"
  set +e
  lake env lean -DmaxErrors=2000 "${source}" \
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
      grep -n 'error:' "${log}" | head -120 || true
      echo '--- last errors ---'
      grep -n 'error:' "${log}" | tail -80 || true
      echo '--- log tail ---'
      tail -900 "${log}" || true
    } > "${EVIDENCE}/logs/${phase}-${module}-${pass}-failure-summary.txt"
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

audit_sources() {
  python3 - "$@" <<'PY'
from pathlib import Path
import re
import sys

def strip(source: str) -> str:
    out=[]; i=0; depth=0; string=False; escaped=False
    while i < len(source):
        if depth:
            if source.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if source[i]=='\n' else ' '); i += 1
        elif string:
            ch=source[i]; out.append('\n' if ch=='\n' else ' ')
            if escaped: escaped=False
            elif ch=='\\': escaped=True
            elif ch=='"': string=False
            i += 1
        elif source.startswith('/-', i): depth=1; out.extend('  '); i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n': out.append(' '); i += 1
        elif source[i]=='"': string=True; out.append(' '); i += 1
        else: out.append(source[i]); i += 1
    if depth or string: raise SystemExit('unterminated comment or string')
    return ''.join(out)

checks={
  'sorry':r'\bsorry\b', 'admit':r'\badmit\b',
  'global_axiom':r'(?m)^\s*axiom\b', 'unsafe':r'\bunsafe\b',
  'native_decide':r'\bnative_decide\b',
  'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'
}
bad=False
for raw in sys.argv[1:]:
    p=Path(raw); code=strip(p.read_text(encoding='utf-8'))
    print(f'[{p}]')
    for name,pat in checks.items():
        n=len(re.findall(pat,code)); print(f'{name}={n}'); bad |= n != 0
if bad: raise SystemExit('forbidden executable token detected')
PY
}

printf '%s\n' \
  'authority=PASS339' \
  'required_order=FAx2 -> Integrated/Mock3x2 -> QYMx2' \
  "source_sha=${SOURCE_SHA}" \
  "checked_out_head=$(git rev-parse HEAD)" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/snapshot.txt"

cp "${ADVANCED}" "${EVIDENCE}/source/Mock2_Advanced-before.lean"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-before.lean"
cp "${INTEGRATED}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis_Integrated-before.lean"
cp "${QYM}" "${EVIDENCE}/source/QYM-before.lean"

# Reconstruct the exact PASS 339 candidate. The diagnostic is expected to
# return nonzero until the candidate itself compiles, but it must leave the
# hash-verified source in the worktree.
set +e
bash scripts/diagnose_pass339_fa.sh
pass339_diagnostic_code=$?
set -e
printf 'pass339_diagnostic_code=%s\n' "${pass339_diagnostic_code}" \
  | tee -a "${EVIDENCE}/snapshot.txt"
actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
test "${actual_sha}" = "${PASS339_SHA}"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass339.lean"

# Accept a direct PASS 339 success immediately; otherwise invoke the existing
# statement-preserving repair agents with the PASS 339 candidate as input.
fa_ok=0
if compile_module FA pass339-direct1 Mock2_FunctionalAnalysis; then
  compile_module FA pass339-direct2 Mock2_FunctionalAnalysis
  fa_ok=1
fi

if [[ "${fa_ok}" -ne 1 ]]; then
  export PASS_BASELINE=339
  export BASELINE_PASS=339
  export BASELINE_SHA256="${PASS339_SHA}"
  export EXPECTED_INPUT_SHA256="${PASS339_SHA}"
  export TARGET_FILE="${FA}"
  export TARGET_SOURCE="${FA}"
  export LEAN_FILE="${FA}"
  export TARGET_MODULE='Mock2_FunctionalAnalysis'
  export MODULE='Mock2_FunctionalAnalysis'
  export MAX_ROUNDS=96
  export MAX_AGENT_ROUNDS=96
  export EVIDENCE_DIR="${EVIDENCE}/agent"
  export BRANCH="${TARGET_BRANCH}"
  export GH_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
  export MODELS_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
  mkdir -p "${EVIDENCE_DIR}"

  agent_code=1
  for agent in \
    scripts/pass327_lean_repair_agent_v3.py \
    scripts/pass327_lean_repair_agent_v2.py \
    scripts/pass327_lean_repair_agent.py; do
    [[ -f "${agent}" ]] || continue
    echo "===== invoking ${agent} from PASS 339 =====" \
      | tee -a "${EVIDENCE}/logs/agent-invocations.log"
    set +e
    python3 "${agent}" 2>&1 | tee -a "${EVIDENCE}/logs/agent-invocations.log"
    agent_code=${PIPESTATUS[0]}
    set -e
    if compile_module FA "post-$(basename "${agent}")-1" Mock2_FunctionalAnalysis; then
      compile_module FA "post-$(basename "${agent}")-2" Mock2_FunctionalAnalysis
      fa_ok=1
      break
    fi
  done

  if [[ "${fa_ok}" -ne 1 && -f scripts/ci_pass327_agent_orchestrator_v2.sh ]]; then
    echo '===== invoking constrained orchestrator from PASS 339 =====' \
      | tee -a "${EVIDENCE}/logs/agent-invocations.log"
    set +e
    bash scripts/ci_pass327_agent_orchestrator_v2.sh \
      2>&1 | tee -a "${EVIDENCE}/logs/agent-invocations.log"
    orchestrator_code=${PIPESTATUS[0]}
    set -e
    printf 'orchestrator_code=%s\n' "${orchestrator_code}" \
      | tee -a "${EVIDENCE}/snapshot.txt"
    if compile_module FA post-orchestrator1 Mock2_FunctionalAnalysis; then
      compile_module FA post-orchestrator2 Mock2_FunctionalAnalysis
      fa_ok=1
    fi
  fi
fi

test "${fa_ok}" -eq 1
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-final.lean"
cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" "${EVIDENCE}/artifacts/"
echo 'fa_status=PASS_TWICE' | tee -a "${EVIDENCE}/snapshot.txt"

# Materialize the complete implementation under the integrated path and retain
# the historical import path as a transparent compatibility wrapper.
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
for pass in 1 2; do
  compile_module Integrated "${pass}" Mock2_FunctionalAnalysis_Integrated
  compile_module Integrated-wrapper "${pass}" Mock2_FunctionalAnalysis
done
cp "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" "${EVIDENCE}/artifacts/"
echo 'integrated_status=PASS_TWICE' | tee -a "${EVIDENCE}/snapshot.txt"

# Compile every actual Mock3 module present in the repository; do not invent a
# placeholder when the project names the third mock only through QYM.
mapfile -t mock3_files < <(find PrimalitySheafVerification -maxdepth 1 -type f \
  -name 'Mock3*.lean' -print | sort)
printf '%s\n' "${mock3_files[@]:-}" > "${EVIDENCE}/mock3-files.txt"
for file in "${mock3_files[@]}"; do
  module="$(basename "${file}" .lean)"
  compile_module Mock3 1 "${module}"
  compile_module Mock3 2 "${module}"
done
if [[ "${#mock3_files[@]}" -eq 0 ]]; then
  echo 'mock3_status=NO_SEPARATE_SOURCE_FILE_QYM_IS_THIRD_MOCK_ENTRY' \
    | tee -a "${EVIDENCE}/snapshot.txt"
else
  echo 'mock3_status=ALL_PRESENT_MODULES_PASS_TWICE' \
    | tee -a "${EVIDENCE}/snapshot.txt"
fi

# Final requested dependency chain: remove all project artifacts and rebuild
# through QYM twice so stale objects cannot mask a failure.
for pass in 1 2; do
  rm -rf "${OUTDIR}"
  mkdir -p "${OUTDIR}"
  compile_module QYM-chain "${pass}" Mock2
  compile_module QYM-chain "${pass}" Mock2_Advanced
  compile_module QYM-chain "${pass}" Mock2_FunctionalAnalysis_Integrated
  compile_module QYM-chain "${pass}" Mock2_FunctionalAnalysis
  for file in "${mock3_files[@]}"; do
    compile_module QYM-chain "${pass}" "$(basename "${file}" .lean)"
  done
  compile_module QYM-chain "${pass}" QYM
done
cp "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" "${EVIDENCE}/artifacts/"
echo 'qym_status=PASS_TWICE' | tee -a "${EVIDENCE}/snapshot.txt"

audit_sources "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  "${mock3_files[@]}" | tee "${EVIDENCE}/trust-audit.txt"
git diff --check
sha256sum "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  "${mock3_files[@]}" "${EVIDENCE}/artifacts/"* \
  | tee "${EVIDENCE}/provenance-sha256.txt"

# Only source files that passed the final two-pass gate may be materialized.
allowed=("${FA}" "${INTEGRATED}" "${QYM}")
for file in "${mock3_files[@]}"; do allowed+=("${file}"); done
while IFS= read -r changed; do
  [[ -z "${changed}" ]] && continue
  ok=0
  for path in "${allowed[@]}"; do [[ "${changed}" = "${path}" ]] && ok=1; done
  if [[ "${ok}" -ne 1 ]]; then
    echo "unexpected changed path before materialization: ${changed}" >&2
    exit 92
  fi
done < <(git diff --name-only)

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}" "${INTEGRATED}" "${QYM}" "${mock3_files[@]}"
if git diff --cached --quiet; then
  echo 'materialized=false' | tee "${EVIDENCE}/materialization.txt"
else
  remote_head="$(git ls-remote origin "refs/heads/${TARGET_BRANCH}" | awk '{print $1}')"
  test "${remote_head}" = "${SOURCE_SHA}"
  git commit -m 'fix: materialize PASS 339 verified FA Mock3 QYM chain'
  verified_commit="$(git rev-parse HEAD)"
  printf '%s\n' \
    'materialized=true' \
    "trigger_head=${SOURCE_SHA}" \
    "verified_commit=${verified_commit}" \
    | tee "${EVIDENCE}/materialization.txt"
  git push origin "HEAD:${TARGET_BRANCH}"
fi

echo 'PASS339_FINAL_FA_MOCK3_QYM_GATE=SUCCESS' | tee "${EVIDENCE}/status.txt"
