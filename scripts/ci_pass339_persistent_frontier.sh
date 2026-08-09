#!/usr/bin/env bash
set -euo pipefail

: "${SOURCE_BRANCH:=$(git branch --show-current)}"
: "${SOURCE_SHA:=$(git rev-parse HEAD)}"
: "${TARGET_BRANCH:=ci/fa319-isolated-20260807}"
: "${FRONTIER_BRANCH:=ci/fa339-frontier-20260808}"

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pass339-persistent-frontier'
PASS339_SHA='57f084029aff8e8a4b95d13e0daa9890eaa036716da48b3a3352ac3023be1c25'
ITERATION_FILE='build-logs/pass339-frontier-iteration.txt'
MAX_ITERATIONS=40

mkdir -p "${EVIDENCE}/logs" "${EVIDENCE}/source" "${EVIDENCE}/artifacts" "${OUTDIR}" build-logs
echo 'phase,pass,module,exit_code,error_count,warning_count,source_sha256' > "${EVIDENCE}/compile-summary.csv"

preserve_exit() {
  local code=$?
  mkdir -p "${EVIDENCE}/source"
  [[ -f "${FA}" ]] && cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-on-exit.lean" || true
  [[ -f "${FA}" ]] && sha256sum "${FA}" > "${EVIDENCE}/source/Mock2_FunctionalAnalysis-on-exit.sha256" || true
  git diff > "${EVIDENCE}/source/on-exit.patch" || true
  printf 'exit_code=%s\n' "${code}" > "${EVIDENCE}/exit-status.txt"
}
trap preserve_exit EXIT

compile_module() {
  local phase="$1" pass="$2" module="$3"
  local source="PrimalitySheafVerification/${module}.lean"
  local log="${EVIDENCE}/logs/${phase}-${module}-${pass}.log"
  local code errors warnings source_sha
  test -f "${source}"
  mkdir -p "${OUTDIR}"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" "${OUTDIR}/${module}.olean.private"
  source_sha="$(sha256sum "${source}" | awk '{print $1}')"
  set +e
  lake env lean -DmaxErrors=2000 "${source}" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s,%s,%s\n' "${phase}" "${pass}" "${module}" \
    "${code}" "${errors}" "${warnings}" "${source_sha}" >> "${EVIDENCE}/compile-summary.csv"
  if [[ "${code}" -ne 0 ]]; then
    {
      echo "phase=${phase} pass=${pass} module=${module} exit=${code} errors=${errors}"
      echo "source_sha256=${source_sha}"
      echo '--- first errors ---'; grep -n 'error:' "${log}" | head -120 || true
      echo '--- last errors ---'; grep -n 'error:' "${log}" | tail -80 || true
      echo '--- log tail ---'; tail -900 "${log}" || true
    } > "${EVIDENCE}/logs/${phase}-${module}-${pass}-failure-summary.txt"
    return "${code}"
  fi
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  ! grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" "${log}"
}

audit_sources() {
  python3 - "$@" <<'PY'
from pathlib import Path
import re,sys

def strip(s):
    out=[];i=0;depth=0;string=False;escaped=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            ch=s[i];out.append('\n' if ch=='\n' else ' ')
            if escaped:escaped=False
            elif ch=='\\':escaped=True
            elif ch=='"':string=False
            i+=1
        elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif s.startswith('--',i):
            while i<len(s) and s[i]!='\n':out.append(' ');i+=1
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    if depth or string:raise SystemExit('unterminated comment/string')
    return ''.join(out)
checks={'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b','Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
for raw in sys.argv[1:]:
    p=Path(raw); code=strip(p.read_text(encoding='utf-8'))
    print(f'[{p}]')
    for name,pat in checks.items():
        n=len(re.findall(pat,code));print(f'{name}={n}');bad|=n!=0
if bad:raise SystemExit('forbidden executable token detected')
PY
}

write_wrapper() {
  printf '%s\n' \
    '/-!' '# Mock2 FunctionalAnalysis compatibility entry point' '' \
    'The complete source-level implementation is stored in' \
    '`PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated`.' \
    'This module preserves the historical import path and re-exports the' \
    'same public declarations without duplicating their definitions.' '-/' \
    'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' > "${FA}"
}

mapfile -t mock3_files < <(find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print | sort)
printf '%s\n' "${mock3_files[@]:-}" > "${EVIDENCE}/mock3-files.txt"

try_final_gate() {
  local label="$1"
  local pass module file
  for pass in 1 2; do
    rm -rf "${OUTDIR}"; mkdir -p "${OUTDIR}"
    compile_module "${label}" "${pass}" Mock2 || return 1
    compile_module "${label}" "${pass}" Mock2_Advanced || return 1
    if grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "${FA}"; then
      compile_module "${label}" "${pass}" Mock2_FunctionalAnalysis_Integrated || return 1
      compile_module "${label}" "${pass}" Mock2_FunctionalAnalysis || return 1
    else
      compile_module "${label}" "${pass}" Mock2_FunctionalAnalysis || return 1
      [[ -f "${INTEGRATED}" ]] && compile_module "${label}" "${pass}" Mock2_FunctionalAnalysis_Integrated || true
    fi
    for file in "${mock3_files[@]}"; do
      module="$(basename "${file}" .lean)"
      compile_module "${label}" "${pass}" "${module}" || return 1
    done
    compile_module "${label}" "${pass}" QYM || return 1
  done
  return 0
}

printf '%s\n' \
  'authority=PASS339' "source_branch=${SOURCE_BRANCH}" "source_sha=${SOURCE_SHA}" \
  "target_branch=${TARGET_BRANCH}" "frontier_branch=${FRONTIER_BRANCH}" \
  "utc_started=$(date -u +%FT%TZ)" | tee "${EVIDENCE}/snapshot.txt"

# A previously materialized success is accepted only through a fresh two-pass gate.
if try_final_gate checked-in-final; then
  audit_sources "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" "${mock3_files[@]}" \
    | tee "${EVIDENCE}/trust-audit.txt"
  echo 'PASS339_PERSISTENT_GATE=ALREADY_SUCCESS' | tee "${EVIDENCE}/status.txt"
  exit 0
fi

# Frontier runs continue from their accepted full FA source. PR9 runs reconstruct
# the exact PASS339 source unless a large integrated implementation is already present.
if [[ "${SOURCE_BRANCH}" == "${FRONTIER_BRANCH}" ]]; then
  candidate_mode='persisted-frontier'
elif grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "${FA}" \
  && [[ $(wc -l < "${INTEGRATED}") -gt 1000 ]]; then
  cp "${INTEGRATED}" "${FA}"
  candidate_mode='integrated-frontier'
else
  set +e
  bash scripts/diagnose_pass339_fa.sh
  diagnostic_code=$?
  set -e
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${PASS339_SHA}"
  candidate_mode='reconstructed-pass339'
  printf 'diagnostic_code=%s\n' "${diagnostic_code}" | tee -a "${EVIDENCE}/snapshot.txt"
fi
echo "candidate_mode=${candidate_mode}" | tee -a "${EVIDENCE}/snapshot.txt"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-candidate-start.lean"
start_sha="$(sha256sum "${FA}" | awk '{print $1}')"

fa_pass=0
if compile_module frontier direct1 Mock2_FunctionalAnalysis; then
  compile_module frontier direct2 Mock2_FunctionalAnalysis
  fa_pass=1
fi

# Three bounded phases use the current accepted candidate as their own baseline.
if [[ "${fa_pass}" -ne 1 ]]; then
  for phase in 1 2 3; do
    current_sha="$(sha256sum "${FA}" | awk '{print $1}')"
    export PASS_BASELINE=339 BASELINE_PASS=339
    export BASELINE_SHA256="${current_sha}" EXPECTED_INPUT_SHA256="${current_sha}"
    export TARGET_FILE="${FA}" TARGET_SOURCE="${FA}" LEAN_FILE="${FA}"
    export TARGET_MODULE='Mock2_FunctionalAnalysis' MODULE='Mock2_FunctionalAnalysis'
    export PASS339_AGENT_ROUNDS=8
    case "${phase}" in 1) export PASS339_AGENT_MAX_ERRORS=12;; 2) export PASS339_AGENT_MAX_ERRORS=30;; *) export PASS339_AGENT_MAX_ERRORS=60;; esac
    export EVIDENCE_DIR="${EVIDENCE}/agent-phase-${phase}"
    export BRANCH="${FRONTIER_BRANCH}"
    export GH_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
    export MODELS_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
    mkdir -p "${EVIDENCE_DIR}"
    set +e
    python3 scripts/pass339_targeted_lean_repair_agent.py \
      2>&1 | tee "${EVIDENCE}/logs/targeted-agent-phase-${phase}.log"
    agent_code=${PIPESTATUS[0]}
    set -e
    printf 'agent_phase_%s_code=%s\n' "${phase}" "${agent_code}" | tee -a "${EVIDENCE}/snapshot.txt"
    if compile_module frontier "phase${phase}-1" Mock2_FunctionalAnalysis; then
      compile_module frontier "phase${phase}-2" Mock2_FunctionalAnalysis
      fa_pass=1
      break
    fi
  done
fi

# Existing project agents remain fallback-only and are still judged by direct Lean.
if [[ "${fa_pass}" -ne 1 ]]; then
  current_sha="$(sha256sum "${FA}" | awk '{print $1}')"
  export BASELINE_SHA256="${current_sha}" EXPECTED_INPUT_SHA256="${current_sha}"
  export TARGET_FILE="${FA}" TARGET_SOURCE="${FA}" LEAN_FILE="${FA}"
  export TARGET_MODULE='Mock2_FunctionalAnalysis' MODULE='Mock2_FunctionalAnalysis'
  export MAX_ROUNDS=24 MAX_AGENT_ROUNDS=24
  export EVIDENCE_DIR="${EVIDENCE}/fallback-agent"
  mkdir -p "${EVIDENCE_DIR}"
  for agent in scripts/pass327_lean_repair_agent_v3.py scripts/pass327_lean_repair_agent_v2.py; do
    [[ -f "${agent}" ]] || continue
    set +e
    python3 "${agent}" 2>&1 | tee -a "${EVIDENCE}/logs/fallback-agent.log"
    code=${PIPESTATUS[0]}
    set -e
    printf '%s=%s\n' "$(basename "${agent}")" "${code}" | tee -a "${EVIDENCE}/snapshot.txt"
    if compile_module frontier "fallback-$(basename "${agent}")-1" Mock2_FunctionalAnalysis; then
      compile_module frontier "fallback-$(basename "${agent}")-2" Mock2_FunctionalAnalysis
      fa_pass=1
      break
    fi
  done
fi

if [[ "${fa_pass}" -ne 1 ]]; then
  audit_sources "${ADVANCED}" "${FA}" "${QYM}" | tee "${EVIDENCE}/trust-audit-frontier.txt"
  final_sha="$(sha256sum "${FA}" | awk '{print $1}')"
  if [[ "${final_sha}" == "${start_sha}" ]]; then
    echo 'PASS339_PERSISTENT_GATE=STALLED_WITHOUT_PROGRESS' | tee "${EVIDENCE}/status.txt"
    exit 2
  fi
  iteration=0
  [[ -f "${ITERATION_FILE}" ]] && iteration="$(cat "${ITERATION_FILE}")"
  iteration=$((iteration + 1))
  test "${iteration}" -le "${MAX_ITERATIONS}"
  printf '%s\n' "${iteration}" > "${ITERATION_FILE}"
  cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-frontier-${iteration}.lean"
  git config user.name 'github-actions[bot]'
  git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
  git add "${FA}" "${ITERATION_FILE}"
  git commit -m "ci: persist PASS339 FA frontier iteration ${iteration}"
  git push --force-with-lease origin "HEAD:refs/heads/${FRONTIER_BRANCH}"
  echo "PASS339_PERSISTENT_GATE=FRONTIER_PUSHED_${iteration}" | tee "${EVIDENCE}/status.txt"
  exit 0
fi

echo 'fa_status=PASS_TWICE' | tee -a "${EVIDENCE}/snapshot.txt"

# Build the integrated implementation and compatibility wrapper only after FA passes twice.
cp "${FA}" "${INTEGRATED}"
write_wrapper
git diff --check
for pass in 1 2; do
  compile_module integrated "${pass}" Mock2_FunctionalAnalysis_Integrated
  compile_module integrated-wrapper "${pass}" Mock2_FunctionalAnalysis
  for file in "${mock3_files[@]}"; do compile_module mock3 "${pass}" "$(basename "${file}" .lean)"; done
done
echo 'integrated_mock3_status=PASS_TWICE' | tee -a "${EVIDENCE}/snapshot.txt"

# QYM must pass twice from a deleted project artifact directory.
for pass in 1 2; do
  rm -rf "${OUTDIR}"; mkdir -p "${OUTDIR}"
  compile_module qym-chain "${pass}" Mock2
  compile_module qym-chain "${pass}" Mock2_Advanced
  compile_module qym-chain "${pass}" Mock2_FunctionalAnalysis_Integrated
  compile_module qym-chain "${pass}" Mock2_FunctionalAnalysis
  for file in "${mock3_files[@]}"; do compile_module qym-chain "${pass}" "$(basename "${file}" .lean)"; done
  compile_module qym-chain "${pass}" QYM
done
echo 'qym_status=PASS_TWICE' | tee -a "${EVIDENCE}/snapshot.txt"

audit_sources "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" "${mock3_files[@]}" \
  | tee "${EVIDENCE}/trust-audit.txt"
cp "${FA}" /tmp/pass339-verified-wrapper.lean
cp "${INTEGRATED}" /tmp/pass339-verified-integrated.lean
cp "${QYM}" /tmp/pass339-verified-qym.lean
mkdir -p /tmp/pass339-verified-mock3
for file in "${mock3_files[@]}"; do cp "${file}" /tmp/pass339-verified-mock3/; done

# Promote only onto the latest PR9 head, then re-run the complete two-pass chain.
git fetch origin "refs/heads/${TARGET_BRANCH}:refs/remotes/origin/${TARGET_BRANCH}"
git checkout --detach "refs/remotes/origin/${TARGET_BRANCH}"
cp /tmp/pass339-verified-wrapper.lean "${FA}"
cp /tmp/pass339-verified-integrated.lean "${INTEGRATED}"
cp /tmp/pass339-verified-qym.lean "${QYM}"
for file in /tmp/pass339-verified-mock3/*.lean; do [[ -e "${file}" ]] || continue; cp "${file}" PrimalitySheafVerification/; done
mapfile -t mock3_files < <(find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print | sort)
try_final_gate promotion-recheck

audit_sources "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" "${mock3_files[@]}" \
  | tee "${EVIDENCE}/promotion-trust-audit.txt"
git diff --check
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}" "${INTEGRATED}" "${QYM}" "${mock3_files[@]}"
if ! git diff --cached --quiet; then
  git commit -m 'fix: materialize PASS339 verified FA Mock3 QYM chain'
  git push origin "HEAD:refs/heads/${TARGET_BRANCH}"
fi
sha256sum "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" "${mock3_files[@]}" \
  | tee "${EVIDENCE}/provenance-sha256.txt"
echo 'PASS339_PERSISTENT_GATE=SUCCESS' | tee "${EVIDENCE}/status.txt"
