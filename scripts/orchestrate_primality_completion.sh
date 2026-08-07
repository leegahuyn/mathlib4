#!/usr/bin/env bash
set -euo pipefail

: "${SOURCE_SHA:?}"
: "${BRANCH:?}"
: "${PR_NUMBER:?}"
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_TOKEN:?}"

MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
LOGDIR='/tmp/primality-completion-orchestrator'
mkdir -p "${OUTDIR}" "${LOGDIR}/logs"

test "$(git rev-parse HEAD)" = "${SOURCE_SHA}"
printf '%s\n' \
  "source_sha=${SOURCE_SHA}" \
  "branch=${BRANCH}" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${LOGDIR}/snapshot.txt"

compile_probe() {
  local path="$1" label="$2" module log code errors
  module="$(basename "${path}" .lean)"
  log="${LOGDIR}/logs/${label}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "${path}" -o "${OUTDIR}/${module}.olean" \
    -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  printf '%s,%s,%s\n' "${label}" "${code}" "${errors}" \
    >> "${LOGDIR}/probe-summary.csv"
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

echo 'stage,exit_code,error_count' > "${LOGDIR}/probe-summary.csv"
compile_probe "${MOCK2}" Mock2

set +e
compile_probe "${ADVANCED}" Mock2_Advanced
advanced_code=$?
set -e
if [[ "${advanced_code}" -ne 0 ]]; then
  echo 'Mock2_Advanced requires bounded v4 materialization.' | tee "${LOGDIR}/decision.txt"
  sed \
    -e 's#adaptive_mock2_advanced_universe_repair_v2.py#adaptive_mock2_advanced_universe_repair_v4.py#g' \
    -e 's#/tmp/adaptive-mock2-advanced-v2#/tmp/adaptive-mock2-advanced-orchestrated#g' \
    -e 's#seq 1 48#seq 1 16#g' \
    scripts/ci_adaptive_mock2_advanced_v2.sh \
    > /tmp/ci_adaptive_mock2_advanced_orchestrated.sh
  bash /tmp/ci_adaptive_mock2_advanced_orchestrated.sh
  new_remote="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
  if [[ "${new_remote}" != "${SOURCE_SHA}" ]]; then
    echo "Advanced materialized at ${new_remote}; next push will resume orchestration." \
      | tee "${LOGDIR}/status.txt"
    exit 0
  fi
  # The repair driver can return without a push only when the checked-in source
  # has become directly valid during a concurrent earlier materialization.
  compile_probe "${ADVANCED}" Mock2_Advanced-after-driver
fi

set +e
compile_probe "${FA}" Mock2_FunctionalAnalysis
fa_code=$?
set -e
if [[ "${fa_code}" -ne 0 ]]; then
  echo 'Mock2_FunctionalAnalysis requires deterministic pass-315 materialization.' \
    | tee "${LOGDIR}/decision.txt"
  bash scripts/ci_materialize_mock2_functional_analysis.sh
  new_remote="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
  if [[ "${new_remote}" != "${SOURCE_SHA}" ]]; then
    echo "FunctionalAnalysis materialized at ${new_remote}; next push will resume orchestration." \
      | tee "${LOGDIR}/status.txt"
    exit 0
  fi
  compile_probe "${FA}" Mock2_FunctionalAnalysis-after-driver
fi

compile_probe "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated
compile_probe "${QYM}" QYM

echo 'Focused dependency chain passes; entering full non-mutating clean gate.' \
  | tee "${LOGDIR}/decision.txt"
PRIMALITY_SHEAF_LOGDIR='/tmp/primality-orchestrator-full-gate' \
  bash scripts/primality_sheaf_ci.sh

# Full gate passed. Use the latest hardened finalizer implementation. It repeats
# the gate, removes temporary infrastructure, installs the single official CI,
# waits for that exact commit to pass, updates the PR evidence, and marks Ready.
sed \
  -e 's#scripts/primality-sheaf-ci.final-v2.yml#scripts/primality-sheaf-ci.final-v3.yml#g' \
  -e 's#origin/master\.\.\.HEAD#origin/master HEAD#g' \
  scripts/finalize_primality_sheaf_pr_v2.sh \
  > /tmp/finalize_primality_sheaf_pr_orchestrated.sh
bash /tmp/finalize_primality_sheaf_pr_orchestrated.sh

echo 'Full clean build, official CI, and Ready-for-Review transition completed.' \
  | tee "${LOGDIR}/status.txt"
