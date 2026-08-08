#!/usr/bin/env bash
set -euo pipefail

MODE="${1:?usage: pass376_run_phase.sh MODE [BUDGET_SECONDS]}"
BUDGET_SECONDS="${2:-19000}"
BRANCH="${PASS376_BRANCH:-fix/pass376-self-driving-20260809}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "${ROOT}"

mkdir -p build-logs /tmp/pass376-multiphase
SUCCESS='build-logs/pass376-fa-mock3-qym-2x-pass.txt'
CYCLE_FILE='build-logs/pass376-multiphase-cycle.txt'

if test -s "${SUCCESS}"; then
  echo "[pass376-phase] ordered target gate already complete"
  exit 0
fi

cycle=0
if test -f "${CYCLE_FILE}"; then
  cycle="$(cat "${CYCLE_FILE}")"
fi
case "${cycle}" in
  ''|*[!0-9]*) cycle=0 ;;
esac

deadline=$(( $(date +%s) + BUDGET_SECONDS ))

checkpoint() {
  local label="$1"
  git config user.name 'github-actions[bot]'
  git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

  git add \
    build-logs/pass376-v2-state.json \
    build-logs/pass376-v2-baseline.json \
    build-logs/pass376-multiphase-cycle.txt \
    build-logs/pass376-fa-mock3-qym-2x-pass.txt \
    PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
    2>/dev/null || true

  if test -f PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean; then
    git add PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean
  fi
  while IFS= read -r -d '' file; do
    git add "${file}"
  done < <(find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print0)
  if test -f PrimalitySheafVerification/QYM.lean; then
    git add PrimalitySheafVerification/QYM.lean
  fi

  rm -f .aider.chat.history.md .aider.input.history .aider.conf.yml || true
  if ! git diff --cached --quiet; then
    if test -s "${SUCCESS}"; then
      git commit -m "fix: verify FA Integrated Mock3 QYM twice (${label})"
    else
      git commit -m "wip: advance PASS376 ${label}"
    fi
    git push origin "HEAD:${BRANCH}"
  fi
}

run_core() {
  local current="$1"
  local seconds="$2"
  set +e
  python3 scripts/pass376_multitarget_agent_v3.py \
    --cycle "${current}" --budget-seconds "${seconds}" \
    > "/tmp/pass376-multiphase/${MODE}-core-${current}.log" 2>&1
  local rc=$?
  set -e
  cat "/tmp/pass376-multiphase/${MODE}-core-${current}.log"
  return "${rc}"
}

run_tool() {
  local current="$1"
  local seconds="$2"
  set +e
  python3 scripts/pass376_tool_agent.py \
    --cycle "${current}" --budget-seconds "${seconds}" --max-turns 56 \
    > "/tmp/pass376-multiphase/${MODE}-tool-${current}.log" 2>&1
  local rc=$?
  set -e
  cat "/tmp/pass376-multiphase/${MODE}-tool-${current}.log"
  return "${rc}"
}

run_aider() {
  local current="$1"
  local seconds="$2"
  set +e
  python3 scripts/pass376_aider_architect_cycle.py \
    --cycle "${current}" --timeout-seconds "${seconds}" \
    > "/tmp/pass376-multiphase/${MODE}-aider-${current}.log" 2>&1
  local rc=$?
  set -e
  cat "/tmp/pass376-multiphase/${MODE}-aider-${current}.log"
  return "${rc}"
}

while test "$(date +%s)" -lt $((deadline - 900)); do
  cycle=$((cycle + 1))
  printf '%s\n' "${cycle}" > "${CYCLE_FILE}"
  echo "[pass376-phase] mode=${MODE} cycle=${cycle}"

  case "${MODE}" in
    core)
      remaining=$((deadline - $(date +%s) - 600))
      step=$(( remaining > 3600 ? 3600 : remaining ))
      test "${step}" -gt 300 || break
      run_core "${cycle}" "${step}" || true
      checkpoint "${MODE}-cycle-${cycle}"
      ;;

    tool)
      run_core "${cycle}" 650 || true
      checkpoint "${MODE}-pre-${cycle}"
      test -s "${SUCCESS}" && break
      remaining=$((deadline - $(date +%s) - 1300))
      step=$(( remaining > 4200 ? 4200 : remaining ))
      test "${step}" -gt 600 || break
      run_tool "${cycle}" "${step}" || true
      checkpoint "${MODE}-agent-${cycle}"
      test -s "${SUCCESS}" && break
      run_core "${cycle}" 650 || true
      checkpoint "${MODE}-post-${cycle}"
      ;;

    aider)
      run_core "${cycle}" 650 || true
      checkpoint "${MODE}-pre-${cycle}"
      test -s "${SUCCESS}" && break
      remaining=$((deadline - $(date +%s) - 1300))
      step=$(( remaining > 4200 ? 4200 : remaining ))
      test "${step}" -gt 600 || break
      run_aider "${cycle}" "${step}" || true
      checkpoint "${MODE}-agent-${cycle}"
      test -s "${SUCCESS}" && break
      run_core "${cycle}" 650 || true
      checkpoint "${MODE}-post-${cycle}"
      ;;

    mixed)
      run_core "${cycle}" 900 || true
      checkpoint "${MODE}-core-${cycle}"
      test -s "${SUCCESS}" && break
      remaining=$((deadline - $(date +%s) - 1300))
      if (( cycle % 2 == 0 )); then
        step=$(( remaining > 3600 ? 3600 : remaining ))
        test "${step}" -gt 600 || break
        run_tool "${cycle}" "${step}" || true
      else
        step=$(( remaining > 3600 ? 3600 : remaining ))
        test "${step}" -gt 600 || break
        run_aider "${cycle}" "${step}" || true
      fi
      checkpoint "${MODE}-agent-${cycle}"
      test -s "${SUCCESS}" && break
      run_core "${cycle}" 650 || true
      checkpoint "${MODE}-post-${cycle}"
      ;;

    *)
      echo "unknown mode: ${MODE}" >&2
      exit 64
      ;;
  esac

  if test -s "${SUCCESS}"; then
    echo "[pass376-phase] SUCCESS marker created in cycle ${cycle}"
    break
  fi
done

checkpoint "${MODE}-phase-final"

if test -s "${SUCCESS}"; then
  echo "[pass376-phase] complete=true"
else
  echo "[pass376-phase] complete=false"
fi
exit 0
