#!/usr/bin/env bash
set -euo pipefail

BRANCH='ci/fa319-isolated-20260807'
STATE='build-logs/pass327-agent-state.json'
SUCCESS='build-logs/pass327-targets-pass.json'
EVIDENCE='/tmp/pass327-repair-agent'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
mkdir -p "${EVIDENCE}"

export PATH="${HOME}/.elan/bin:${PATH}"
export GH_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
export GITHUB_TOKEN="${GITHUB_TOKEN:-${GH_TOKEN:-}}"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

trigger_head="$(git rev-parse HEAD)"
remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
printf '%s\n' \
  "trigger_head=${trigger_head}" \
  "remote_head=${remote_head}" \
  "branch=${BRANCH}" \
  "utc=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/orchestrator-provenance.txt"
test "${remote_head}" = "${trigger_head}"

if [[ -f "${SUCCESS}" ]]; then
  echo 'PASS 327 target gate already complete; nothing to repair.' | tee "${EVIDENCE}/status.txt"
  exit 0
fi

if [[ ! -f "${STATE}" ]]; then
  set +e
  bash scripts/ci_pass327_fa_qym_recovery.sh \
    > >(tee "${EVIDENCE}/pass327-recovery.log") 2>&1
  recovery_rc=$?
  set -e
  echo "recovery_exit=${recovery_rc}" | tee -a "${EVIDENCE}/orchestrator-provenance.txt"
  case "${recovery_rc}" in
    0)
      echo 'PASS 327 recovery itself completed the requested target gate.' \
        | tee "${EVIDENCE}/status.txt"
      exit 0
      ;;
    20)
      ;;
    *)
      echo "PASS 327 recovery failed before producing a valid FA frontier (rc=${recovery_rc})." \
        | tee "${EVIDENCE}/status.txt"
      exit "${recovery_rc}"
      ;;
  esac

  # The recovery script leaves the exact best Advanced and FA candidates in the
  # worktree.  Commit both together so a later checkpoint/restart cannot lose
  # the PASS 327 dependency source while retaining only the FA state file.
  git add "${ADVANCED}" "${FA}"
  if ! git diff --cached --quiet; then
    git commit -m 'wip: preserve recovered PASS 327 Advanced and FA candidates'
  fi
fi

set +e
python3 scripts/pass327_lean_repair_agent.py \
  --max-rounds-per-target 28 --minutes 315 \
  > >(tee "${EVIDENCE}/agent-console.log") 2>&1
agent_rc=$?
set -e

echo "agent_exit=${agent_rc}" | tee -a "${EVIDENCE}/orchestrator-provenance.txt"

# Include all four priority layers in every honest checkpoint.  This does not
# call a failing candidate PASS; it only preserves compile-improving progress.
git add "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  build-logs/pass327-agent-state.json \
  build-logs/pass327-targets-pass.json 2>/dev/null || true
find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print0 \
  | xargs -0 -r git add
if ! git diff --cached --quiet; then
  git commit -m 'wip: checkpoint PASS 327 Advanced FA Mock3 QYM repair'
fi

new_head="$(git rev-parse HEAD)"
current_remote="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
if [[ "${new_head}" != "${trigger_head}" ]]; then
  test "${current_remote}" = "${trigger_head}"
  git push origin "HEAD:${BRANCH}"
fi

case "${agent_rc}" in
  0)
    test -f "${SUCCESS}"
    echo 'PASS_327_FA_MOCK3_QYM_COMPLETE' | tee "${EVIDENCE}/status.txt"
    exit 0
    ;;
  20)
    echo 'PASS_327_REPAIR_CHECKPOINT_PUSHED' | tee "${EVIDENCE}/status.txt"
    exit 0
    ;;
  *)
    echo "PASS_327_AGENT_FAILED rc=${agent_rc}" | tee "${EVIDENCE}/status.txt"
    exit "${agent_rc}"
    ;;
esac
