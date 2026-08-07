#!/usr/bin/env bash
set -euo pipefail

BRANCH='ci/fa319-isolated-20260807'
STATE='build-logs/pass327-agent-state.json'
SUCCESS='build-logs/pass327-targets-pass.json'
EVIDENCE='/tmp/pass327-repair-agent'
mkdir -p "${EVIDENCE}"

export PATH="${HOME}/.elan/bin:${PATH}"
export GH_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
export GITHUB_TOKEN="${GITHUB_TOKEN:-${GH_TOKEN:-}}"

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

# On the first run only, recover and compare the exact candidates attached to
# PASS 327.  Exit 20 means the best honest FA candidate is left in the working
# tree for the repair agent; zero means the four requested targets already pass.
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
fi

# The agent only accepts a patch after a fresh direct compile demonstrates a
# smaller error frontier or a later first error.  It checkpoints honest progress
# to PR #9 and returns 20 when another run is required.
set +e
python3 scripts/pass327_lean_repair_agent.py \
  --max-rounds-per-target 28 --minutes 315 \
  > >(tee "${EVIDENCE}/agent-console.log") 2>&1
agent_rc=$?
set -e

echo "agent_exit=${agent_rc}" | tee -a "${EVIDENCE}/orchestrator-provenance.txt"

# Commit any local checkpoint created by the agent.  The state-file push is the
# explicit resume trigger.  No final-source PASS is claimed by a checkpoint.
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
if ! git diff --quiet || ! git diff --cached --quiet; then
  git add PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
    PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \
    PrimalitySheafVerification/QYM.lean \
    build-logs/pass327-agent-state.json \
    build-logs/pass327-targets-pass.json 2>/dev/null || true
  find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print0 \
    | xargs -0 -r git add
  git diff --cached --quiet || git commit -m 'wip: checkpoint PASS 327 FA Mock3 QYM repair'
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
