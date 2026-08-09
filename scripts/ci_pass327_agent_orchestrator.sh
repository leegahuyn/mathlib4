#!/usr/bin/env bash
set -euo pipefail

BRANCH='ci/fa319-isolated-20260807'
STATE='build-logs/pass327-agent-state.json'
SUCCESS='build-logs/pass327-targets-pass.json'
EVIDENCE='/tmp/pass327-repair-agent'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
PASS333_SHA='8c0b0797155d3ae4f8f05b2d38d36552a629c900b8e990aba1ff44b666b72e45'
PASS334_SHA='7a179ce46bcb210dbd8cbf30a19aeb7da65ffed24709a8844bf4a244a8e65de5'
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

# Start the autonomous repair loop from the newest deterministic source chain,
# not from the historical PASS 320 artifact.  The diagnostic driver leaves the
# reconstructed PASS 333 source in the working tree even though its compile is
# expected to return nonzero; PASS 334 is then applied and hash-verified.
if [[ ! -f "${STATE}" ]]; then
  set +e
  bash scripts/diagnose_pass333_fa.sh \
    > >(tee "${EVIDENCE}/pass333-reconstruction.log") 2>&1
  pass333_compile_rc=$?
  set -e
  pass333_actual="$(sha256sum "${FA}" | awk '{print $1}')"
  printf '%s\n' \
    "pass333_compile_exit=${pass333_compile_rc}" \
    "pass333_source_sha256=${pass333_actual}" \
    | tee -a "${EVIDENCE}/orchestrator-provenance.txt"
  test "${pass333_actual}" = "${PASS333_SHA}"

  python3 scripts/apply_three_hundred_thirty_fourth_pass_functional_analysis_repairs.py \
    2>&1 | tee "${EVIDENCE}/pass334-apply.log"
  pass334_actual="$(sha256sum "${FA}" | awk '{print $1}')"
  echo "pass334_source_sha256=${pass334_actual}" \
    | tee -a "${EVIDENCE}/orchestrator-provenance.txt"
  test "${pass334_actual}" = "${PASS334_SHA}"
fi

# The agent only accepts a patch after a fresh direct compile demonstrates a
# smaller error frontier or a later first error. It also rejects theorem-header
# changes and every forbidden proof escape before checkpointing progress.
set +e
python3 scripts/pass327_lean_repair_agent.py \
  --max-rounds-per-target 28 --minutes 315 \
  > >(tee "${EVIDENCE}/agent-console.log") 2>&1
agent_rc=$?
set -e

echo "agent_exit=${agent_rc}" | tee -a "${EVIDENCE}/orchestrator-provenance.txt"

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
  git diff --cached --quiet || git commit -m 'wip: checkpoint PASS 334 FA Mock3 QYM repair'
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
    echo 'PASS_334_FA_MOCK3_QYM_COMPLETE' | tee "${EVIDENCE}/status.txt"
    exit 0
    ;;
  20)
    echo 'PASS_334_REPAIR_CHECKPOINT_PUSHED' | tee "${EVIDENCE}/status.txt"
    exit 0
    ;;
  *)
    echo "PASS_334_AGENT_FAILED rc=${agent_rc}" | tee "${EVIDENCE}/status.txt"
    exit "${agent_rc}"
    ;;
esac
