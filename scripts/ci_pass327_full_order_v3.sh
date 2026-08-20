#!/usr/bin/env bash
set -euo pipefail

PR9_BRANCH='ci/fa319-isolated-20260807'
PR7_BRANCH='fix/primality-sheaf-clean-build'
PRIORITY='build-logs/pass327-targets-pass.json'
PRIORITY_STATE='build-logs/pass327-agent-state.json'
MOCK1='build-logs/mock1-family-pass.json'
MOCK1_STATE='build-logs/post-priority-agent-state.json'
FINAL_LOCAL='build-logs/final-local-gate-pass.json'
FINAL_DEP_STATE='build-logs/final-dependency-agent-state.json'
EVIDENCE='/tmp/pass327-full-order-v3'
mkdir -p "${EVIDENCE}" "${EVIDENCE}/logs"

export PATH="${HOME}/.elan/bin:${PATH}"
export GH_TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
export GITHUB_TOKEN="${GITHUB_TOKEN:-${GH_TOKEN:-}}"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

require_pass() {
  python3 - "$1" <<'PY'
import json,sys
p=sys.argv[1]
data=json.load(open(p,encoding='utf-8'))
if data.get('status')!='PASS': raise SystemExit(f'{p} is not PASS: {data}')
PY
}

priority_paths=(
  PrimalitySheafVerification/Mock2_Advanced.lean
  PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean
  PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean
  PrimalitySheafVerification/QYM.lean
)
mock1_paths=(
  PrimalitySheafVerification/Mock1.lean
  PrimalitySheafVerification/Mock1_Advanced.lean
)
state_paths=(
  "${PRIORITY}" "${PRIORITY_STATE}" "${MOCK1}" "${MOCK1_STATE}"
  "${FINAL_LOCAL}" "${FINAL_DEP_STATE}"
  build-logs/final-dependency-repair-pass.json
)

stage_and_commit() {
  local message="$1"
  shift
  local paths=("$@")
  for path in "${paths[@]}"; do
    [[ -e "${path}" ]] && git add -- "${path}"
  done
  find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print0 \
    | xargs -0 -r git add
  if ! git diff --cached --quiet; then
    git commit -m "${message}"
  fi
}

push_pr9_checkpoint() {
  local trigger_head="$1"
  local new_head remote_head
  new_head="$(git rev-parse HEAD)"
  remote_head="$(git ls-remote origin "refs/heads/${PR9_BRANCH}" | awk '{print $1}')"
  if [[ "${new_head}" != "${trigger_head}" ]]; then
    test "${remote_head}" = "${trigger_head}"
    git push origin "HEAD:${PR9_BRANCH}"
  fi
}

cancel_branch_runs() {
  local branch="$1"
  gh api --paginate \
    "repos/${GITHUB_REPOSITORY}/actions/runs?branch=${branch}&per_page=100" \
    --jq '.workflow_runs[] | select(.status == "queued" or .status == "in_progress" or .status == "pending") | .id' \
    | sort -u \
    | while IFS= read -r run_id; do
        [[ -n "${run_id}" ]] || continue
        [[ "${run_id}" = "${GITHUB_RUN_ID}" ]] && continue
        gh api -X POST "repos/${GITHUB_REPOSITORY}/actions/runs/${run_id}/cancel" \
          >/dev/null 2>&1 || true
      done
}

trigger_head="$(git rev-parse HEAD)"
remote_head="$(git ls-remote origin "refs/heads/${PR9_BRANCH}" | awk '{print $1}')"
test "${remote_head}" = "${trigger_head}"
printf '%s\n' \
  "trigger_head=${trigger_head}" \
  "remote_head=${remote_head}" \
  "utc=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/provenance.txt"

# ---------------------------------------------------------------------------
# Stage 1: PASS 327 priority targets.  Nothing below runs without this marker.
# ---------------------------------------------------------------------------
if [[ ! -f "${PRIORITY}" ]]; then
  if [[ ! -f "${PRIORITY_STATE}" ]]; then
    set +e
    bash scripts/ci_pass327_fa_qym_recovery.sh \
      > >(tee "${EVIDENCE}/logs/pass327-recovery.log") 2>&1
    recovery_rc=$?
    set -e
    case "${recovery_rc}" in
      0)
        ;;
      20)
        stage_and_commit \
          'wip: preserve recovered PASS 327 Advanced and FA candidates' \
          "${priority_paths[@]}"
        ;;
      *)
        echo "PASS 327 recovery failed rc=${recovery_rc}" >&2
        exit "${recovery_rc}"
        ;;
    esac
  fi

  if [[ ! -f "${PRIORITY}" ]]; then
    set +e
    python3 scripts/pass327_lean_repair_agent.py \
      --max-rounds-per-target 28 --minutes 305 \
      > >(tee "${EVIDENCE}/logs/priority-agent.log") 2>&1
    agent_rc=$?
    set -e
    stage_and_commit \
      'wip: checkpoint PASS 327 Advanced FA Mock3 QYM repair' \
      "${priority_paths[@]}" "${PRIORITY}" "${PRIORITY_STATE}"
    if [[ "${agent_rc}" -eq 20 ]]; then
      push_pr9_checkpoint "${trigger_head}"
      echo 'PRIORITY_CHECKPOINT_PUSHED' | tee "${EVIDENCE}/status.txt"
      exit 0
    fi
    test "${agent_rc}" -eq 0
  fi
fi
require_pass "${PRIORITY}"

# ---------------------------------------------------------------------------
# Stage 2: Mock1 family, only after all four priority layers pass twice.
# ---------------------------------------------------------------------------
if [[ ! -f "${MOCK1}" ]]; then
  set +e
  python3 scripts/post_priority_lean_repair_agent.py \
    --minutes 305 --rounds 28 \
    > >(tee "${EVIDENCE}/logs/mock1-agent.log") 2>&1
  mock1_rc=$?
  set -e
  stage_and_commit \
    'wip: checkpoint Mock1 family direct-source repair' \
    "${mock1_paths[@]}" "${MOCK1}" "${MOCK1_STATE}"
  if [[ "${mock1_rc}" -eq 20 ]]; then
    push_pr9_checkpoint "${trigger_head}"
    echo 'MOCK1_CHECKPOINT_PUSHED' | tee "${EVIDENCE}/status.txt"
    exit 0
  fi
  test "${mock1_rc}" -eq 0
fi
require_pass "${MOCK1}"

# ---------------------------------------------------------------------------
# Stage 3: BuildAll dependencies, two clean rebuilds, and Spt5 whole-file audit.
# ---------------------------------------------------------------------------
if [[ ! -f "${FINAL_LOCAL}" ]]; then
  set +e
  FINAL_EVIDENCE_DIR="${EVIDENCE}/pr9-final-gate" \
    bash scripts/primality_final_local_gate_v2.sh \
    > >(tee "${EVIDENCE}/logs/pr9-final-local-gate.log") 2>&1
  gate_rc=$?
  set -e
  if [[ "${gate_rc}" -ne 0 ]]; then
    summary="${EVIDENCE}/pr9-final-gate/compile-summary.csv"
    failed_module=''
    if [[ -s "${summary}" ]]; then
      failed_module="$(python3 - "${summary}" <<'PY'
import csv,sys
rows=list(csv.DictReader(open(sys.argv[1],encoding='utf-8')))
failed=[r for r in rows if r.get('exit_code')!='0' or r.get('error_count')!='0']
print(failed[-1]['module'] if failed else '')
PY
)"
    fi
    if [[ -n "${failed_module}" && -f "PrimalitySheafVerification/${failed_module}.lean" ]]; then
      set +e
      python3 scripts/final_dependency_repair_agent.py \
        "PrimalitySheafVerification/${failed_module}.lean" \
        --minutes 305 --rounds 28 \
        > >(tee "${EVIDENCE}/logs/final-dependency-${failed_module}.log") 2>&1
      dep_rc=$?
      set -e
      stage_and_commit \
        "wip: checkpoint final dependency repair for ${failed_module}" \
        "PrimalitySheafVerification/${failed_module}.lean" \
        "${FINAL_DEP_STATE}" build-logs/final-dependency-repair-pass.json
      if [[ "${dep_rc}" -eq 20 || "${dep_rc}" -eq 0 ]]; then
        push_pr9_checkpoint "${trigger_head}"
        echo "FINAL_DEPENDENCY_CHECKPOINT_${failed_module}" | tee "${EVIDENCE}/status.txt"
        exit 0
      fi
      exit "${dep_rc}"
    fi
    echo 'Final local gate failed outside an addressable module compile; preserving evidence.' >&2
    exit "${gate_rc}"
  fi
  stage_and_commit \
    'ci: PASS two clean rebuilds and Spt5 whole-file audit on PR9' \
    "${FINAL_LOCAL}"
  # Split the expensive verified local gate from the PR7 transfer into a fresh
  # run, ensuring the exact PASS commit is persisted first.
  push_pr9_checkpoint "${trigger_head}"
  echo 'PR9_FINAL_LOCAL_GATE_CHECKPOINT_PUSHED' | tee "${EVIDENCE}/status.txt"
  exit 0
fi
require_pass "${FINAL_LOCAL}"

# ---------------------------------------------------------------------------
# Stage 4: Transfer only verified sources to PR7, rerun the exact final gate,
# install the single patch-free official CI, wait for green, and mark ready.
# ---------------------------------------------------------------------------
cancel_branch_runs "${PR7_BRANCH}"
git fetch origin "${PR7_BRANCH}"
pr7_base="$(git rev-parse "origin/${PR7_BRANCH}")"
worktree='/tmp/primality-pr7-final'
rm -rf "${worktree}"
git worktree add --detach "${worktree}" "${pr7_base}"

copy_to_pr7() {
  local path="$1"
  [[ -e "${path}" ]] || return 0
  mkdir -p "${worktree}/$(dirname "${path}")"
  cp -a "${path}" "${worktree}/${path}"
}

for path in \
  PrimalitySheafVerification/Mock2_Advanced.lean \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \
  PrimalitySheafVerification/QYM.lean \
  PrimalitySheafVerification/Mock1.lean \
  PrimalitySheafVerification/Mock1_Advanced.lean \
  PrimalitySheafVerification/BuildAll.lean \
  scripts/primality_final_local_gate.sh \
  scripts/primality_final_local_gate_v2.sh \
  scripts/generate_spt5_whole_file_audit.py \
  scripts/install_primality_official_ci.py \
  "${PRIORITY}" "${MOCK1}" "${FINAL_LOCAL}"; do
  copy_to_pr7 "${path}"
done
while IFS= read -r path; do copy_to_pr7 "${path}"; done \
  < <(find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' | sort)

cd "${worktree}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

FINAL_EVIDENCE_DIR="${EVIDENCE}/pr7-final-gate" \
  bash scripts/primality_final_local_gate_v2.sh \
  > >(tee "${EVIDENCE}/logs/pr7-final-local-gate.log") 2>&1
python3 scripts/install_primality_official_ci.py \
  > >(tee "${EVIDENCE}/logs/install-official-ci.log") 2>&1
bash -n scripts/primality_official_ci_driver.sh
python3 -m py_compile scripts/generate_spt5_whole_file_audit.py scripts/install_primality_official_ci.py

git add -A
if git diff --cached --quiet; then
  echo 'No verified transfer changes were produced.' >&2
  exit 1
fi
git commit -m 'fix: finalize all PrimalitySheafVerification clean builds and official CI'
final_sha="$(git rev-parse HEAD)"
latest_remote="$(git ls-remote origin "refs/heads/${PR7_BRANCH}" | awk '{print $1}')"
test "${latest_remote}" = "${pr7_base}"
git push origin "HEAD:${PR7_BRANCH}"

# Wait for the official patch-free CI attached to the exact final commit.
official_run=''
for _ in $(seq 1 300); do
  runs_json="$(gh api "repos/${GITHUB_REPOSITORY}/actions/runs?head_sha=${final_sha}&per_page=100")"
  official_run="$(python3 -c 'import json,sys; d=json.load(sys.stdin); xs=[r for r in d.get("workflow_runs",[]) if r.get("name")=="PrimalitySheafVerification official clean CI"]; xs.sort(key=lambda r:r.get("created_at","") ,reverse=True); print(xs[0]["id"] if xs else "")' <<<"${runs_json}")"
  if [[ -n "${official_run}" ]]; then
    status="$(gh api "repos/${GITHUB_REPOSITORY}/actions/runs/${official_run}" --jq .status)"
    conclusion="$(gh api "repos/${GITHUB_REPOSITORY}/actions/runs/${official_run}" --jq '.conclusion // ""')"
    printf '%s,%s,%s,%s\n' "$(date -u +%FT%TZ)" "${official_run}" "${status}" "${conclusion}" \
      | tee -a "${EVIDENCE}/official-ci-poll.csv"
    if [[ "${status}" = 'completed' ]]; then
      test "${conclusion}" = 'success'
      break
    fi
  fi
  sleep 60
done
test -n "${official_run}"
test "$(gh api "repos/${GITHUB_REPOSITORY}/actions/runs/${official_run}" --jq .status)" = 'completed'
test "$(gh api "repos/${GITHUB_REPOSITORY}/actions/runs/${official_run}" --jq .conclusion)" = 'success'

# Record the final evidence in PR #7 and change only draft readiness, never merge.
current_body="$(gh pr view 7 --repo "${GITHUB_REPOSITORY}" --json body --jq .body)"
cat > /tmp/pr7-final-body.md <<EOF
## Final clean-build status: PASS

- Final verified commit: \`${final_sha}\`
- Official CI run: \`${official_run}\`
- Mock2 Advanced, Mock2 FunctionalAnalysis, Integrated/Mock3 bridge, and QYM: direct-source PASS twice
- Mock1 and Mock1 Advanced: direct-source PASS twice
- All 13 modules and BuildAll: project artifacts deleted and rebuilt successfully twice
- Spt5 whole-file public declaration axiom audit: PASS
- Allowed axioms only: \`propext\`, \`Classical.choice\`, \`Quot.sound\`
- Runtime Lean source repair in official CI: none
- Automatic merge: not performed

${current_body}
EOF
gh pr edit 7 --repo "${GITHUB_REPOSITORY}" --body-file /tmp/pr7-final-body.md
gh pr ready 7 --repo "${GITHUB_REPOSITORY}"
gh pr comment 7 --repo "${GITHUB_REPOSITORY}" --body \
  "Final direct-source clean gate passed at ${final_sha}; official workflow run ${official_run} succeeded. PR changed from draft to ready for review. It was not merged."

gh pr close 9 --repo "${GITHUB_REPOSITORY}" --comment \
  "PASS 327 verified sources were transferred to PR #7. PR #9 is closed without merge after the official PR #7 clean CI succeeded."

printf '%s\n' \
  "status=COMPLETE" \
  "pr7_final_sha=${final_sha}" \
  "official_run=${official_run}" \
  "pr7_ready=true" \
  "merged=false" \
  | tee "${EVIDENCE}/FINAL_STATUS.txt"
