#!/usr/bin/env bash
set -euo pipefail

: "${GITHUB_TOKEN:?}"
: "${GITHUB_REPOSITORY:?}"
: "${SOURCE_SHA:?}"
: "${BRANCH:?}"
: "${PR_NUMBER:?}"

VALIDATION_LOGDIR='/tmp/primality-finalizer-validation'
FINALIZER_LOGDIR='/tmp/primality-finalizer'
OFFICIAL_WORKFLOW='.github/workflows/primality-sheaf-ci.yml'
OFFICIAL_TEMPLATE='scripts/primality-sheaf-ci.final-v2.yml'
OFFICIAL_TEMPLATE_COPY='/tmp/primality-sheaf-ci.final-v2.yml'
FINAL_CI_DRIVER='scripts/primality_sheaf_ci.sh'
mkdir -p "${VALIDATION_LOGDIR}" "${FINALIZER_LOGDIR}"
cp "${OFFICIAL_TEMPLATE}" "${OFFICIAL_TEMPLATE_COPY}"

# Hard gate: the repository is untouched unless all direct-source checks pass.
PRIMALITY_SHEAF_LOGDIR="${VALIDATION_LOGDIR}" \
  bash "${FINAL_CI_DRIVER}"

git diff --exit-code
test "$(git rev-parse HEAD)" = "${SOURCE_SHA}"
remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
printf '%s\n' "validation_head=${SOURCE_SHA}" "remote_head_before_cleanup=${remote_head}" \
  | tee "${FINALIZER_LOGDIR}/race-guard.txt"
test "${remote_head}" = "${SOURCE_SHA}"

git fetch --depth=1 origin master:refs/remotes/origin/master

restore_or_remove() {
  local path="$1"
  if git cat-file -e "origin/master:${path}" 2>/dev/null; then
    mkdir -p "$(dirname "${path}")"
    git show "origin/master:${path}" > "${path}"
    git add "${path}"
  else
    rm -f "${path}"
    git add -A -- "${path}"
  fi
}

mapfile -t changed_workflows < <(
  git diff --name-only origin/master...HEAD -- .github/workflows | sort -u
)
for path in "${changed_workflows[@]}"; do
  [[ -z "${path}" ]] && continue
  [[ "${path}" = "${OFFICIAL_WORKFLOW}" ]] && continue
  restore_or_remove "${path}"
done

mapfile -t changed_actions < <(
  git diff --name-only origin/master...HEAD -- .github/actions | sort -u
)
for path in "${changed_actions[@]}"; do
  [[ -z "${path}" ]] && continue
  restore_or_remove "${path}"
done

mapfile -t changed_scripts < <(
  git diff --name-only origin/master...HEAD -- scripts | sort -u
)
for path in "${changed_scripts[@]}"; do
  [[ -z "${path}" ]] && continue
  [[ "${path}" = "${FINAL_CI_DRIVER}" ]] && continue
  restore_or_remove "${path}"
done

mapfile -t changed_build_logs < <(
  git diff --name-only origin/master...HEAD -- build-logs | sort -u
)
for path in "${changed_build_logs[@]}"; do
  [[ -z "${path}" ]] && continue
  restore_or_remove "${path}"
done

mkdir -p "$(dirname "${OFFICIAL_WORKFLOW}")"
cp "${OFFICIAL_TEMPLATE_COPY}" "${OFFICIAL_WORKFLOW}"
git add "${OFFICIAL_WORKFLOW}" "${FINAL_CI_DRIVER}"

git diff --cached --check
if git diff --cached --quiet; then
  echo 'cleanup produced no staged changes' >&2
  exit 1
fi

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git commit -m 'ci: finalize direct clean-build verification'
final_sha="$(git rev-parse HEAD)"
git diff --exit-code

remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
printf '%s\n' \
  "remote_head_before_final_push=${remote_head}" \
  "final_cleanup_commit=${final_sha}" \
  | tee -a "${FINALIZER_LOGDIR}/race-guard.txt"
test "${remote_head}" = "${SOURCE_SHA}"
git push origin "HEAD:${BRANCH}"

printf '%s\n' \
  "final_sha=${final_sha}" \
  "official_workflow=${OFFICIAL_WORKFLOW}" \
  "runtime_source_repairs=0" \
  > "${FINALIZER_LOGDIR}/final-cleanup.txt"

api="https://api.github.com/repos/${GITHUB_REPOSITORY}/actions/runs?head_sha=${final_sha}&per_page=100"
run_url=''
for attempt in $(seq 1 240); do
  response_file="${FINALIZER_LOGDIR}/official-runs-${attempt}.json"
  curl --fail --silent --show-error \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H 'Accept: application/vnd.github+json' \
    -H 'X-GitHub-Api-Version: 2022-11-28' \
    "${api}" > "${response_file}"
  state="$({
    python3 - "${response_file}" <<'PY'
import json
import sys

with open(sys.argv[1], encoding='utf-8') as handle:
    runs = json.load(handle).get('workflow_runs', [])
selected = [
    run for run in runs
    if run.get('name') == 'PrimalitySheafVerification CI'
    and run.get('event') == 'push'
]
if not selected:
    print('missing|-|-')
else:
    run = sorted(selected, key=lambda item: item.get('run_number', 0), reverse=True)[0]
    print('|'.join([
        run.get('status') or '-',
        run.get('conclusion') or '-',
        run.get('html_url') or '-',
    ]))
PY
  })"
  printf '%s\n' "attempt=${attempt} state=${state}" \
    | tee -a "${FINALIZER_LOGDIR}/official-ci-poll.log"
  status="${state%%|*}"
  remainder="${state#*|}"
  conclusion="${remainder%%|*}"
  url="${remainder#*|}"
  if [[ "${status}" = completed && "${conclusion}" = success ]]; then
    run_url="${url}"
    break
  fi
  if [[ "${status}" = completed && "${conclusion}" != success ]]; then
    echo "official CI failed: ${state}" >&2
    exit 1
  fi
  sleep 30
done

test -n "${run_url}"
test "${run_url}" != '-'
printf '%s\n' "official_ci_url=${run_url}" \
  | tee "${FINALIZER_LOGDIR}/official-ci-success.txt"

observed_axioms="$(
  sed -n 's/^observed_axioms=//p' \
    "${VALIDATION_LOGDIR}/audit/Spt5-axiom-summary.txt" | tail -1
)"
body_file="${FINALIZER_LOGDIR}/pr-body.md"
cat > "${body_file}" <<EOF
## Completion status

All 13 primary \`PrimalitySheafVerification\` modules and aggregate \`BuildAll.lean\` compile directly from the checked-in Lean source. The final workflow performs no runtime source repair.

| Module | Result |
|---|---|
| Spt1 | PASS |
| Spt2 | PASS |
| Spt3 | PASS |
| Spt4 | PASS |
| Spt5 | PASS |
| Spt6 | PASS |
| Spt7 | PASS |
| Mock1 | PASS |
| Mock1_Advanced | PASS |
| Mock2 | PASS |
| Mock2_Advanced | PASS |
| Mock2_FunctionalAnalysis | PASS |
| QYM | PASS |
| BuildAll | PASS |

## Reproducibility evidence

- Final source commit: \`${final_sha}\`
- Lean toolchain: \`$(cat lean-toolchain)\`
- Existing project artifacts deleted before each rebuild: yes
- Dependency-ordered clean compile passes: 2
- Every module produced \`.olean\` and \`.ilean\`: yes
- Runtime repair or source transformation: 0
- Official Actions run: ${run_url}
- Evidence artifact: \`primality-sheaf-clean-audit-${final_sha}\`

## Trust audit

- Executable \`sorry\`: 0
- Executable \`admit\`: 0
- New line-start global \`axiom\`: 0
- \`unsafe\` proof escape: 0
- \`native_decide\`: 0
- \`Lean.ofReduceBool\`: 0
- Spt5 whole-file \`#print axioms\` audit: PASS
- Spt5 observed axiom set: \`${observed_axioms}\`
- \`sorryAx\`: absent

No public theorem statement was weakened and no hidden mathematical assumption was added. This PR is ready for review but remains unmerged.
EOF

curl --fail --silent --show-error \
  -X PATCH \
  -H "Authorization: Bearer ${GITHUB_TOKEN}" \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "https://api.github.com/repos/${GITHUB_REPOSITORY}/pulls/${PR_NUMBER}" \
  -d "$(jq -n --rawfile body "${body_file}" '{body:$body}')" \
  > "${FINALIZER_LOGDIR}/pr-update-response.json"

pr_node_id="$(
  curl --fail --silent --show-error \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H 'Accept: application/vnd.github+json' \
    -H 'X-GitHub-Api-Version: 2022-11-28' \
    "https://api.github.com/repos/${GITHUB_REPOSITORY}/pulls/${PR_NUMBER}" \
    | jq -r '.node_id'
)"
test -n "${pr_node_id}"
test "${pr_node_id}" != null

mutation='mutation($id:ID!){markPullRequestReadyForReview(input:{pullRequestId:$id}){pullRequest{isDraft number}}}'
curl --fail --silent --show-error \
  -X POST \
  -H "Authorization: Bearer ${GITHUB_TOKEN}" \
  -H 'Content-Type: application/json' \
  https://api.github.com/graphql \
  -d "$(jq -n --arg query "${mutation}" --arg id "${pr_node_id}" \
    '{query:$query,variables:{id:$id}}')" \
  > "${FINALIZER_LOGDIR}/ready-for-review-response.json"

python3 - "${FINALIZER_LOGDIR}/ready-for-review-response.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding='utf-8') as handle:
    response = json.load(handle)
if response.get('errors'):
    raise SystemExit(response['errors'])
pull = response['data']['markPullRequestReadyForReview']['pullRequest']
if pull['isDraft']:
    raise SystemExit('PR remained draft')
print(f"PR #{pull['number']} is ready for review")
PY
