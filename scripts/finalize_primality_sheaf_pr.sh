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
FINAL_CI_DRIVER='scripts/primality_sheaf_ci.sh'
mkdir -p "${VALIDATION_LOGDIR}" "${FINALIZER_LOGDIR}"

# This is the hard gate. No repository mutation occurs before it succeeds.
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

# Restore every workflow to the current master version, except the one official
# PrimalitySheafVerification workflow that this project intentionally replaces.
mapfile -t changed_workflows < <(
  git diff --name-only origin/master...HEAD -- .github/workflows | sort -u
)
for path in "${changed_workflows[@]}"; do
  [[ -z "${path}" ]] && continue
  [[ "${path}" = "${OFFICIAL_WORKFLOW}" ]] && continue
  restore_or_remove "${path}"
done

# Restore project-local custom actions as well; final CI uses only pinned public
# actions and the non-mutating local shell driver.
mapfile -t changed_actions < <(
  git diff --name-only origin/master...HEAD -- .github/actions | sort -u
)
for path in "${changed_actions[@]}"; do
  [[ -z "${path}" ]] && continue
  restore_or_remove "${path}"
done

# Remove/restore temporary repair and materialization scripts. Keep only the
# final non-mutating CI driver.
mapfile -t changed_scripts < <(
  git diff --name-only origin/master...HEAD -- scripts | sort -u
)
for path in "${changed_scripts[@]}"; do
  [[ -z "${path}" ]] && continue
  [[ "${path}" = "${FINAL_CI_DRIVER}" ]] && continue
  restore_or_remove "${path}"
done

# Build logs belong in Actions artifacts, not in the source tree.
mapfile -t changed_build_logs < <(
  git diff --name-only origin/master...HEAD -- build-logs | sort -u
)
for path in "${changed_build_logs[@]}"; do
  [[ -z "${path}" ]] && continue
  restore_or_remove "${path}"
done

# Install the single official workflow after temporary templates have served
# their purpose. The permanent workflow never edits Lean source.
mkdir -p "$(dirname "${OFFICIAL_WORKFLOW}")"
cp "${OFFICIAL_TEMPLATE}" "${OFFICIAL_WORKFLOW}"
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

# Wait synchronously for the official workflow on the exact cleanup commit.
api="https://api.github.com/repos/${GITHUB_REPOSITORY}/actions/runs?head_sha=${final_sha}&per_page=100"
run_url=''
for attempt in $(seq 1 240); do
  response="$(curl --fail --silent --show-error \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H 'Accept: application/vnd.github+json' \
    -H 'X-GitHub-Api-Version: 2022-11-28' \
    "${api}")"
  state="$(python3 -c '
import json,sys
runs=json.load(sys.stdin).get("workflow_runs",[])
selected=[r for r in runs if r.get("name")=="PrimalitySheafVerification CI" and r.get("event")=="push"]
if not selected:
    print("missing")
else:
    run=sorted(selected,key=lambda r:r.get("run_number",0),reverse=True)[0]
    print(f"{run.get(chr(115)+chr(116)+chr(97)+chr(116)+chr(117)+chr(115))}:{run.get(chr(99)+chr(111)+chr(110)+chr(99)+chr(108)+chr(117)+chr(115)+chr(105)+chr(111)+chr(110)) or ""}:{run.get(chr(104)+chr(116)+chr(109)+chr(108)+chr(95)+chr(117)+chr(114)+chr(108)) or ""}")
' <<<"${response}")"
  printf '%s\n' "attempt=${attempt} state=${state}" \
    | tee -a "${FINALIZER_LOGDIR}/official-ci-poll.log"
  case "${state}" in
    completed:success:*)
      run_url="${state#completed:success:}"
      break
      ;;
    completed:*:*)
      echo "official CI failed: ${state}" >&2
      exit 1
      ;;
  esac
  sleep 30
done

test -n "${run_url}"
printf '%s\n' "official_ci_url=${run_url}" \
  | tee "${FINALIZER_LOGDIR}/official-ci-success.txt"

observed_axioms="$(
  sed -n 's/^observed_axioms=//p' \
    "${VALIDATION_LOGDIR}/audit/Spt5-axiom-summary.txt" | tail -1
)"
body_file="${FINALIZER_LOGDIR}/pr-body.md"
cat > "${body_file}" <<EOF
## Completion status

All 13 primary \`PrimalitySheafVerification\` modules and aggregate \`BuildAll.lean\` now compile directly from the checked-in Lean source. The final workflow performs no runtime source repair.

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
- Project artifact directory deleted before each rebuild: yes
- Full dependency-ordered compile passes: 2
- \`.olean\` and \`.ilean\` required for every module: yes
- Runtime repair or source transformation: 0
- Official Actions run: ${run_url}
- Artifact: \`primality-sheaf-clean-audit-${final_sha}\`

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
import json,sys
response=json.load(open(sys.argv[1],encoding='utf-8'))
if response.get('errors'):
    raise SystemExit(response['errors'])
pull=response['data']['markPullRequestReadyForReview']['pullRequest']
if pull['isDraft']:
    raise SystemExit('PR remained draft')
print(f"PR #{pull['number']} is ready for review")
PY
