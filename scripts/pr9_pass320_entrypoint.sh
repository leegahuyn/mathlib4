#!/usr/bin/env bash
set -uo pipefail

BRANCH='ci/fa319-isolated-20260807'
EVIDENCE='/tmp/pr9-pass320-replay'
STATUS='build-logs/pr9-pass320-latest-status.txt'
mkdir -p "${EVIDENCE}" build-logs

set +e
bash scripts/pr9_replay_pass320_fa_qym.sh
code=$?
set -e

{
  echo "utc=$(date -u +%FT%TZ)"
  echo "branch=${BRANCH}"
  echo "workflow_head=$(git rev-parse HEAD)"
  echo "replay_exit=${code}"
  echo "pass320_run=31159696948"
  echo "pass320_job=92827136991"
  echo
  echo '--- PR #9 state ---'
  gh api "/repos/${GITHUB_REPOSITORY}/pulls/9" \
    --jq '"state=\(.state) merged=\(.merged) draft=\(.draft) head=\(.head.sha) base=\(.base.sha) mergeable=\(.mergeable)"' \
    || true
  echo
  echo '--- compile summary ---'
  cat "${EVIDENCE}/compile-summary.csv" 2>/dev/null || true
  echo
  echo '--- selected sources ---'
  cat "${EVIDENCE}/selection.txt" 2>/dev/null || true
  echo
  echo '--- PASS 320 artifacts ---'
  cat "${EVIDENCE}/artifact-ids.tsv" 2>/dev/null || true
  echo
  echo '--- final error excerpts ---'
  find "${EVIDENCE}/logs" -maxdepth 1 -type f -name '*.log' -print0 2>/dev/null \
    | sort -z \
    | while IFS= read -r -d '' log; do
        errors="$(grep -c 'error:' "${log}" 2>/dev/null || true)"
        if [[ "${errors}" -gt 0 ]]; then
          echo "===== ${log} errors=${errors} ====="
          grep -n 'error:' "${log}" | head -40 || true
          echo '--- tail ---'
          tail -120 "${log}" || true
        fi
      done
} > "${STATUS}"

# Persist the status without changing Lean sources. If the verified source was
# pushed by the replay, refresh to that remote head first.
git fetch --no-tags origin "+refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}" || true
git switch -C "${BRANCH}" "origin/${BRANCH}" || exit "${code}"
mkdir -p "$(dirname "${STATUS}")"
cp /tmp/pr9-pass320-status-copy.txt "${STATUS}" 2>/dev/null || true

# The switch above replaces the worktree, so reconstruct the status from evidence.
{
  echo "utc=$(date -u +%FT%TZ)"
  echo "branch=${BRANCH}"
  echo "recorded_head=$(git rev-parse HEAD)"
  echo "replay_exit=${code}"
  echo "pass320_run=31159696948"
  echo "pass320_job=92827136991"
  echo
  echo '--- compile summary ---'
  cat "${EVIDENCE}/compile-summary.csv" 2>/dev/null || true
  echo
  echo '--- selected sources ---'
  cat "${EVIDENCE}/selection.txt" 2>/dev/null || true
  echo
  echo '--- PASS 320 artifacts ---'
  cat "${EVIDENCE}/artifact-ids.tsv" 2>/dev/null || true
  echo
  echo '--- error index ---'
  find "${EVIDENCE}/logs" -maxdepth 1 -type f -name '*.log' -print0 2>/dev/null \
    | sort -z \
    | while IFS= read -r -d '' log; do
        errors="$(grep -c 'error:' "${log}" 2>/dev/null || true)"
        if [[ "${errors}" -gt 0 ]]; then
          echo "===== $(basename "${log}") errors=${errors} ====="
          grep -n 'error:' "${log}" | head -80 || true
        fi
      done
} > "${STATUS}"

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${STATUS}"
if ! git diff --cached --quiet; then
  git commit -m 'ci: record latest PR9 PASS 320 replay status'
  git push origin "HEAD:${BRANCH}" || true
fi

exit "${code}"
