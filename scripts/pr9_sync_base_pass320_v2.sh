#!/usr/bin/env bash
set -euo pipefail

HEAD_BRANCH='ci/fa319-isolated-20260807'
BASE_BRANCH='fix/primality-sheaf-clean-build'
STATUS='build-logs/pr9-branch-sync-status.txt'
PRESERVE='/tmp/pr9-pass320-preserve'
mkdir -p "${PRESERVE}" build-logs

test "$(git branch --show-current)" = "${HEAD_BRANCH}"
git fetch --no-tags origin \
  "+refs/heads/${BASE_BRANCH}:refs/remotes/origin/${BASE_BRANCH}"

before_head="$(git rev-parse HEAD)"
base_head="$(git rev-parse "origin/${BASE_BRANCH}")"
counts="$(git rev-list --left-right --count "origin/${BASE_BRANCH}...HEAD")"

preserve_paths=(
  '.github/workflows/pr9-pass320-replay.yml'
  '.github/workflows/pr9-pass320-replay-v2.yml'
  '.github/workflows/pr9-sync-base-pass320.yml'
  '.github/workflows/pr9-sync-base-pass320-v2.yml'
  'scripts/pr9_replay_pass320_fa_qym.sh'
  'scripts/pr9_pass320_entrypoint.sh'
  'scripts/pr9_sync_base_pass320_v2.sh'
)
for path in "${preserve_paths[@]}"; do
  if [[ -f "${path}" ]]; then
    mkdir -p "${PRESERVE}/$(dirname "${path}")"
    cp "${path}" "${PRESERVE}/${path}"
  fi
done

sync_result='already-current'
conflict_count=0
if ! git merge-base --is-ancestor "origin/${BASE_BRANCH}" HEAD; then
  sync_result='merged-base'
  set +e
  git merge --no-ff --no-commit "origin/${BASE_BRANCH}"
  merge_code=$?
  set -e

  if [[ "${merge_code}" -ne 0 ]]; then
    mapfile -t conflicts < <(git diff --name-only --diff-filter=U)
    conflict_count="${#conflicts[@]}"
    test "${conflict_count}" -gt 0

    # PR #9 is a disposable verification branch.  Resolve all inherited source
    # conflicts in favour of the latest repair base, then restore only the
    # PASS-320 verification infrastructure listed above.
    for path in "${conflicts[@]}"; do
      git checkout --theirs -- "${path}"
      git add -- "${path}"
    done
  fi

  for path in "${preserve_paths[@]}"; do
    if [[ -f "${PRESERVE}/${path}" ]]; then
      mkdir -p "$(dirname "${path}")"
      cp "${PRESERVE}/${path}" "${path}"
      git add -- "${path}"
    fi
  done
fi

after_worktree="$(git rev-parse HEAD)"
{
  echo "utc=$(date -u +%FT%TZ)"
  echo "head_branch=${HEAD_BRANCH}"
  echo "base_branch=${BASE_BRANCH}"
  echo "before_head=${before_head}"
  echo "base_head=${base_head}"
  echo "before_left_right=${counts}"
  echo "sync_result=${sync_result}"
  echo "conflict_count=${conflict_count}"
  echo "worktree_head=${after_worktree}"
  echo "unmerged_count=$(git diff --name-only --diff-filter=U | wc -l | tr -d ' ')"
} > "${STATUS}"
git add "${STATUS}"

test -z "$(git diff --name-only --diff-filter=U)"
git diff --cached --check

if git diff --cached --quiet; then
  echo 'No branch-sync commit was necessary.'
  exit 0
fi

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git commit -m 'merge: synchronize PR9 with latest PASS 320 base'
git push origin "HEAD:${HEAD_BRANCH}"
