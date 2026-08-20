#!/usr/bin/env bash
set -uo pipefail

BRANCH='ci/fa319-isolated-20260807'
STATUS='build-logs/pr9-resilient-pass320-status.txt'
EVIDENCE='/tmp/pr9-exact-pass320'
RECOVERY='/tmp/pr9-pass320-remote-recovery'
COMMENT='/tmp/pr9-resilient-pass320-comment.md'
mkdir -p build-logs "${EVIDENCE}" "${RECOVERY}"

set +e
bash scripts/pr9_apply_exact_pass320_resilient.sh
code=$?
set -e
conclusion='failure'
[[ "${code}" -eq 0 ]] && conclusion='success'

build_report() {
  echo "utc=$(date -u +%FT%TZ)"
  echo "conclusion=${conclusion}"
  echo "exit_code=${code}"
  echo "authority_run=31159696948"
  echo "authority_job=92827136991"
  echo "branch=${BRANCH}"
  echo
  echo '--- compile summaries ---'
  for f in "${EVIDENCE}/compile-summary.csv" "${RECOVERY}/compile-summary.csv"; do
    if [[ -s "${f}" ]]; then
      echo "===== ${f} ====="
      cat "${f}"
    fi
  done
  echo
  echo '--- repair hashes ---'
  cat "${EVIDENCE}/repair-hashes.txt" 2>/dev/null || true
  echo
  echo '--- recovery ---'
  cat "${RECOVERY}/recovery-status.txt" 2>/dev/null || true
  echo
  echo '--- first errors ---'
  find "${EVIDENCE}/logs" "${RECOVERY}/logs" -type f -name '*.errors.txt' -print0 2>/dev/null \
    | sort -z \
    | while IFS= read -r -d '' f; do
        echo "===== ${f} ====="
        sed -n '1,160p' "${f}"
      done
}

build_report > /tmp/pr9-resilient-pass320-status.txt

# Refresh to the latest branch head so the status record never overwrites a
# verified source commit made by the repair script.
git fetch --no-tags origin \
  "+refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}" || true
git reset --hard "origin/${BRANCH}"
mkdir -p "$(dirname "${STATUS}")"
cp /tmp/pr9-resilient-pass320-status.txt "${STATUS}"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${STATUS}"
if ! git diff --cached --quiet; then
  git commit -m "ci: record PR9 resilient PASS 320 ${conclusion}"
  git push origin "HEAD:${BRANCH}" || true
fi

{
  echo '<!-- pr9-resilient-pass320 -->'
  echo '## PR #9 resilient PASS 320 result'
  echo
  echo "- Authority: \`31159696948 / 92827136991\`"
  echo "- Result: **${conclusion}**"
  echo "- Exit code: \`${code}\`"
  echo "- Recorded branch head: \`$(git rev-parse HEAD)\`"
  echo
  echo '### Compile summary'
  echo '```csv'
  if [[ -s "${EVIDENCE}/compile-summary.csv" ]]; then
    cat "${EVIDENCE}/compile-summary.csv"
  fi
  if [[ -s "${RECOVERY}/compile-summary.csv" ]]; then
    cat "${RECOVERY}/compile-summary.csv"
  fi
  echo '```'
  if [[ -s "${EVIDENCE}/repair-hashes.txt" ]]; then
    echo '### Exact PASS 320 hashes'
    echo '```text'
    cat "${EVIDENCE}/repair-hashes.txt"
    echo '```'
  fi
  if [[ "${code}" -ne 0 ]]; then
    echo '### First remaining errors'
    echo '```text'
    first="$(find "${EVIDENCE}/logs" "${RECOVERY}/logs" -type f -name '*.errors.txt' -print 2>/dev/null | sort | head -1)"
    if [[ -n "${first}" && -s "${first}" ]]; then
      sed -n '1,100p' "${first}"
    else
      echo 'No compiler error index was generated; inspect the failed workflow step and uploaded artifact.'
    fi
    echo '```'
  fi
} > "${COMMENT}"

export GH_TOKEN="${GITHUB_TOKEN:?GITHUB_TOKEN is required}"
existing="$(gh api "/repos/${GITHUB_REPOSITORY}/issues/9/comments?per_page=100" \
  --jq '.[] | select(.body | contains("<!-- pr9-resilient-pass320 -->")) | .id' \
  | tail -1)"
if [[ -n "${existing}" ]]; then
  gh api --method PATCH "/repos/${GITHUB_REPOSITORY}/issues/comments/${existing}" \
    -F body=@"${COMMENT}" >/dev/null || true
else
  gh api --method POST "/repos/${GITHUB_REPOSITORY}/issues/9/comments" \
    -F body=@"${COMMENT}" >/dev/null || true
fi

exit "${code}"
