#!/usr/bin/env bash
set -uo pipefail

BRANCH='ci/fa319-isolated-20260807'
EVIDENCE='/tmp/pr9-adaptive-post320'
STATUS='build-logs/pr9-adaptive-post320-status.txt'
COMMENT='/tmp/pr9-adaptive-post320-comment.md'
mkdir -p "${EVIDENCE}" build-logs

set +e
bash scripts/pr9_adaptive_post320_fa_qym.sh
code=$?
set -e
conclusion='failure'; [[ "${code}" -eq 0 ]] && conclusion='success'

{
  echo "utc=$(date -u +%FT%TZ)"
  echo "conclusion=${conclusion}"
  echo "exit_code=${code}"
  echo "authority_run=31159696948"
  echo "authority_job=92827136991"
  echo
  echo '--- status ---'
  cat "${EVIDENCE}/status.txt" 2>/dev/null || true
  echo
  echo '--- repair chain ---'
  cat "${EVIDENCE}/repair-chain.txt" 2>/dev/null || true
  echo
  echo '--- compile summary ---'
  cat "${EVIDENCE}/compile-summary.csv" 2>/dev/null || true
  echo
  echo '--- first errors ---'
  find "${EVIDENCE}/logs" -type f -name '*.errors.txt' -print0 2>/dev/null | sort -z \
    | while IFS= read -r -d '' f; do
        echo "===== ${f} ====="
        sed -n '1,180p' "${f}"
      done
} > /tmp/pr9-adaptive-post320-status.txt

git fetch --no-tags origin "+refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}" || true
git reset --hard "origin/${BRANCH}"
cp /tmp/pr9-adaptive-post320-status.txt "${STATUS}"
if [[ "${conclusion}" == 'success' ]]; then
  touch build-logs/PR9_ADAPTIVE_POST320_FA_QYM_PASS
  rm -f build-logs/PR9_ADAPTIVE_POST320_FA_QYM_FAIL
else
  touch build-logs/PR9_ADAPTIVE_POST320_FA_QYM_FAIL
  rm -f build-logs/PR9_ADAPTIVE_POST320_FA_QYM_PASS
fi
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add -A build-logs
if ! git diff --cached --quiet; then
  git commit -m "ci: record adaptive post-PASS320 ${conclusion}"
  git push origin "HEAD:${BRANCH}" || true
fi

{
  echo '<!-- pr9-adaptive-post320 -->'
  echo '## PR #9 adaptive post-PASS 320 result'
  echo
  echo "- Authority: \`31159696948 / 92827136991\`"
  echo "- Result: **${conclusion}**"
  echo "- Exit code: \`${code}\`"
  echo
  if [[ -s "${EVIDENCE}/repair-chain.txt" ]]; then
    echo '### Applied SHA-chained repair path'
    echo '```text'
    cat "${EVIDENCE}/repair-chain.txt"
    echo '```'
  fi
  echo '### Compile summary'
  echo '```csv'
  cat "${EVIDENCE}/compile-summary.csv" 2>/dev/null || true
  echo '```'
  if [[ "${conclusion}" != 'success' ]]; then
    first="$(find "${EVIDENCE}/logs" -type f -name '*.errors.txt' -print 2>/dev/null | sort | head -1)"
    echo '### First remaining compiler errors'
    echo '```text'
    [[ -n "${first}" ]] && sed -n '1,100p' "${first}" || true
    echo '```'
  fi
} > "${COMMENT}"

export GH_TOKEN="${GITHUB_TOKEN:?GITHUB_TOKEN is required}"
existing="$(gh api "/repos/${GITHUB_REPOSITORY}/issues/9/comments?per_page=100" \
  --jq '.[] | select(.body | contains("<!-- pr9-adaptive-post320 -->")) | .id' | tail -1)"
if [[ -n "${existing}" ]]; then
  gh api --method PATCH "/repos/${GITHUB_REPOSITORY}/issues/comments/${existing}" \
    -F body=@"${COMMENT}" >/dev/null || true
else
  gh api --method POST "/repos/${GITHUB_REPOSITORY}/issues/9/comments" \
    -F body=@"${COMMENT}" >/dev/null || true
fi

exit "${code}"
