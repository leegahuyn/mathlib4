#!/usr/bin/env bash
set -euo pipefail

: "${EXPECTED_SHA_31725:?}"
: "${EXPECTED_SHA_31726:?}"
: "${PASS423_RUN_ID:?}"
: "${PASS376_ARTIFACT_ID:?}"
: "${SOURCE_PATH:?}"
: "${ACTIVE_BRANCH:?}"
: "${GH_TOKEN:?}"

mkdir -p /tmp/fa425-artifacts /tmp/fa425-refs
sha256sum "$SOURCE_PATH" | awk '{print $1}' > /tmp/fa425-original-source.sha
: > /tmp/fa425-donor-refs.txt
: > /tmp/fa425-remote-branches.txt
: > /tmp/fa425-ref-map.tsv

git ls-remote --heads origin \
  | awk '{print $2}' \
  | sed 's#refs/heads/##' \
  | grep -E '(fa37[6-9]|fa4[0-9][0-9]|pass376|champion|functional|mock2)' \
  | sort -u | tail -n 80 > /tmp/fa425-remote-branches.txt || true

i=0
while IFS= read -r branch; do
  test -n "$branch" || continue
  i=$((i+1))
  local_ref="refs/remotes/fa425/donor-${i}"
  if git fetch --no-tags --depth=1 origin "+refs/heads/${branch}:${local_ref}" >/dev/null 2>&1; then
    echo "$local_ref" >> /tmp/fa425-donor-refs.txt
    if git show "${local_ref}:${SOURCE_PATH}" > "/tmp/fa425-refs/${i}.lean" 2>/dev/null; then
      printf '%s\t%s\n' "$local_ref" "$branch" >> /tmp/fa425-ref-map.tsv
    fi
  fi
done < /tmp/fa425-remote-branches.txt

find_by_sha() {
  local expected=$1 output=$2 origin_file=$3
  if test "$(sha256sum "$SOURCE_PATH" | awk '{print $1}')" = "$expected"; then
    cp "$SOURCE_PATH" "$output"
    echo "checked-in:${ACTIVE_BRANCH}" > "$origin_file"
    return 0
  fi
  while IFS=$'\t' read -r ref branch; do
    test -n "${ref:-}" || continue
    tmp=$(mktemp)
    if git show "${ref}:${SOURCE_PATH}" > "$tmp" 2>/dev/null && \
       test "$(sha256sum "$tmp" | awk '{print $1}')" = "$expected"; then
      cp "$tmp" "$output"
      echo "branch:${branch}" > "$origin_file"
      rm -f "$tmp"
      return 0
    fi
    rm -f "$tmp"
  done < /tmp/fa425-ref-map.tsv
  return 1
}

if ! find_by_sha "$EXPECTED_SHA_31726" /tmp/fa425-baseline.lean /tmp/fa425-champion-origin.txt; then
  gh api -H 'Accept: application/vnd.github+json' \
    "/repos/${GITHUB_REPOSITORY}/actions/runs/${PASS423_RUN_ID}/artifacts?per_page=100" \
    > /tmp/fa425-pass423-artifacts.json
  python3 - <<'PY'
import json
from pathlib import Path
obj=json.loads(Path('/tmp/fa425-pass423-artifacts.json').read_text())
ids=[str(a['id']) for a in obj.get('artifacts',[]) if not a.get('expired')]
Path('/tmp/fa425-pass423-artifact-ids.txt').write_text('\n'.join(ids)+'\n')
PY
  while IFS= read -r artifact_id; do
    test -n "$artifact_id" || continue
    zip="/tmp/fa425-artifacts/pass423-${artifact_id}.zip"
    dir="/tmp/fa425-artifacts/pass423-${artifact_id}"
    mkdir -p "$dir"
    gh api -H 'Accept: application/vnd.github+json' \
      "/repos/${GITHUB_REPOSITORY}/actions/artifacts/${artifact_id}/zip" > "$zip" || continue
    unzip -q "$zip" -d "$dir" || continue
  done < /tmp/fa425-pass423-artifact-ids.txt
  match=$(find /tmp/fa425-artifacts -type f -print0 | while IFS= read -r -d '' file; do
    test "$(sha256sum "$file" | awk '{print $1}')" = "$EXPECTED_SHA_31726" && printf '%s\n' "$file"
  done | head -n 1)
  if test -n "$match"; then
    cp "$match" /tmp/fa425-baseline.lean
    echo "PASS423-run:${PASS423_RUN_ID}:artifact-file:${match}" > /tmp/fa425-champion-origin.txt
  elif ! find_by_sha "$EXPECTED_SHA_31725" /tmp/fa425-baseline.lean /tmp/fa425-champion-origin.txt; then
    zip=/tmp/fa425-artifacts/pass376.zip
    dir=/tmp/fa425-artifacts/pass376
    mkdir -p "$dir"
    gh api -H 'Accept: application/vnd.github+json' \
      "/repos/${GITHUB_REPOSITORY}/actions/artifacts/${PASS376_ARTIFACT_ID}/zip" > "$zip"
    unzip -q "$zip" -d "$dir"
    match=$(find "$dir" -type f -print0 | while IFS= read -r -d '' file; do
      test "$(sha256sum "$file" | awk '{print $1}')" = "$EXPECTED_SHA_31725" && printf '%s\n' "$file"
    done | head -n 1)
    test -n "$match"
    cp "$match" /tmp/fa425-baseline.lean
    echo "PASS376-artifact:${PASS376_ARTIFACT_ID}:file:${match}" > /tmp/fa425-champion-origin.txt
  fi
fi

resolved=$(sha256sum /tmp/fa425-baseline.lean | awk '{print $1}')
test "$resolved" = "$EXPECTED_SHA_31726" || test "$resolved" = "$EXPECTED_SHA_31725"
test "$(python3 -c "print(len(open('/tmp/fa425-baseline.lean',encoding='utf-8').read().splitlines()))")" = 60453
cp /tmp/fa425-baseline.lean "$SOURCE_PATH"
printf 'resolved_sha256=%s\norigin=%s\nline_count=60453\n' \
  "$resolved" "$(cat /tmp/fa425-champion-origin.txt)" | tee /tmp/fa425-resolution.txt
