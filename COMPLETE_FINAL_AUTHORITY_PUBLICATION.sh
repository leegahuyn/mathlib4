#!/usr/bin/env bash
set -euo pipefail

REPOSITORY="leegahuyn/mathlib4"
AUTHORITY_COMMIT="61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3"
TAG="formalization-final-2026-08-21"
TITLE="Formalization FINAL AUTHORITY — 2026-08-21"
PR_NUMBER="56"
RUN_ID="32438949135"
EVIDENCE_SHA256="86b2525c7533562b929a573eca0ff006c6b1df1ac054329c906eae009e05954a"
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="${1:-$PWD}"
PACKAGE_DIR="${2:-$SCRIPT_DIR}"

fail() { printf 'FINAL AUTHORITY PUBLICATION: FAIL: %s\n' "$*" >&2; exit 1; }
for cmd in git gh python3 sha256sum; do command -v "$cmd" >/dev/null 2>&1 || fail "$cmd is required"; done
[ -n "${GH_TOKEN:-}" ] || fail "set GH_TOKEN to a token with Contents:write and Workflows:write (or classic repo+workflow)"
gh auth status >/dev/null 2>&1 || fail "gh authentication failed"
[ -d "$REPO_DIR/.git" ] || fail "not a Git working tree: $REPO_DIR"
[ -f "$PACKAGE_DIR/SHA256SUMS.txt" ] || fail "missing package SHA256SUMS.txt"

(cd "$PACKAGE_DIR" && sha256sum -c SHA256SUMS.txt)
git -C "$REPO_DIR" remote get-url origin | grep -Eq 'github\.com[:/]leegahuyn/mathlib4(?:\.git)?$' || fail "wrong origin repository"
git -C "$REPO_DIR" fetch origin "$AUTHORITY_COMMIT" --no-tags
test "$(git -C "$REPO_DIR" rev-parse "$AUTHORITY_COMMIT^{commit}")" = "$AUTHORITY_COMMIT" || fail "authority commit missing"

# The branch and tag share a name in this repository. Always use refs/tags/... explicitly.
remote_tag="$(git -C "$REPO_DIR" ls-remote --tags origin "refs/tags/$TAG" "refs/tags/$TAG^{}")"
if grep -q "refs/tags/$TAG" <<<"$remote_tag"; then
  git -C "$REPO_DIR" fetch --force origin "refs/tags/$TAG:refs/tags/$TAG"
  test "$(git -C "$REPO_DIR" cat-file -t "refs/tags/$TAG")" = "tag" || fail "existing canonical ref is not an annotated tag"
  test "$(git -C "$REPO_DIR" rev-parse "refs/tags/$TAG^{}")" = "$AUTHORITY_COMMIT" || fail "TAG_ALREADY_EXISTS_WRONG_TARGET"
else
  tag_message="$(mktemp)"
  trap 'rm -f "$tag_message"' EXIT
  cat > "$tag_message" <<EOF
Formalization FINAL AUTHORITY
Exact tested commit: $AUTHORITY_COMMIT
Actual Lean authority run: $RUN_ID
Job: 96645636205
Final13 13/13; bridges 2/2; BuildAll PASS; clean×2 PASS;
checklist 15/15; forbidden 0; panic 0; axiom/source identity PASS.
Evidence ZIP SHA256:
$EVIDENCE_SHA256
EOF
  git -C "$REPO_DIR" tag -a "$TAG" "$AUTHORITY_COMMIT" -F "$tag_message"
  git -C "$REPO_DIR" push origin "refs/tags/$TAG"
fi

git -C "$REPO_DIR" fetch --force origin "refs/tags/$TAG:refs/tags/$TAG"
test "$(git -C "$REPO_DIR" cat-file -t "refs/tags/$TAG")" = "tag" || fail "canonical tag is not annotated"
test "$(git -C "$REPO_DIR" rev-parse "refs/tags/$TAG^{}")" = "$AUTHORITY_COMMIT" || fail "canonical tag target mismatch"
remote_tag="$(git -C "$REPO_DIR" ls-remote --tags origin "refs/tags/$TAG" "refs/tags/$TAG^{}")"
grep -Eq "^$AUTHORITY_COMMIT[[:space:]]+refs/tags/$TAG\^\{\}$" <<<"$remote_tag" || fail "remote peeled tag target mismatch"

if gh release view "$TAG" --repo "$REPOSITORY" --json tagName,name,url >/tmp/final-authority-release.json 2>/dev/null; then
  test "$(python3 -c 'import json;print(json.load(open("/tmp/final-authority-release.json"))["tagName"])')" = "$TAG" || fail "existing release tag mismatch"
else
  gh release create "$TAG" --repo "$REPOSITORY" --verify-tag --title "$TITLE" --notes-file "$PACKAGE_DIR/RELEASE_NOTES.md"
fi

assets=(
  final-authority-last-mile-32438949135-attempt1.zip
  FINAL_AUTHORITY_RECORD.json
  FINAL_AUTHORITY_RECORD.md
  SHA256SUMS.txt
  VERIFY_FINAL_AUTHORITY.sh
  VERIFY_FINAL_AUTHORITY.ps1
  formalization-final-source-61a48f07.tar.gz
  RELEASE_NOTES.md
  FINAL_TRUE_PASS_REPORT.md
  FINAL_STATUS_CARD.md
  FINAL_SOURCE_IDENTITY.json
  FINAL_15_CHECKLIST_RESULT.json
  CLEAN_BUILD_1_RESULT.json
  CLEAN_BUILD_2_RESULT.json
  BUILDALL_RESULT.json
  FINAL_13_BUILD_RESULTS.json
  FORBIDDEN_AUDIT.json
  AXIOM_AUDIT.json
  QYM_CANONICAL_REPLAY_RESULT.json
  MOCK3_CANONICAL_RESULT.json
)
existing="$(gh release view "$TAG" --repo "$REPOSITORY" --json assets --jq '.assets[].name')"
for name in "${assets[@]}"; do
  path="$PACKAGE_DIR/$name"
  [ -f "$path" ] || fail "missing release asset: $name"
  if grep -Fxq "$name" <<<"$existing"; then
    tmp="$(mktemp -d)"
    gh release download "$TAG" --repo "$REPOSITORY" --pattern "$name" --dir "$tmp"
    test "$(sha256sum "$tmp/$name" | awk '{print $1}')" = "$(sha256sum "$path" | awk '{print $1}')" || fail "existing release asset hash mismatch: $name"
    rm -rf "$tmp"
  else
    gh release upload "$TAG" "$path" --repo "$REPOSITORY"
  fi
done

release_json="$(gh release view "$TAG" --repo "$REPOSITORY" --json tagName,name,url,assets)"
release_url="$(python3 -c 'import json,sys;print(json.load(sys.stdin)["url"])' <<<"$release_json")"
marker='<!-- formalization-final-2026-08-21-archive -->'
comment_body="$(cat <<EOF
$marker
FINAL AUTHORITY archived.

Canonical tag:
$TAG

Exact authority commit:
$AUTHORITY_COMMIT

Authority run:
$RUN_ID

Evidence SHA256:
$EVIDENCE_SHA256

Release:
$release_url

No merge commit supersedes this authority.
Future development requires a successor version.
EOF
)"
comment_id="$(gh api --paginate "repos/$REPOSITORY/issues/$PR_NUMBER/comments?per_page=100" --jq ".[] | select(.body | contains(\"$marker\")) | .id" | head -n1)"
if [ -z "$comment_id" ]; then
  gh api --method POST "repos/$REPOSITORY/issues/$PR_NUMBER/comments" -f body="$comment_body" >/dev/null
else
  existing_body="$(gh api "repos/$REPOSITORY/issues/comments/$comment_id" --jq .body)"
  test "$existing_body" = "$comment_body" || fail "existing archive PR comment differs"
fi

printf '%s\n' "FINAL AUTHORITY PUBLICATION: PASS"
printf '%s\n' "Tag target: $(git -C "$REPO_DIR" rev-parse "refs/tags/$TAG^{}")"
printf '%s\n' "Release: $release_url"
