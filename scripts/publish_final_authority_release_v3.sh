#!/usr/bin/env bash
set -euo pipefail

AUTH=8f7e861f5f76c0aa5d347e0de865516a1ba23922
FINAL_BRANCH=gpt/final-authority-pass-20260821
ARCHIVE_BRANCH=archive/formalization-final-2026-08-21
TAG=formalization-final-authority-2026-08-21
RELEASE_TITLE='Formalization FINAL AUTHORITY — 2026-08-21'
PACKAGE_ARTIFACT_ID=9437702903
PACKAGE_ARTIFACT_SHA256=15c7dbada60b86e28709457a1fef3b123813a68a1bad7c6756b08e0608c4aea8
REPO=${GITHUB_REPOSITORY:-leegahuyn/mathlib4}
: "${GH_TOKEN:?GH_TOKEN is required}"

api="https://api.github.com/repos/$REPO"
auth=(-H "Authorization: Bearer $GH_TOKEN" -H 'Accept: application/vnd.github+json' -H 'X-GitHub-Api-Version: 2022-11-28')

rm -rf package
mkdir -p package

git cat-file -e "$AUTH^{commit}"
test "$(git ls-remote origin "refs/heads/$FINAL_BRANCH" | awk '{print $1}')" = "$AUTH"
test "$(git ls-remote origin "refs/heads/$ARCHIVE_BRANCH" | awk '{print $1}')" = "$AUTH"
test "$(git rev-parse "$AUTH:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")" = 28f614d48e02a0f28d3f5a758e813350b3ea89cf
test "$(git rev-parse "$AUTH:PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean")" = 464f5dd095876b20165d12690c8127ef9d909e6a
test "$(git rev-parse "$AUTH:PrimalitySheafVerification/QYM.lean")" = 7afb309d7c4da97da7bc6b922931734d72830d41
test "$(git rev-parse "$AUTH:PrimalitySheafVerification/Mock1_Advanced.lean")" = 3b6596bbc0790c7d6e427c44e2b0b18b8af3efa6
test "$(git show "$AUTH:PrimalitySheafVerification/QYM.lean" | sha256sum | awk '{print $1}')" = ab7c394f68b812046bcfae109b274a2d4fa42479bf8e76461c73a9c190fb3204

curl --fail --location --retry 5 --retry-all-errors \
  -H "Authorization: Bearer $GH_TOKEN" -H 'Accept: application/vnd.github+json' \
  "$api/actions/artifacts/$PACKAGE_ARTIFACT_ID/zip" -o /tmp/final-authority-package.zip
echo "$PACKAGE_ARTIFACT_SHA256  /tmp/final-authority-package.zip" | sha256sum --check -
unzip -q /tmp/final-authority-package.zip -d package

test -x package/VERIFY_FINAL_AUTHORITY.sh
package/VERIFY_FINAL_AUTHORITY.sh
for f in \
  package/FINAL_AUTHORITY_RECORD.json \
  package/FINAL_AUTHORITY_RECORD.md \
  package/RELEASE_NOTES.md \
  package/TAG_MESSAGE.txt \
  package/SHA256SUMS.txt \
  package/formalization-final-source-8f7e861f5f76.tar.gz \
  package/evidence/full-authority-9435161106.zip \
  package/evidence/qym-replay-9398192196.zip \
  package/evidence/terminal-authority-9436985567.zip
do
  test -s "$f"
done

code=$(curl -sS -o /tmp/tag-ref.json -w '%{http_code}' "${auth[@]}" "$api/git/ref/tags/$TAG")
if [ "$code" = 404 ]; then
  jq -n \
    --arg tag "$TAG" \
    --arg message "$(cat package/TAG_MESSAGE.txt)" \
    --arg object "$AUTH" \
    --arg date "$(date -u +'%Y-%m-%dT%H:%M:%SZ')" \
    '{tag:$tag,message:$message,object:$object,type:"commit",tagger:{name:"leegahuyn FINAL AUTHORITY archiver",email:"102484661+leegahuyn@users.noreply.github.com",date:$date}}' \
    > /tmp/tag-payload.json
  curl --fail --silent --show-error "${auth[@]}" -X POST "$api/git/tags" \
    --data-binary @/tmp/tag-payload.json > /tmp/tag-object.json
  tag_object_sha=$(jq -r .sha /tmp/tag-object.json)
  test -n "$tag_object_sha" && test "$tag_object_sha" != null
  jq -n --arg ref "refs/tags/$TAG" --arg sha "$tag_object_sha" '{ref:$ref,sha:$sha}' > /tmp/ref-payload.json
  curl --fail --silent --show-error "${auth[@]}" -X POST "$api/git/refs" \
    --data-binary @/tmp/ref-payload.json > /tmp/tag-ref.json
elif [ "$code" != 200 ]; then
  cat /tmp/tag-ref.json
  exit 1
fi

test "$(jq -r .object.type /tmp/tag-ref.json)" = tag
tag_object_sha=$(jq -r .object.sha /tmp/tag-ref.json)
curl --fail --silent --show-error "${auth[@]}" "$api/git/tags/$tag_object_sha" > package/ANNOTATED_TAG_RESULT.json
test "$(jq -r .tag package/ANNOTATED_TAG_RESULT.json)" = "$TAG"
test "$(jq -r .object.type package/ANNOTATED_TAG_RESULT.json)" = commit
test "$(jq -r .object.sha package/ANNOTATED_TAG_RESULT.json)" = "$AUTH"

assets=(
  package/evidence/full-authority-9435161106.zip
  package/evidence/qym-replay-9398192196.zip
  package/evidence/terminal-authority-9436985567.zip
  package/formalization-final-source-8f7e861f5f76.tar.gz
  package/FINAL_AUTHORITY_RECORD.json
  package/FINAL_AUTHORITY_RECORD.md
  package/SHA256SUMS.txt
  package/VERIFY_FINAL_AUTHORITY.sh
  package/VERIFY_FINAL_AUTHORITY.ps1
  package/reports/FINAL_TRUE_PASS_REPORT.md
  package/reports/FINAL_STATUS_CARD.md
  package/reports/FINAL_SOURCE_IDENTITY.json
  package/reports/FINAL_15_CHECKLIST_RESULT.json
  package/reports/FINAL_13_BUILD_RESULTS.json
  package/reports/BUILDALL_RESULT.json
  package/reports/CLEAN_BUILD_1_RESULT.json
  package/reports/CLEAN_BUILD_2_RESULT.json
  package/reports/FORBIDDEN_AUDIT.json
  package/reports/AXIOM_AUDIT.json
  package/ANNOTATED_TAG_RESULT.json
)

if gh release view "$TAG" --repo "$REPO" >/dev/null 2>&1; then
  gh release edit "$TAG" --repo "$REPO" --title "$RELEASE_TITLE" --notes-file package/RELEASE_NOTES.md
  gh release upload "$TAG" --repo "$REPO" --clobber "${assets[@]}"
else
  gh release create "$TAG" --repo "$REPO" --verify-tag --title "$RELEASE_TITLE" \
    --notes-file package/RELEASE_NOTES.md "${assets[@]}"
fi

gh release view "$TAG" --repo "$REPO" \
  --json url,tagName,isDraft,isPrerelease,targetCommitish,assets > package/GITHUB_RELEASE_RESULT.json

curl --fail --silent --show-error "${auth[@]}" "$api/git/ref/tags/$TAG" > /tmp/final-ref.json
test "$(jq -r .object.type /tmp/final-ref.json)" = tag
final_tag_sha=$(jq -r .object.sha /tmp/final-ref.json)
curl --fail --silent --show-error "${auth[@]}" "$api/git/tags/$final_tag_sha" > /tmp/final-tag.json
test "$(jq -r .object.sha /tmp/final-tag.json)" = "$AUTH"
test "$(git ls-remote origin "refs/heads/$FINAL_BRANCH" | awk '{print $1}')" = "$AUTH"
test "$(git ls-remote origin "refs/heads/$ARCHIVE_BRANCH" | awk '{print $1}')" = "$AUTH"

python3 - <<'PY'
import json
p='package/GITHUB_RELEASE_RESULT.json'
d=json.load(open(p))
assert d['tagName']=='formalization-final-authority-2026-08-21'
assert d['isDraft'] is False and d['isPrerelease'] is False
names={a['name'] for a in d['assets']}
required={
 'full-authority-9435161106.zip','qym-replay-9398192196.zip','terminal-authority-9436985567.zip',
 'formalization-final-source-8f7e861f5f76.tar.gz','FINAL_AUTHORITY_RECORD.json','FINAL_AUTHORITY_RECORD.md',
 'SHA256SUMS.txt','VERIFY_FINAL_AUTHORITY.sh','VERIFY_FINAL_AUTHORITY.ps1','FINAL_TRUE_PASS_REPORT.md',
 'FINAL_STATUS_CARD.md','FINAL_SOURCE_IDENTITY.json','FINAL_15_CHECKLIST_RESULT.json',
 'FINAL_13_BUILD_RESULTS.json','BUILDALL_RESULT.json','CLEAN_BUILD_1_RESULT.json',
 'CLEAN_BUILD_2_RESULT.json','FORBIDDEN_AUDIT.json','AXIOM_AUDIT.json','ANNOTATED_TAG_RESULT.json'
}
assert required <= names, sorted(required-names)
assert all(a.get('size',0)>0 for a in d['assets'])
PY

jq -n \
  --arg authority_commit "$AUTH" \
  --arg tag "$TAG" \
  --arg release_url "$(jq -r .url package/GITHUB_RELEASE_RESULT.json)" \
  --arg final_branch "$FINAL_BRANCH" \
  --arg archive_branch "$ARCHIVE_BRANCH" \
  '{pass:true,authority_commit:$authority_commit,annotated_tag:$tag,release_url:$release_url,final_branch:$final_branch,archive_branch:$archive_branch}' \
  > package/PUBLISH_RESULT.json

cat package/PUBLISH_RESULT.json
