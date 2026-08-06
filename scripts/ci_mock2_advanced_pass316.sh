#!/usr/bin/env bash
set -euo pipefail

: "${SOURCE_SHA:?}"
: "${SOURCE_BRANCH:?}"
: "${PR_NUMBER:?}"
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_RUN_ID:?}"
: "${GITHUB_RUN_ATTEMPT:?}"
: "${GITHUB_TOKEN:?}"

MOCK2='PrimalitySheafVerification/Mock2.lean'
TARGET='PrimalitySheafVerification/Mock2_Advanced.lean'
EXPECTED_MOCK2_BLOB='94f8894b5f866701955a105044b8958a8deb7734'
EXPECTED_START_BLOB='54bbfa432f1b8a6554d25104a0c29d4f41999984'
EXPECTED_CANDIDATE_BLOB='b71fddf282b107ce14924609c84a97fb240737eb'
EXPECTED_CANDIDATE_SHA256='e59496026992858e176443990940305db05300e211eb2b09962ec540808af2d4'
LOGDIR='/tmp/focused-advanced-pass316'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'

mkdir -p "${LOGDIR}" "${OUTDIR}"
test "${SOURCE_BRANCH}" = 'fix/primality-sheaf-clean-build'
test "$(git rev-parse HEAD)" = "${SOURCE_SHA}"
test "$(git hash-object "${MOCK2}")" = "${EXPECTED_MOCK2_BLOB}"

start_blob="$(git hash-object "${TARGET}")"
start_sha="$(sha256sum "${TARGET}" | awk '{print $1}')"
if [[ "${start_blob}" = "${EXPECTED_START_BLOB}" ]]; then
  source_mode='candidate-repair'
elif [[ "${start_blob}" = "${EXPECTED_CANDIDATE_BLOB}" && \
        "${start_sha}" = "${EXPECTED_CANDIDATE_SHA256}" ]]; then
  source_mode='checked-in-direct'
else
  echo "Unexpected Mock2_Advanced source: blob=${start_blob} sha256=${start_sha}" >&2
  exit 1
fi

printf '%s\n' \
  "repository=${GITHUB_REPOSITORY}" \
  "source_sha=${SOURCE_SHA}" \
  "source_branch=${SOURCE_BRANCH}" \
  "source_mode=${source_mode}" \
  "mock2_blob=$(git hash-object "${MOCK2}")" \
  "advanced_start_blob=${start_blob}" \
  "advanced_start_sha256=${start_sha}" \
  "workflow_run_id=${GITHUB_RUN_ID}" \
  "workflow_run_attempt=${GITHUB_RUN_ATTEMPT}" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${LOGDIR}/snapshot.txt"

if [[ "${source_mode}" = 'candidate-repair' ]]; then
  scripts=(
    apply_two_hundred_eighty_ninth_pass_repairs.py
    apply_two_hundred_ninetieth_pass_repairs.py
    apply_two_hundred_ninety_first_pass_repairs.py
    apply_two_hundred_ninety_second_pass_repairs.py
    apply_two_hundred_ninety_third_pass_repairs.py
    apply_two_hundred_ninety_fourth_pass_repairs.py
    apply_two_hundred_ninety_fifth_pass_repairs.py
    apply_two_hundred_ninety_seventh_pass_repairs.py
    apply_two_hundred_ninety_eighth_pass_repairs.py
    apply_two_hundred_ninety_ninth_pass_repairs.py
    apply_three_hundredth_pass_repairs.py
    apply_three_hundred_ninth_pass_repairs.py
    apply_three_hundred_tenth_pass_repairs.py
    apply_three_hundred_eleventh_pass_repairs.py
    apply_three_hundred_twelfth_pass_repairs.py
    repair_mock2_advanced_v68.py
  )
  for script in "${scripts[@]}"; do
    echo "===== scripts/${script} ====="
    python3 "scripts/${script}"
  done 2>&1 | tee "${LOGDIR}/repair-application.log"

  while IFS= read -r changed; do
    if [[ -n "${changed}" && "${changed}" != "${TARGET}" ]]; then
      git restore --source=HEAD --worktree -- "${changed}"
    fi
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${TARGET}"
else
  echo 'No runtime repair executed; checked-in direct source selected.' \
    | tee "${LOGDIR}/repair-application.log"
  git diff --exit-code
fi

git diff --check
actual_blob="$(git hash-object "${TARGET}")"
actual_sha="$(sha256sum "${TARGET}" | awk '{print $1}')"
test "${actual_blob}" = "${EXPECTED_CANDIDATE_BLOB}"
test "${actual_sha}" = "${EXPECTED_CANDIDATE_SHA256}"
printf '%s\n' \
  "advanced_candidate_blob=${actual_blob}" \
  "advanced_candidate_sha256=${actual_sha}" \
  "advanced_candidate_lines=$(wc -l < "${TARGET}")" \
  | tee -a "${LOGDIR}/snapshot.txt"

python3 - <<'PY' | tee "${LOGDIR}/forbidden-token-audit.txt"
from pathlib import Path
import re

files = [
    Path("PrimalitySheafVerification/Mock2.lean"),
    Path("PrimalitySheafVerification/Mock2_Advanced.lean"),
]

def strip(src: str) -> str:
    out, i, depth, string, escaped = [], 0, 0, False, False
    while i < len(src):
        if depth:
            if src.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif src.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if src[i] == "\n" else " "); i += 1
        elif string:
            ch = src[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif ch == '"': string = False
            i += 1
        elif src.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif src.startswith("--", i):
            while i < len(src) and src[i] != "\n":
                out.append(" "); i += 1
        elif src[i] == '"':
            string = True; out.append(" "); i += 1
        else:
            out.append(src[i]); i += 1
    if depth or string:
        raise SystemExit("unterminated comment or string")
    return "".join(out)

checks = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "line_start_global_axiom": r"(?m)^\s*axiom\b",
    "unsafe": r"\bunsafe\b",
    "native_decide": r"\bnative_decide\b",
    "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    "by_contra!": r"\bby_contra!\b",
    "placeholder": r"\bplaceholder\b",
    "unfinished_TODO_FIXME": r"\b(?:TODO|FIXME)\b",
}
bad = False
for path in files:
    code = strip(path.read_text(encoding="utf-8"))
    print(f"[{path}]")
    for name, pattern in checks.items():
        matches = list(re.finditer(pattern, code))
        print(f"{name}: {len(matches)}")
        if matches:
            bad = True
            for match in matches[:20]:
                line = code.count("\n", 0, match.start()) + 1
                print(f"  line {line}: {match.group(0)!r}")
if bad:
    raise SystemExit("forbidden executable token or global axiom detected")
PY

compile_module() {
  local module="$1"
  local pass="$2"
  local log="${LOGDIR}/${module}-pass${pass}.log"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/${module}.lean" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" \
    >"${log}" 2>&1
  local code=$?
  set -e
  local errors warnings
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' \
    "${module}" "${pass}" "${code}" "${errors}" "${warnings}" \
    >> "${LOGDIR}/compile-summary.csv"
  echo "${code}" > "${LOGDIR}/${module}-exit-pass${pass}.txt"
  if [[ "${code}" -ne 0 ]]; then
    echo 'first_errors:'
    grep -n 'error:' "${log}" | head -10 || true
    echo 'last_error:'
    grep -n 'error:' "${log}" | tail -1 || true
    echo "total_errors=${errors}"
    grep -in 'maximum number of errors' "${log}" || true
    tail -240 "${log}" || true
    exit "${code}"
  fi
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  ! grep -Eqi \
    "maximum number of errors|PANIC|segmentation fault|stack overflow|missing object file|declaration uses 'sorry'|sorryAx" \
    "${log}"
}

echo 'module,pass,exit_code,error_count,warning_count' > "${LOGDIR}/compile-summary.csv"
for pass in 1 2; do
  compile_module Mock2 "${pass}"
  compile_module Mock2_Advanced "${pass}"
done

if [[ "${source_mode}" = 'candidate-repair' ]]; then
  test "$(git diff --name-only)" = "${TARGET}"
else
  git diff --exit-code
fi

sha256sum "${MOCK2}" "${TARGET}" \
  "${OUTDIR}/Mock2.olean" "${OUTDIR}/Mock2.ilean" \
  "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
  | tee "${LOGDIR}/provenance-sha256.txt"
printf '%s\n' "utc_compiled=$(date -u +%FT%TZ)" >> "${LOGDIR}/snapshot.txt"

if [[ "${source_mode}" = 'candidate-repair' ]]; then
  remote_head="$(git ls-remote origin "refs/heads/${SOURCE_BRANCH}" | awk '{print $1}')"
  echo "trigger_head=${SOURCE_SHA}"
  echo "remote_head=${remote_head}"
  test "${remote_head}" = "${SOURCE_SHA}"
  git config user.name 'github-actions[bot]'
  git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
  git add "${TARGET}"
  test "$(git diff --cached --name-only)" = "${TARGET}"
  git commit -m 'fix: materialize Mock2 Advanced pass 316 verified source'
  git push origin "HEAD:${SOURCE_BRANCH}"
  exit 0
fi

mock2_olean_sha="$(sha256sum "${OUTDIR}/Mock2.olean" | awk '{print $1}')"
mock2_ilean_sha="$(sha256sum "${OUTDIR}/Mock2.ilean" | awk '{print $1}')"
advanced_olean_sha="$(sha256sum "${OUTDIR}/Mock2_Advanced.olean" | awk '{print $1}')"
advanced_ilean_sha="$(sha256sum "${OUTDIR}/Mock2_Advanced.ilean" | awk '{print $1}')"
summary="$(cat "${LOGDIR}/compile-summary.csv")"
comment_file="${LOGDIR}/pr-comment.md"
cat > "${comment_file}" <<EOF
<!-- mock2-advanced-pass316-direct-source-proof -->
## Mock2 Advanced pass 316 checked-in direct-source proof

- Commit: \`${SOURCE_SHA}\`
- Workflow run: \`${GITHUB_RUN_ID}\`, attempt \`${GITHUB_RUN_ATTEMPT}\`
- Source mode: checked-in direct source; runtime repair not executed
- Mock2 blob: \`${EXPECTED_MOCK2_BLOB}\`
- Mock2_Advanced blob: \`${EXPECTED_CANDIDATE_BLOB}\`
- Mock2_Advanced SHA-256: \`${EXPECTED_CANDIDATE_SHA256}\`
- Mock2 regression clean passes: exit 0 / exit 0
- Mock2_Advanced clean passes: exit 0 / exit 0
- Executable forbidden-token/global-axiom audit: 0
- Missing object / maximum-error / PANIC / sorryAx markers: 0
- Mock2.olean SHA-256: \`${mock2_olean_sha}\`
- Mock2.ilean SHA-256: \`${mock2_ilean_sha}\`
- Mock2_Advanced.olean SHA-256: \`${advanced_olean_sha}\`
- Mock2_Advanced.ilean SHA-256: \`${advanced_ilean_sha}\`

\`\`\`csv
${summary}
\`\`\`
EOF
python3 - "${comment_file}" "${LOGDIR}/comment.json" <<'PY'
from pathlib import Path
import json, sys
body = Path(sys.argv[1]).read_text(encoding="utf-8")
Path(sys.argv[2]).write_text(json.dumps({"body": body}), encoding="utf-8")
PY
curl --fail --silent --show-error \
  -X POST \
  -H "Authorization: Bearer ${GITHUB_TOKEN}" \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "https://api.github.com/repos/${GITHUB_REPOSITORY}/issues/${PR_NUMBER}/comments" \
  --data-binary "@${LOGDIR}/comment.json" \
  > "${LOGDIR}/comment-response.json"
cat "${LOGDIR}/comment-response.json"
