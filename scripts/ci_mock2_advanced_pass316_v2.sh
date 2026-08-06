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
LOGDIR='/tmp/focused-advanced-pass316-v2'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'

mkdir -p "${LOGDIR}/source" "${LOGDIR}/logs" "${LOGDIR}/artifacts" "${OUTDIR}"
test "${SOURCE_BRANCH}" = 'fix/primality-sheaf-clean-build'
test "$(git rev-parse HEAD)" = "${SOURCE_SHA}"
test "$(git hash-object "${MOCK2}")" = "${EXPECTED_MOCK2_BLOB}"

start_blob="$(git hash-object "${TARGET}")"
start_sha="$(sha256sum "${TARGET}" | awk '{print $1}')"
if [[ "${start_blob}" = "${EXPECTED_START_BLOB}" ]]; then
  source_mode='candidate-repair'
else
  source_mode='checked-in-direct'
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
    apply_three_hundred_sixteenth_pass_repairs.py
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
actual_lines="$(wc -l < "${TARGET}")"
if [[ "${source_mode}" = 'candidate-repair' ]]; then
  test "${actual_blob}" != "${EXPECTED_START_BLOB}"
  grep -Fq 'UnnumberedFormulaLedger.ClaimEvidence.{0}' "${TARGET}"
  grep -Fq 'UnnumberedFormulaLedger.claimEvidence.{0}' "${TARGET}"
fi
printf '%s\n' \
  "advanced_candidate_blob=${actual_blob}" \
  "advanced_candidate_sha256=${actual_sha}" \
  "advanced_candidate_lines=${actual_lines}" \
  | tee -a "${LOGDIR}/snapshot.txt"
cp "${MOCK2}" "${LOGDIR}/source/Mock2.lean"
cp "${TARGET}" "${LOGDIR}/source/Mock2_Advanced.lean"

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

hard_checks = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "line_start_global_axiom": r"(?m)^\s*axiom\b",
    "unsafe": r"\bunsafe\b",
    "native_decide": r"\bnative_decide\b",
    "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    "placeholder": r"\bplaceholder\b",
    "unfinished_TODO_FIXME": r"\b(?:TODO|FIXME)\b",
}
review_pattern = re.compile(r"(?<![A-Za-z0-9_])by_contra!(?![A-Za-z0-9_])")
bad = False
review_lines: list[str] = []
for path in files:
    code = strip(path.read_text(encoding="utf-8"))
    print(f"[{path}]")
    for name, pattern in hard_checks.items():
        matches = list(re.finditer(pattern, code))
        print(f"{name}: {len(matches)}")
        if matches:
            bad = True
            for match in matches[:20]:
                line = code.count("\n", 0, match.start()) + 1
                print(f"  line {line}: {match.group(0)!r}")
    reviews = list(review_pattern.finditer(code))
    print(f"by_contra!_manual_review: {len(reviews)}")
    src_lines = path.read_text(encoding="utf-8").splitlines()
    for match in reviews:
        line = code.count("\n", 0, match.start()) + 1
        lo, hi = max(1, line - 3), min(len(src_lines), line + 3)
        review_lines.append(f"[{path}:{line}]\n")
        for n in range(lo, hi + 1):
            review_lines.append(f"{n}: {src_lines[n-1]}\n")
        review_lines.append("\n")
Path("/tmp/focused-advanced-pass316-v2/by-contra-review.txt").write_text(
    "".join(review_lines) if review_lines else "by_contra!: 0\n",
    encoding="utf-8",
)
if bad:
    raise SystemExit("forbidden executable token or global axiom detected")
PY

compile_module() {
  local module="$1"
  local pass="$2"
  local log="${LOGDIR}/logs/${module}-pass${pass}.log"
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
    {
      echo 'first_errors:'
      grep -n 'error:' "${log}" | head -10 || true
      echo 'last_error:'
      grep -n 'error:' "${log}" | tail -1 || true
      echo "total_errors=${errors}"
      grep -in 'maximum number of errors' "${log}" || true
      tail -240 "${log}" || true
    } | tee "${LOGDIR}/${module}-failure-summary-pass${pass}.txt"
    return "${code}"
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

for module in Mock2 Mock2_Advanced; do
  cp "${OUTDIR}/${module}.olean" "${LOGDIR}/artifacts/candidate-${module}.olean"
  cp "${OUTDIR}/${module}.ilean" "${LOGDIR}/artifacts/candidate-${module}.ilean"
done

if [[ "${source_mode}" = 'candidate-repair' ]]; then
  test "$(git diff --name-only)" = "${TARGET}"
else
  git diff --exit-code
fi

sha256sum "${MOCK2}" "${TARGET}" \
  "${OUTDIR}/Mock2.olean" "${OUTDIR}/Mock2.ilean" \
  "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
  "${LOGDIR}/logs/Mock2-pass1.log" "${LOGDIR}/logs/Mock2-pass2.log" \
  "${LOGDIR}/logs/Mock2_Advanced-pass1.log" "${LOGDIR}/logs/Mock2_Advanced-pass2.log" \
  | tee "${LOGDIR}/candidate-provenance-sha256.txt"
printf '%s\n' "utc_candidate_compiled=$(date -u +%FT%TZ)" >> "${LOGDIR}/snapshot.txt"

if [[ "${source_mode}" = 'candidate-repair' ]]; then
  remote_head="$(git ls-remote origin "refs/heads/${SOURCE_BRANCH}" | awk '{print $1}')"
  echo "trigger_head=${SOURCE_SHA}"
  echo "remote_head_before_local_commit=${remote_head}"
  test "${remote_head}" = "${SOURCE_SHA}"

  git config user.name 'github-actions[bot]'
  git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
  git add "${TARGET}"
  test "$(git diff --cached --name-only)" = "${TARGET}"
  git commit -m 'fix: materialize Mock2 Advanced pass 316 verified source'
  materialized_sha="$(git rev-parse HEAD)"
  git diff --exit-code
  test "$(git hash-object "${TARGET}")" = "${actual_blob}"
  printf '%s\n' \
    "materialized_local_commit=${materialized_sha}" \
    "runtime_repair_for_direct_validation=0" \
    | tee -a "${LOGDIR}/snapshot.txt"

  for pass in direct1 direct2; do
    compile_module Mock2 "${pass}"
    compile_module Mock2_Advanced "${pass}"
  done

  for module in Mock2 Mock2_Advanced; do
    cp "${OUTDIR}/${module}.olean" "${LOGDIR}/artifacts/${module}.olean"
    cp "${OUTDIR}/${module}.ilean" "${LOGDIR}/artifacts/${module}.ilean"
  done

  sha256sum "${MOCK2}" "${TARGET}" \
    "${OUTDIR}/Mock2.olean" "${OUTDIR}/Mock2.ilean" \
    "${OUTDIR}/Mock2_Advanced.olean" "${OUTDIR}/Mock2_Advanced.ilean" \
    "${LOGDIR}/logs/Mock2-passdirect1.log" "${LOGDIR}/logs/Mock2-passdirect2.log" \
    "${LOGDIR}/logs/Mock2_Advanced-passdirect1.log" \
    "${LOGDIR}/logs/Mock2_Advanced-passdirect2.log" \
    | tee "${LOGDIR}/provenance-sha256.txt"

  cat > "${LOGDIR}/direct-source-proof.txt" <<EOF2
Mock2 Advanced checked-in direct-source proof before push
commit=${materialized_sha}
trigger_commit=${SOURCE_SHA}
workflow_run=${GITHUB_RUN_ID}
workflow_attempt=${GITHUB_RUN_ATTEMPT}
source_blob=${actual_blob}
source_sha256=${actual_sha}
runtime_repair_for_direct_validation=0
Mock2_clean_passes=0,0
Mock2_Advanced_clean_passes=0,0
EOF2

  remote_head="$(git ls-remote origin "refs/heads/${SOURCE_BRANCH}" | awk '{print $1}')"
  echo "remote_head_before_push=${remote_head}"
  test "${remote_head}" = "${SOURCE_SHA}"
  git push origin "HEAD:${SOURCE_BRANCH}"
  printf '%s\n' \
    "materialized_pushed_commit=${materialized_sha}" \
    "utc_direct_compiled=$(date -u +%FT%TZ)" \
    | tee -a "${LOGDIR}/snapshot.txt"
  exit 0
fi

for module in Mock2 Mock2_Advanced; do
  cp "${OUTDIR}/${module}.olean" "${LOGDIR}/artifacts/${module}.olean"
  cp "${OUTDIR}/${module}.ilean" "${LOGDIR}/artifacts/${module}.ilean"
done
mv "${LOGDIR}/candidate-provenance-sha256.txt" "${LOGDIR}/provenance-sha256.txt"
printf '%s\n' "utc_direct_compiled=$(date -u +%FT%TZ)" >> "${LOGDIR}/snapshot.txt"
cat > "${LOGDIR}/direct-source-proof.txt" <<EOF2
Mock2 Advanced checked-in direct-source proof
commit=${SOURCE_SHA}
workflow_run=${GITHUB_RUN_ID}
workflow_attempt=${GITHUB_RUN_ATTEMPT}
source_blob=${actual_blob}
source_sha256=${actual_sha}
runtime_repair=0
Mock2_clean_passes=0,0
Mock2_Advanced_clean_passes=0,0
EOF2
