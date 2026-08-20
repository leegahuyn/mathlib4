#!/usr/bin/env bash
set -Eeuo pipefail

BRANCH="${BRANCH:-fix/primality-sheaf-clean-build}"
MOCK2="PrimalitySheafVerification/Mock2.lean"
ADV="PrimalitySheafVerification/Mock2_Advanced.lean"
FA="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
INTEGRATED="PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"
QYM="PrimalitySheafVerification/QYM.lean"
OUTDIR=".lake/build/lib/lean/PrimalitySheafVerification"
LOGDIR="build-logs/focused-three-modules-v3"
FA_BASELINE_COMMIT="623dfac27a24c170330d6218005e67b06490b814"

mkdir -p "${OUTDIR}" "${LOGDIR}"
: > "${LOGDIR}/phase-status.txt"

module_name() {
  basename "$1" .lean
}

blob_at() {
  local ref="$1" path="$2" value
  value="$(git ls-tree "${ref}" -- "${path}" | awk '{print $3}')"
  if [[ -z "${value}" ]]; then
    printf '%s' MISSING
  else
    printf '%s' "${value}"
  fi
}

start_blob() {
  local path="$1" value
  if [[ -f "${path}" ]]; then
    value="$(git hash-object "${path}")"
  else
    value=MISSING
  fi
  printf '%s' "${value}"
}

START_MOCK2_BLOB="$(start_blob "${MOCK2}")"
START_ADV_BLOB="$(start_blob "${ADV}")"
START_FA_BLOB="$(start_blob "${FA}")"
START_INTEGRATED_BLOB="$(start_blob "${INTEGRATED}")"
START_QYM_BLOB="$(start_blob "${QYM}")"

cat > "${LOGDIR}/snapshot.txt" <<EOF
trigger_sha=${GITHUB_SHA:-$(git rev-parse HEAD)}
branch=${BRANCH}
mock2_blob=${START_MOCK2_BLOB}
advanced_blob=${START_ADV_BLOB}
functional_analysis_blob=${START_FA_BLOB}
integrated_blob=${START_INTEGRATED_BLOB}
qym_blob=${START_QYM_BLOB}
mock2_sha256=$(sha256sum "${MOCK2}" | awk '{print $1}')
advanced_sha256=$(sha256sum "${ADV}" | awk '{print $1}')
functional_analysis_sha256=$(sha256sum "${FA}" | awk '{print $1}')
integrated_sha256=$(if [[ -f "${INTEGRATED}" ]]; then sha256sum "${INTEGRATED}" | awk '{print $1}'; else echo MISSING; fi)
qym_sha256=$(sha256sum "${QYM}" | awk '{print $1}')
EOF

LAST_OPERATION="initialization"

summarize_log() {
  local log="$1" tag="$2"
  {
    echo "tag=${tag}"
    echo "error_count=$(grep -c 'error:' "${log}" 2>/dev/null || true)"
    echo "warning_count=$(grep -c 'warning:' "${log}" 2>/dev/null || true)"
    echo "maximum_error_count=$(grep -Eci 'maximum number of errors' "${log}" 2>/dev/null || true)"
    echo 'first_errors_begin'
    grep -n 'error:' "${log}" 2>/dev/null | head -n 10 || true
    echo 'first_errors_end'
    echo 'last_error_begin'
    grep -n 'error:' "${log}" 2>/dev/null | tail -n 1 || true
    echo 'last_error_end'
  } > "${LOGDIR}/${tag}.summary.txt"
}

on_error() {
  local rc=$?
  set +e
  {
    echo "overall_focused_status=FAIL"
    echo "trigger_sha=${GITHUB_SHA:-unknown}"
    echo "last_operation=${LAST_OPERATION}"
    echo "exit_code=${rc}"
    echo "head=$(git rev-parse HEAD 2>/dev/null || true)"
    echo "working_tree_begin"
    git status --short 2>/dev/null || true
    echo "working_tree_end"
  } > "${LOGDIR}/failure.txt"
  echo "Focused three-module gate failed at: ${LAST_OPERATION}" >&2
  exit "${rc}"
}
trap on_error ERR

static_audit() {
  local path="$1" tag="$2"
  LAST_OPERATION="static audit ${tag}"
  python3 - "${path}" <<'PY' | tee "${LOGDIR}/${tag}.trust-audit.txt"
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
src = path.read_text(encoding='utf-8')
out = []
i = 0
depth = 0
in_string = False
escaped = False
while i < len(src):
    if depth:
        if src.startswith('/-', i):
            depth += 1; out.extend('  '); i += 2
        elif src.startswith('-/', i):
            depth -= 1; out.extend('  '); i += 2
        else:
            out.append('\n' if src[i] == '\n' else ' '); i += 1
    elif in_string:
        ch = src[i]
        out.append('\n' if ch == '\n' else ' ')
        if escaped:
            escaped = False
        elif ch == '\\':
            escaped = True
        elif ch == '"':
            in_string = False
        i += 1
    elif src.startswith('/-', i):
        depth = 1; out.extend('  '); i += 2
    elif src.startswith('--', i):
        while i < len(src) and src[i] != '\n':
            out.append(' '); i += 1
    elif src[i] == '"':
        in_string = True; out.append(' '); i += 1
    else:
        out.append(src[i]); i += 1
if depth or in_string:
    raise SystemExit('unterminated comment or string')
code = ''.join(out)
patterns = {
    'sorry': r'\bsorry\b',
    'admit': r'\badmit\b',
    'global_axiom': r'(?m)^\s*axiom\b',
    'unsafe': r'\bunsafe\b',
    'native_decide': r'\bnative_decide\b',
    'Lean.ofReduceBool': r'\bLean\.ofReduceBool\b',
    'by_contra!': r'\bby_contra!\b',
}
bad = False
for key, pat in patterns.items():
    count = len(re.findall(pat, code))
    print(f'{key}={count}')
    bad |= count != 0
if bad:
    raise SystemExit(1)
PY
}

compile_once() {
  local path="$1" tag="$2"
  local name code log
  name="$(module_name "${path}")"
  log="${LOGDIR}/${tag}.log"
  LAST_OPERATION="compile ${tag}"
  rm -f \
    "${OUTDIR}/${name}.olean" \
    "${OUTDIR}/${name}.ilean" \
    "${OUTDIR}/${name}.olean.private"
  set +e
  lake env lean "${path}" \
    -o "${OUTDIR}/${name}.olean" \
    -i "${OUTDIR}/${name}.ilean" \
    > "${log}" 2>&1
  code=$?
  set -e
  echo "${code}" > "${LOGDIR}/${tag}.exit-code.txt"
  summarize_log "${log}" "${tag}"
  if [[ "${code}" -ne 0 ]]; then
    return "${code}"
  fi
  test -s "${OUTDIR}/${name}.olean"
  test -s "${OUTDIR}/${name}.ilean"
  test "$(grep -c 'error:' "${log}" || true)" -eq 0
  ! grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" "${log}"
}

compile_twice() {
  local path="$1" tag="$2"
  compile_once "${path}" "${tag}-pass1"
  compile_once "${path}" "${tag}-pass2"
}

probe_twice() {
  local path="$1" tag="$2"
  if compile_once "${path}" "${tag}-probe1" && compile_once "${path}" "${tag}-probe2"; then
    return 0
  fi
  return 1
}

statement_headers() {
  local path="$1" out="$2"
  python3 - "${path}" > "${out}" <<'PY'
from pathlib import Path
import re
import sys

src = Path(sys.argv[1]).read_text(encoding='utf-8')
# Preserve newlines while blanking comments and strings.
out=[]; i=0; depth=0; string=False; esc=False
while i < len(src):
    if depth:
        if src.startswith('/-',i): depth+=1; out.extend('  '); i+=2
        elif src.startswith('-/',i): depth-=1; out.extend('  '); i+=2
        else: out.append('\n' if src[i]=='\n' else ' '); i+=1
    elif string:
        ch=src[i]; out.append('\n' if ch=='\n' else ' ')
        if esc: esc=False
        elif ch=='\\': esc=True
        elif ch=='"': string=False
        i+=1
    elif src.startswith('/-',i): depth=1; out.extend('  '); i+=2
    elif src.startswith('--',i):
        while i<len(src) and src[i]!='\n': out.append(' '); i+=1
    elif src[i]=='"': string=True; out.append(' '); i+=1
    else: out.append(src[i]); i+=1
code=''.join(out)
pat=re.compile(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+([^\s(:]+)')
ms=list(pat.finditer(code))
for m in ms:
    start=m.start(); j=m.end(); par=br=cur=0
    while j < len(code):
        c=code[j]
        if c=='(': par+=1
        elif c==')': par-=1
        elif c=='[': br+=1
        elif c==']': br-=1
        elif c=='{': cur+=1
        elif c=='}': cur-=1
        if par==br==cur==0:
            if code.startswith(':=',j): break
            if re.match(r'\bby\b',code[j:]): break
            if re.match(r'\bwhere\b',code[j:]): break
        j+=1
    print(re.sub(r'\s+',' ',code[start:j]).strip())
PY
}

compare_statements() {
  local before="$1" after="$2" tag="$3"
  LAST_OPERATION="statement integrity ${tag}"
  statement_headers "${before}" "/tmp/${tag}.before.headers"
  statement_headers "${after}" "/tmp/${tag}.after.headers"
  {
    echo "before_count=$(wc -l < "/tmp/${tag}.before.headers")"
    echo "after_count=$(wc -l < "/tmp/${tag}.after.headers")"
  } | tee "${LOGDIR}/${tag}.statement-integrity.txt"
  if ! cmp -s "/tmp/${tag}.before.headers" "/tmp/${tag}.after.headers"; then
    diff -u "/tmp/${tag}.before.headers" "/tmp/${tag}.after.headers" \
      | head -n 200 | tee -a "${LOGDIR}/${tag}.statement-integrity.txt" || true
    return 1
  fi
  {
    echo 'statement_changed=0'
    echo 'assumptions_changed=0'
  } | tee -a "${LOGDIR}/${tag}.statement-integrity.txt"
}

push_verified_change() {
  local message="$1"
  shift
  local paths=("$@")
  local path key expected remote
  LAST_OPERATION="race guard and push: ${message}"
  git diff --check
  git add "${paths[@]}"
  git diff --cached --check
  git commit -m "${message}"
  git fetch origin "${BRANCH}"
  for path in "${paths[@]}"; do
    case "${path}" in
      "${ADV}") expected="${START_ADV_BLOB}" ;;
      "${FA}") expected="${START_FA_BLOB}" ;;
      "${INTEGRATED}") expected="${START_INTEGRATED_BLOB}" ;;
      "${QYM}") expected="${START_QYM_BLOB}" ;;
      *) echo "No recorded start blob for ${path}" >&2; return 1 ;;
    esac
    remote="$(blob_at "origin/${BRANCH}" "${path}")"
    printf '%s\n' "path=${path}" "start_blob=${expected}" "remote_blob=${remote}" \
      | tee -a "${LOGDIR}/race-guard.txt"
    test "${remote}" = "${expected}"
  done
  git rebase "origin/${BRANCH}"
  git push origin "HEAD:${BRANCH}"
}

write_hashes() {
  local tag="$1"
  shift
  local path name
  : > "${LOGDIR}/${tag}.hashes.txt"
  for path in "$@"; do
    name="$(module_name "${path}")"
    sha256sum "${path}" >> "${LOGDIR}/${tag}.hashes.txt"
    if [[ -f "${OUTDIR}/${name}.olean" ]]; then sha256sum "${OUTDIR}/${name}.olean" >> "${LOGDIR}/${tag}.hashes.txt"; fi
    if [[ -f "${OUTDIR}/${name}.ilean" ]]; then sha256sum "${OUTDIR}/${name}.ilean" >> "${LOGDIR}/${tag}.hashes.txt"; fi
  done
}

# ---------------------------------------------------------------------------
# Mandatory Mock2 regression before all focused phases.
# ---------------------------------------------------------------------------
static_audit "${MOCK2}" Mock2
compile_once "${MOCK2}" Mock2-regression-initial
echo 'Mock2 regression: PASS' | tee -a "${LOGDIR}/phase-status.txt"

# ---------------------------------------------------------------------------
# Phase A: Mock2_Advanced direct source, or deterministic v61-v68 candidate.
# ---------------------------------------------------------------------------
if probe_twice "${ADV}" Mock2_Advanced-direct; then
  static_audit "${ADV}" Mock2_Advanced
  write_hashes Mock2_Advanced-direct "${ADV}"
  echo 'Phase A Mock2_Advanced checked-in direct source: PASS' | tee -a "${LOGDIR}/phase-status.txt"
else
  git reset --hard HEAD
  cp "${ADV}" /tmp/Mock2_Advanced.before.lean
  : > "${LOGDIR}/Mock2_Advanced.repair-chain.txt"
  for n in 61 62 63 64 65 66 67 68; do
    script="scripts/repair_mock2_advanced_v${n}.py"
    test -f "${script}"
    LAST_OPERATION="apply ${script}"
    echo "RUN ${script}" | tee -a "${LOGDIR}/Mock2_Advanced.repair-chain.txt"
    python3 "${script}" 2>&1 | tee -a "${LOGDIR}/Mock2_Advanced.repair-application.log"
    echo "OK ${script} sha256=$(sha256sum "${ADV}" | awk '{print $1}')" \
      | tee -a "${LOGDIR}/Mock2_Advanced.repair-chain.txt"
  done
  mapfile -t changed < <(git diff --name-only)
  printf '%s\n' "${changed[@]}" > "${LOGDIR}/Mock2_Advanced.changed-files.txt"
  test "${#changed[@]}" -eq 1
  test "${changed[0]}" = "${ADV}"
  compare_statements /tmp/Mock2_Advanced.before.lean "${ADV}" Mock2_Advanced-candidate
  static_audit "${ADV}" Mock2_Advanced-candidate
  compile_once "${MOCK2}" Mock2-regression-after-advanced-repair
  compile_twice "${ADV}" Mock2_Advanced-candidate
  write_hashes Mock2_Advanced-candidate "${ADV}"
  candidate_sha="$(sha256sum "${ADV}" | awk '{print $1}')"
  push_verified_change "fix: materialize Mock2 Advanced v68 verified source (${candidate_sha})" "${ADV}"
  echo 'Phase A candidate materialized; next run must verify the checked-in source directly.' >> "${GITHUB_STEP_SUMMARY:-/dev/null}"
  exit 0
fi

# ---------------------------------------------------------------------------
# Phase B: FunctionalAnalysis direct source, or the established 289-315 chain.
# ---------------------------------------------------------------------------
FA_DIRECT=0
if probe_twice "${FA}" Mock2_FunctionalAnalysis-direct; then
  FA_DIRECT=1
  static_audit "${FA}" Mock2_FunctionalAnalysis
  echo 'Phase B Mock2_FunctionalAnalysis checked-in direct source: PASS' | tee -a "${LOGDIR}/phase-status.txt"
fi

if [[ "${FA_DIRECT}" -eq 0 ]]; then
  git reset --hard HEAD
  compile_once "${MOCK2}" Mock2-regression-before-functional-analysis-repair
  compile_twice "${ADV}" Mock2_Advanced-before-functional-analysis-repair

  cp "${FA}" /tmp/Mock2_FunctionalAnalysis.current.lean
  git fetch --depth=1 origin "${FA_BASELINE_COMMIT}"
  git show "${FA_BASELINE_COMMIT}:${FA}" > /tmp/Mock2_FunctionalAnalysis.baseline.lean
  # The deterministic historical repair chain may only replace the current file
  # when it preserves the complete theorem/lemma interface.
  if [[ "$(wc -l < /tmp/Mock2_FunctionalAnalysis.current.lean)" -gt 1000 ]]; then
    compare_statements /tmp/Mock2_FunctionalAnalysis.current.lean /tmp/Mock2_FunctionalAnalysis.baseline.lean FunctionalAnalysis-current-vs-baseline
  fi

  cp "${ADV}" /tmp/Mock2_Advanced.checked-in.lean
  git show "${FA_BASELINE_COMMIT}:${ADV}" > "${ADV}"
  cp /tmp/Mock2_FunctionalAnalysis.baseline.lean "${FA}"
  repair_scripts=(
    scripts/apply_two_hundred_eighty_ninth_pass_repairs.py
    scripts/apply_two_hundred_ninetieth_pass_repairs.py
    scripts/apply_two_hundred_ninety_first_pass_repairs.py
    scripts/apply_two_hundred_ninety_second_pass_repairs.py
    scripts/apply_two_hundred_ninety_third_pass_repairs.py
    scripts/apply_two_hundred_ninety_fourth_pass_repairs.py
    scripts/apply_two_hundred_ninety_fifth_pass_repairs.py
    scripts/apply_two_hundred_ninety_seventh_pass_repairs.py
    scripts/apply_two_hundred_ninety_eighth_pass_repairs.py
    scripts/apply_two_hundred_ninety_ninth_pass_repairs.py
    scripts/apply_three_hundredth_pass_repairs.py
    scripts/apply_three_hundred_ninth_pass_repairs.py
    scripts/apply_three_hundred_tenth_pass_repairs.py
    scripts/apply_three_hundred_eleventh_pass_repairs.py
    scripts/apply_three_hundred_twelfth_pass_repairs.py
    scripts/apply_three_hundred_thirteenth_pass_repairs.py
    scripts/apply_three_hundred_fourteenth_pass_repairs.py
    scripts/apply_three_hundred_fifteenth_pass_repairs.py
  )
  : > "${LOGDIR}/FunctionalAnalysis.repair-chain.txt"
  for script in "${repair_scripts[@]}"; do
    test -f "${script}"
    LAST_OPERATION="apply ${script}"
    echo "RUN ${script}" | tee -a "${LOGDIR}/FunctionalAnalysis.repair-chain.txt"
    python3 "${script}" 2>&1 | tee -a "${LOGDIR}/FunctionalAnalysis.repair-application.log"
    echo "OK ${script} fa_sha256=$(sha256sum "${FA}" | awk '{print $1}')" \
      | tee -a "${LOGDIR}/FunctionalAnalysis.repair-chain.txt"
  done
  cp /tmp/Mock2_Advanced.checked-in.lean "${ADV}"
  while IFS= read -r path; do
    [[ -z "${path}" || "${path}" = "${FA}" ]] || git restore --source=HEAD --worktree -- "${path}"
  done < <(git diff --name-only)
  test "$(git diff --name-only)" = "${FA}"
  compare_statements /tmp/Mock2_FunctionalAnalysis.baseline.lean "${FA}" Mock2_FunctionalAnalysis-candidate
  static_audit "${FA}" Mock2_FunctionalAnalysis-candidate-unsplit
  compile_twice "${FA}" Mock2_FunctionalAnalysis-candidate-unsplit

  # A substantive Integrated module stores the complete implementation.  The
  # historical FA path remains a compatibility import and deletes no API.
  cp "${FA}" "${INTEGRATED}"
  cat > "${FA}" <<'LEAN'
/-!
# Mock2 FunctionalAnalysis compatibility entry point

The complete checked-in implementation is provided by
`PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated`.
This historical module path re-exports the same public declarations.
-/
import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated
LEAN
  test "$(wc -l < "${INTEGRATED}")" -gt 1000
  static_audit "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated-candidate
  static_audit "${FA}" Mock2_FunctionalAnalysis-compatibility-candidate
  compile_twice "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated-candidate
  compile_twice "${FA}" Mock2_FunctionalAnalysis-compatibility-candidate
  write_hashes FunctionalAnalysis-candidate "${INTEGRATED}" "${FA}"
  candidate_sha="$(sha256sum "${INTEGRATED}" | awk '{print $1}')"
  push_verified_change "fix: materialize FunctionalAnalysis and substantive Integrated source (${candidate_sha})" "${FA}" "${INTEGRATED}"
  echo 'Phase B candidate materialized; next run must verify both checked-in sources directly.' >> "${GITHUB_STEP_SUMMARY:-/dev/null}"
  exit 0
fi

# ---------------------------------------------------------------------------
# Phase C: normalize and verify the substantive Integrated boundary.
# ---------------------------------------------------------------------------
FA_LINES="$(wc -l < "${FA}")"
INTEGRATED_LINES=0
if [[ -f "${INTEGRATED}" ]]; then INTEGRATED_LINES="$(wc -l < "${INTEGRATED}")"; fi

if [[ "${FA_LINES}" -gt 1000 ]]; then
  # A full implementation still in the historical path is moved byte-for-byte
  # into Integrated.  Refuse to overwrite a different substantive implementation.
  if [[ "${INTEGRATED_LINES}" -gt 1000 ]] && ! cmp -s "${FA}" "${INTEGRATED}"; then
    echo 'Both FA and Integrated are substantive but differ; refusing destructive normalization.' >&2
    false
  fi
  cp "${FA}" /tmp/Mock2_FunctionalAnalysis.full.lean
  cp "${FA}" "${INTEGRATED}"
  cat > "${FA}" <<'LEAN'
/-!
# Mock2 FunctionalAnalysis compatibility entry point

The complete checked-in implementation is provided by
`PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated`.
This historical module path re-exports the same public declarations.
-/
import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated
LEAN
  static_audit "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated-split
  static_audit "${FA}" Mock2_FunctionalAnalysis-compatibility-split
  compile_twice "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated-split
  compile_twice "${FA}" Mock2_FunctionalAnalysis-compatibility-split
  push_verified_change 'fix: restore substantive FunctionalAnalysis Integrated boundary' "${FA}" "${INTEGRATED}"
  echo 'Phase C Integrated boundary materialized; next run must verify checked-in sources directly.' >> "${GITHUB_STEP_SUMMARY:-/dev/null}"
  exit 0
fi

test -f "${INTEGRATED}"
test "${INTEGRATED_LINES}" -gt 1000
static_audit "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated
static_audit "${FA}" Mock2_FunctionalAnalysis-compatibility
compile_twice "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated-direct
compile_twice "${FA}" Mock2_FunctionalAnalysis-compatibility-direct
write_hashes FunctionalAnalysis-direct "${INTEGRATED}" "${FA}"
echo 'Phase C substantive Integrated checked-in direct source: PASS' | tee -a "${LOGDIR}/phase-status.txt"

# ---------------------------------------------------------------------------
# Phase D: QYM, after all dependency objects have been generated from source.
# ---------------------------------------------------------------------------
compile_once "${MOCK2}" Mock2-regression-before-QYM
compile_twice "${ADV}" Mock2_Advanced-regression-before-QYM
compile_twice "${INTEGRATED}" Mock2_FunctionalAnalysis_Integrated-regression-before-QYM
compile_twice "${FA}" Mock2_FunctionalAnalysis-regression-before-QYM
static_audit "${QYM}" QYM
compile_twice "${QYM}" QYM-direct
write_hashes QYM-direct "${QYM}"
echo 'Phase D QYM checked-in direct source: PASS' | tee -a "${LOGDIR}/phase-status.txt"

# ---------------------------------------------------------------------------
# Final no-repair direct-source sequence and success receipt.
# ---------------------------------------------------------------------------
compile_once "${MOCK2}" final-Mock2
compile_twice "${ADV}" final-Mock2_Advanced
compile_twice "${INTEGRATED}" final-Mock2_FunctionalAnalysis_Integrated
compile_twice "${FA}" final-Mock2_FunctionalAnalysis
compile_twice "${QYM}" final-QYM

# Compilation must not mutate a checked-in source.
test -z "$(git status --porcelain --untracked-files=no)"
write_hashes final-focused-sequence "${MOCK2}" "${ADV}" "${INTEGRATED}" "${FA}" "${QYM}"

python3 - <<'PY' > build-logs/focused-three-modules-v3-pass.json
from pathlib import Path
import hashlib
import json

paths = {
    'Mock2': Path('PrimalitySheafVerification/Mock2.lean'),
    'Mock2_Advanced': Path('PrimalitySheafVerification/Mock2_Advanced.lean'),
    'Mock2_FunctionalAnalysis': Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'),
    'Mock2_FunctionalAnalysis_Integrated': Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'),
    'QYM': Path('PrimalitySheafVerification/QYM.lean'),
}
report = {
    'overall_focused_status': 'PASS',
    'checked_in_direct_source_only': True,
    'runtime_source_repair_in_final_sequence': False,
    'clean_compile_passes_per_focused_module': 2,
    'error_count': 0,
    'missing_project_object_files': 0,
    'sorry_admit_sorryAx': 0,
    'new_global_user_axioms_in_focused_sources': 0,
    'unsafe_native_decide_Lean_ofReduceBool': 0,
    'theorem_statement_or_assumption_changes_by_repairs': 0,
    'sources': {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in paths.items()},
}
print(json.dumps(report, indent=2, sort_keys=True))
PY

LAST_OPERATION='commit final focused PASS receipt'
git add build-logs/focused-three-modules-v3-pass.json
git diff --cached --check
git commit -m 'ci: record focused three-module checked-in direct-source PASS'
git fetch origin "${BRANCH}"
# All focused source blobs must still be exactly those verified by this run.
for item in \
  "${MOCK2}:${START_MOCK2_BLOB}" \
  "${ADV}:${START_ADV_BLOB}" \
  "${FA}:${START_FA_BLOB}" \
  "${INTEGRATED}:${START_INTEGRATED_BLOB}" \
  "${QYM}:${START_QYM_BLOB}"; do
  path="${item%%:*}"
  expected="${item#*:}"
  remote="$(blob_at "origin/${BRANCH}" "${path}")"
  test "${remote}" = "${expected}"
done
git rebase "origin/${BRANCH}"
git push origin "HEAD:${BRANCH}"

{
  echo '## Overall focused status: PASS'
  echo '- Mock2 regression: PASS'
  echo '- Mock2_Advanced checked-in direct source, two clean compiles: PASS'
  echo '- Mock2_FunctionalAnalysis checked-in direct source, two clean compiles: PASS'
  echo '- substantive Integrated dependency, two clean compiles: PASS'
  echo '- QYM checked-in direct source, two clean compiles: PASS'
  echo '- errors and missing project object files: 0'
  echo '- sorry/admit/sorryAx, new global axioms, and prohibited proof escapes: 0'
  echo '- final sequence executed no source repair script'
} >> "${GITHUB_STEP_SUMMARY:-/dev/null}"
