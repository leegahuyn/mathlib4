#!/usr/bin/env bash
set -euo pipefail

ROOT="${GITHUB_WORKSPACE:-$PWD}"
TARGET_DIR='PrimalitySheafVerification'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/gpt56-pass336-gate'
MOCK2="${TARGET_DIR}/Mock2.lean"
ADVANCED="${TARGET_DIR}/Mock2_Advanced.lean"
FA="${TARGET_DIR}/Mock2_FunctionalAnalysis.lean"
INTEGRATED="${TARGET_DIR}/Mock2_FunctionalAnalysis_Integrated.lean"
QYM="${TARGET_DIR}/QYM.lean"
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
FA_BASELINE_COMMIT='402e2b7aa053b9c43d95f24e6146efbc5ccf714b'
EXPECTED_FA_SHA256='204acd949c17f55013487819b215886ae5c1c5fb4d125d4683871f8fb94847ad'

cd "${ROOT}"
mkdir -p "${EVIDENCE}/logs" "${EVIDENCE}/source" "${OUTDIR}"
printf 'module,pass,exit_code,error_count,warning_count,source_sha256\n' \
  > "${EVIDENCE}/compile-summary.csv"
printf '%s\n' \
  "head=$(git rev-parse HEAD)" \
  "branch=${GITHUB_HEAD_REF:-${GITHUB_REF_NAME:-unknown}}" \
  "utc=$(date -u +%FT%TZ)" \
  "lean_toolchain=$(cat lean-toolchain)" \
  > "${EVIDENCE}/provenance.txt"

strip_audit() {
  python3 - "$@" <<'PY'
from pathlib import Path
import re
import sys

CHECKS = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "global_axiom": r"(?m)^\s*axiom\b",
    "unsafe": r"\bunsafe\b",
    "native_decide": r"\bnative_decide\b",
    "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
}

def strip(source: str) -> str:
    out = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif in_string:
            c = source[i]
            out.append('\n' if c == '\n' else ' ')
            if escaped:
                escaped = False
            elif c == '\\':
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                out.append(' '); i += 1
        elif source[i] == '"':
            in_string = True; out.append(' '); i += 1
        else:
            out.append(source[i]); i += 1
    if depth or in_string:
        raise SystemExit('unterminated comment or string')
    return ''.join(out)

bad = False
for raw in sys.argv[1:]:
    path = Path(raw)
    code = strip(path.read_text(encoding='utf-8'))
    print(f'[{path}]')
    for label, pattern in CHECKS.items():
        count = len(re.findall(pattern, code))
        print(f'{label}={count}')
        bad = bad or count != 0
if bad:
    raise SystemExit(1)
PY
}

compile_one() {
  local path="$1" label="$2" module log rc errors warnings sha
  module="$(basename "${path}" .lean)"
  log="${EVIDENCE}/logs/${label}.log"
  sha="$(sha256sum "${path}" | awk '{print $1}')"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean -DmaxErrors=2000 "${path}" \
    -o "${OUTDIR}/${module}.olean" \
    -i "${OUTDIR}/${module}.ilean" \
    > "${log}" 2>&1
  rc=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s,%s\n' \
    "${module}" "${label}" "${rc}" "${errors}" "${warnings}" "${sha}" \
    >> "${EVIDENCE}/compile-summary.csv"
  if [[ "${rc}" -eq 0 && "${errors}" -eq 0 \
        && -s "${OUTDIR}/${module}.olean" \
        && -s "${OUTDIR}/${module}.ilean" ]] \
      && ! grep -Eqi \
        "maximum number of errors|object file .* does not exist|sorryAx|declaration uses ['\"]sorry|PANIC|segmentation fault|stack overflow" \
        "${log}"; then
    return 0
  fi
  return 1
}

write_failure_context() {
  local source="$1" log="$2" output="$3"
  python3 - "${source}" "${log}" "${output}" <<'PY'
from pathlib import Path
import re
import sys

source = Path(sys.argv[1])
log = Path(sys.argv[2])
out = Path(sys.argv[3])
lines = source.read_text(encoding='utf-8').splitlines()
text = log.read_text(encoding='utf-8', errors='replace')
pattern = re.compile(r'PrimalitySheafVerification/[^:\n]+\.lean:(\d+):(\d+): error(?:\([^\n)]*\))?:')
matches = list(pattern.finditer(text))
blocks = []
seen = set()
for index, match in enumerate(matches):
    line = int(match.group(1))
    if line in seen:
        continue
    seen.add(line)
    start = max(1, line - 24)
    end = min(len(lines), line + 38)
    next_start = matches[index + 1].start() if index + 1 < len(matches) else len(text)
    diagnostic = text[match.start():next_start].strip()[:7000]
    context = '\n'.join(f'{n}: {lines[n - 1]}' for n in range(start, end + 1))
    blocks.append(f'ERROR AT LINE {line}\n{diagnostic}\n\nSOURCE CONTEXT\n{context}')
    if len(blocks) >= 24:
        break
out.write_text('\n\n====================\n\n'.join(blocks), encoding='utf-8')
PY
}

apply_repair() {
  local script="$1"
  echo "===== ${script} =====" | tee -a "${EVIDENCE}/logs/repair-chain.log"
  python3 "scripts/${script}" 2>&1 | tee -a "${EVIDENCE}/logs/repair-chain.log"
  printf '%s,%s\n' "${script}" "$(sha256sum "${FA}" | awk '{print $1}')" \
    >> "${EVIDENCE}/repair-source-sha256.csv"
}

cp "${ADVANCED}" /tmp/gpt56-current-advanced.lean
git -c fetch.writeCommitGraph=false fetch \
  --no-tags --no-recurse-submodules origin \
  "${ADVANCED_BASELINE_COMMIT}" "${FA_BASELINE_COMMIT}" \
  2>&1 | tee "${EVIDENCE}/logs/fetch-baselines.log"
git show "${FA_BASELINE_COMMIT}:${FA}" > "${FA}"
git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"

: > "${EVIDENCE}/logs/repair-chain.log"
echo 'script,fa_source_sha256' > "${EVIDENCE}/repair-source-sha256.csv"
for script in \
  apply_two_hundred_eighty_ninth_pass_repairs.py \
  apply_two_hundred_ninetieth_pass_repairs.py \
  apply_two_hundred_ninety_first_pass_repairs.py \
  apply_two_hundred_ninety_second_pass_repairs.py \
  apply_two_hundred_ninety_third_pass_repairs.py \
  apply_two_hundred_ninety_fourth_pass_repairs.py \
  apply_two_hundred_ninety_fifth_pass_repairs.py \
  apply_two_hundred_ninety_seventh_pass_repairs.py \
  apply_two_hundred_ninety_eighth_pass_repairs.py \
  apply_two_hundred_ninety_ninth_pass_repairs.py \
  apply_three_hundredth_pass_repairs.py \
  apply_three_hundred_ninth_pass_repairs.py \
  apply_three_hundred_tenth_pass_repairs.py \
  apply_three_hundred_eleventh_pass_repairs.py \
  apply_three_hundred_twelfth_pass_repairs.py \
  apply_three_hundred_thirteenth_pass_repairs.py \
  apply_three_hundred_fourteenth_pass_repairs.py \
  apply_three_hundred_fifteenth_pass_repairs.py \
  fa316_driver.py \
  apply_three_hundred_seventeenth_pass_functional_analysis_repairs.py \
  apply_three_hundred_eighteenth_pass_functional_analysis_repairs.py \
  apply_three_hundred_nineteenth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twentieth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_first_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_second_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_third_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_fourth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_fifth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_sixth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_seventh_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_ninth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirtieth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_first_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_second_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_third_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_fourth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_fifth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_sixth_pass_functional_analysis_repairs.py; do
  apply_repair "${script}"
done

cp /tmp/gpt56-current-advanced.lean "${ADVANCED}"
actual_fa_sha="$(sha256sum "${FA}" | awk '{print $1}')"
printf 'expected_fa_sha256=%s\nactual_fa_sha256=%s\n' \
  "${EXPECTED_FA_SHA256}" "${actual_fa_sha}" \
  | tee "${EVIDENCE}/candidate-sha256.txt"
test "${actual_fa_sha}" = "${EXPECTED_FA_SHA256}"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass336.lean"

strip_audit "${MOCK2}" "${ADVANCED}" "${FA}" "${INTEGRATED}" "${QYM}" \
  | tee "${EVIDENCE}/trust-audit.txt"

compile_one "${MOCK2}" Mock2-direct-1 || {
  write_failure_context "${MOCK2}" "${EVIDENCE}/logs/Mock2-direct-1.log" \
    "${EVIDENCE}/Mock2-failure-context.txt"
  echo 'FAIL: Mock2 direct compile' | tee "${EVIDENCE}/status.txt"
  exit 10
}
compile_one "${ADVANCED}" Advanced-direct-1 || {
  write_failure_context "${ADVANCED}" "${EVIDENCE}/logs/Advanced-direct-1.log" \
    "${EVIDENCE}/Advanced-failure-context.txt"
  echo 'FAIL: Mock2 Advanced direct compile 1' | tee "${EVIDENCE}/status.txt"
  exit 11
}
compile_one "${ADVANCED}" Advanced-direct-2 || {
  write_failure_context "${ADVANCED}" "${EVIDENCE}/logs/Advanced-direct-2.log" \
    "${EVIDENCE}/Advanced-failure-context.txt"
  echo 'FAIL: Mock2 Advanced direct compile 2' | tee "${EVIDENCE}/status.txt"
  exit 12
}
compile_one "${FA}" FA-pass336-direct-1 || {
  write_failure_context "${FA}" "${EVIDENCE}/logs/FA-pass336-direct-1.log" \
    "${EVIDENCE}/FA-failure-context.txt"
  echo 'FAIL: FunctionalAnalysis PASS 336 direct compile 1' | tee "${EVIDENCE}/status.txt"
  exit 20
}
compile_one "${FA}" FA-pass336-direct-2 || {
  write_failure_context "${FA}" "${EVIDENCE}/logs/FA-pass336-direct-2.log" \
    "${EVIDENCE}/FA-failure-context.txt"
  echo 'FAIL: FunctionalAnalysis PASS 336 direct compile 2' | tee "${EVIDENCE}/status.txt"
  exit 21
}
compile_one "${INTEGRATED}" Integrated-direct-1 || {
  write_failure_context "${INTEGRATED}" "${EVIDENCE}/logs/Integrated-direct-1.log" \
    "${EVIDENCE}/Integrated-failure-context.txt"
  echo 'FAIL: Integrated direct compile 1' | tee "${EVIDENCE}/status.txt"
  exit 30
}
compile_one "${INTEGRATED}" Integrated-direct-2 || {
  write_failure_context "${INTEGRATED}" "${EVIDENCE}/logs/Integrated-direct-2.log" \
    "${EVIDENCE}/Integrated-failure-context.txt"
  echo 'FAIL: Integrated direct compile 2' | tee "${EVIDENCE}/status.txt"
  exit 31
}
compile_one "${QYM}" QYM-direct-1 || {
  write_failure_context "${QYM}" "${EVIDENCE}/logs/QYM-direct-1.log" \
    "${EVIDENCE}/QYM-failure-context.txt"
  echo 'FAIL: QYM direct compile 1' | tee "${EVIDENCE}/status.txt"
  exit 40
}
compile_one "${QYM}" QYM-direct-2 || {
  write_failure_context "${QYM}" "${EVIDENCE}/logs/QYM-direct-2.log" \
    "${EVIDENCE}/QYM-failure-context.txt"
  echo 'FAIL: QYM direct compile 2' | tee "${EVIDENCE}/status.txt"
  exit 41
}

echo 'PASS: Mock2, Advanced x2, FunctionalAnalysis x2, Integrated x2, QYM x2' \
  | tee "${EVIDENCE}/status.txt"
