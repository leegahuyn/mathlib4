#!/usr/bin/env bash
set -uo pipefail

BRANCH='ci/fa319-isolated-20260807'
PASS_RUN='31159696948'
PASS_JOB='92827136991'
ROOT="${GITHUB_WORKSPACE:-$PWD}"
TARGET_DIR='PrimalitySheafVerification'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pass327-fa-qym-recovery'
MOCK2="${TARGET_DIR}/Mock2.lean"
ADVANCED="${TARGET_DIR}/Mock2_Advanced.lean"
FA="${TARGET_DIR}/Mock2_FunctionalAnalysis.lean"
INTEGRATED="${TARGET_DIR}/Mock2_FunctionalAnalysis_Integrated.lean"
QYM="${TARGET_DIR}/QYM.lean"
mkdir -p "${EVIDENCE}/artifacts" "${EVIDENCE}/downloads" \
  "${EVIDENCE}/logs" "${EVIDENCE}/source" "${OUTDIR}"
cd "${ROOT}"

printf 'module,pass,exit_code,error_count,warning_count,source_sha256\n' \
  > "${EVIDENCE}/compile-summary.csv"

strip_audit() {
  python3 - "$@" <<'PY'
from pathlib import Path
import re, sys

def strip(source: str) -> str:
    output=[]; i=0; depth=0; string=False; escaped=False
    while i < len(source):
        if depth:
            if source.startswith('/-', i): depth += 1; output.extend('  '); i += 2
            elif source.startswith('-/', i): depth -= 1; output.extend('  '); i += 2
            else: output.append('\n' if source[i] == '\n' else ' '); i += 1
        elif string:
            c=source[i]; output.append('\n' if c == '\n' else ' ')
            if escaped: escaped=False
            elif c == '\\': escaped=True
            elif c == '"': string=False
            i += 1
        elif source.startswith('/-', i): depth=1; output.extend('  '); i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n': output.append(' '); i += 1
        elif source[i] == '"': string=True; output.append(' '); i += 1
        else: output.append(source[i]); i += 1
    if depth or string: raise SystemExit('unterminated comment or string')
    return ''.join(output)

checks={
  'sorry':r'\bsorry\b', 'admit':r'\badmit\b',
  'global_axiom':r'(?m)^\s*axiom\b', 'unsafe':r'\bunsafe\b',
  'native_decide':r'\bnative_decide\b',
  'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b',
}
bad=False
for name in sys.argv[1:]:
    path=Path(name); code=strip(path.read_text(encoding='utf-8'))
    print(f'[{path}]')
    for label, pattern in checks.items():
        count=len(re.findall(pattern, code)); print(f'{label}={count}')
        bad |= count != 0
if bad: raise SystemExit(1)
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
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" \
    >"${log}" 2>&1
  rc=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s,%s\n' "${module}" "${label}" "$rc" \
    "$errors" "$warnings" "$sha" >> "${EVIDENCE}/compile-summary.csv"
  if [[ "$rc" -eq 0 && "$errors" -eq 0 && \
        -s "${OUTDIR}/${module}.olean" && -s "${OUTDIR}/${module}.ilean" ]] && \
      ! grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses ['\"]sorry|PANIC|segmentation fault|stack overflow" "${log}"; then
    return 0
  fi
  return 1
}

error_count() {
  grep -c 'error:' "$1" 2>/dev/null || true
}

extract_error_context() {
  local source="$1" log="$2" output="$3"
  python3 - "$source" "$log" "$output" <<'PY'
from pathlib import Path
import re, sys
source=Path(sys.argv[1]); log=Path(sys.argv[2]); output=Path(sys.argv[3])
lines=source.read_text(encoding='utf-8').splitlines()
text=log.read_text(encoding='utf-8', errors='replace')
blocks=[]; seen=set()
for m in re.finditer(r'PrimalitySheafVerification/[^:\n]+\.lean:(\d+):(\d+): error:', text):
    line=int(m.group(1))
    if line in seen: continue
    seen.add(line)
    start=max(1,line-18); end=min(len(lines),line+28)
    context='\n'.join(f'{i}: {lines[i-1]}' for i in range(start,end+1))
    tail=text[m.start():].split('\nPrimalitySheafVerification/',1)[0][:5000]
    blocks.append(f'ERROR AT LINE {line}\n{tail}\n\nSOURCE CONTEXT\n{context}')
    if len(blocks)>=18: break
output.write_text('\n\n====================\n\n'.join(blocks),encoding='utf-8')
PY
}

# PASS 327 provenance is queried dynamically from the exact run and job.
printf '%s\n' "requested_run=${PASS_RUN}" "requested_job=${PASS_JOB}" \
  "trigger_head=$(git rev-parse HEAD)" "trigger_branch=${GITHUB_REF_NAME:-unknown}" \
  "utc=$(date -u +%FT%TZ)" | tee "${EVIDENCE}/provenance.txt"

gh api "repos/${GITHUB_REPOSITORY}/actions/runs/${PASS_RUN}" \
  > "${EVIDENCE}/pass-run.json"
gh api "repos/${GITHUB_REPOSITORY}/actions/jobs/${PASS_JOB}" \
  > "${EVIDENCE}/pass-job.json"
gh api "repos/${GITHUB_REPOSITORY}/actions/jobs/${PASS_JOB}/logs" \
  > "${EVIDENCE}/downloads/pass-job-log.bin" || true
python3 - <<'PY'
from pathlib import Path
import zipfile
p=Path('/tmp/pass327-fa-qym-recovery/downloads/pass-job-log.bin')
out=Path('/tmp/pass327-fa-qym-recovery/logs/pass-job.log')
raw=p.read_bytes() if p.exists() else b''
if raw[:4] == b'PK\x03\x04':
    with zipfile.ZipFile(p) as z:
        out.write_text('\n'.join(z.read(n).decode('utf-8','replace') for n in z.namelist()),encoding='utf-8')
else:
    out.write_text(raw.decode('utf-8','replace'),encoding='utf-8')
PY

gh api --paginate "repos/${GITHUB_REPOSITORY}/actions/runs/${PASS_RUN}/artifacts" \
  > "${EVIDENCE}/pass-artifacts.json"
python3 - <<'PY' > "${EVIDENCE}/artifact-list.tsv"
import json
from pathlib import Path
raw=Path('/tmp/pass327-fa-qym-recovery/pass-artifacts.json').read_text()
objects=[]
for chunk in raw.splitlines():
    try: objects.append(json.loads(chunk))
    except json.JSONDecodeError: pass
for obj in objects:
    for a in obj.get('artifacts',[]):
        if not a.get('expired'): print(a['id'], a['name'], sep='\t')
PY
while IFS=$'\t' read -r id name; do
  [[ -n "$id" ]] || continue
  gh api "repos/${GITHUB_REPOSITORY}/actions/artifacts/${id}/zip" \
    > "${EVIDENCE}/downloads/${id}.zip"
  mkdir -p "${EVIDENCE}/downloads/${id}"
  unzip -q -o "${EVIDENCE}/downloads/${id}.zip" \
    -d "${EVIDENCE}/downloads/${id}"
done < "${EVIDENCE}/artifact-list.tsv"
find "${EVIDENCE}/downloads" -type f | sort > "${EVIDENCE}/downloaded-files.txt"

strip_audit "$MOCK2" "$ADVANCED" | tee "${EVIDENCE}/dependency-audit.txt"
compile_one "$MOCK2" dependency-Mock2

# Prefer the checked-in Advanced source when it is already the PASS source;
# otherwise test every source recovered from the exact PASS 327 artifacts.
cp "$ADVANCED" "${EVIDENCE}/source/Mock2_Advanced.checked-in.lean"
best_adv=''; best_adv_errors=999999; index=0
{
  printf '%s\n' "$ADVANCED"
  find "${EVIDENCE}/downloads" -type f -iname '*Mock2_Advanced*.lean' -print
  find "${EVIDENCE}/downloads" -type f -iname 'repaired-source.lean' -print
} | awk '!seen[$0]++' > "${EVIDENCE}/advanced-candidates.txt"
while IFS= read -r candidate; do
  [[ -s "$candidate" ]] || continue
  index=$((index+1)); cp "$candidate" "$ADVANCED"
  set +e; compile_one "$ADVANCED" "Advanced-candidate-${index}"; rc=$?; set -e
  count="$(error_count "${EVIDENCE}/logs/Advanced-candidate-${index}.log")"
  if (( count < best_adv_errors )); then
    best_adv_errors=$count; best_adv="$candidate"
    cp "$ADVANCED" "${EVIDENCE}/source/Mock2_Advanced.best.lean"
  fi
  [[ "$rc" -eq 0 ]] && break
done < "${EVIDENCE}/advanced-candidates.txt"
[[ -s "${EVIDENCE}/source/Mock2_Advanced.best.lean" ]] || \
  cp "${EVIDENCE}/source/Mock2_Advanced.checked-in.lean" \
    "${EVIDENCE}/source/Mock2_Advanced.best.lean"
cp "${EVIDENCE}/source/Mock2_Advanced.best.lean" "$ADVANCED"
compile_one "$ADVANCED" Advanced-direct-1
compile_one "$ADVANCED" Advanced-direct-2
strip_audit "$ADVANCED" | tee "${EVIDENCE}/Advanced-final-audit.txt"

# Evaluate FA sources recovered from the exact PASS artifacts and checked-in PR9.
cp "$FA" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.checked-in.lean"
best_fa=''; best_fa_errors=999999; best_fa_rc=99; index=0
{
  printf '%s\n' "$FA"
  find "${EVIDENCE}/downloads" -type f -iname '*Mock2_FunctionalAnalysis*.lean' -print
  find "${EVIDENCE}/downloads" -type f \( -iname 'candidate*.lean' -o -iname 'repaired-source.lean' \) -print
} | awk '!seen[$0]++' > "${EVIDENCE}/fa-candidates.txt"
while IFS= read -r candidate; do
  [[ -s "$candidate" ]] || continue
  index=$((index+1)); cp "$candidate" "$FA"
  set +e; compile_one "$FA" "FA-candidate-${index}"; rc=$?; set -e
  count="$(error_count "${EVIDENCE}/logs/FA-candidate-${index}.log")"
  if (( count < best_fa_errors )) || { (( count == best_fa_errors )) && (( rc < best_fa_rc )); }; then
    best_fa_errors=$count; best_fa_rc=$rc; best_fa="$candidate"
    cp "$FA" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.best.lean"
    cp "${EVIDENCE}/logs/FA-candidate-${index}.log" \
      "${EVIDENCE}/logs/FA-best.log"
  fi
  [[ "$rc" -eq 0 ]] && break
done < "${EVIDENCE}/fa-candidates.txt"
cp "${EVIDENCE}/source/Mock2_FunctionalAnalysis.best.lean" "$FA"

# A PASS candidate is materialized only after two direct compiles.  When it
# still fails, expose the exact independent frontier for the next source pass.
set +e; compile_one "$FA" FA-best-direct-1; fa_rc=$?; set -e
if [[ "$fa_rc" -ne 0 ]]; then
  extract_error_context "$FA" "${EVIDENCE}/logs/FA-best-direct-1.log" \
    "${EVIDENCE}/FA-next-errors-with-context.txt"
  cp "$FA" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.next-pass-input.lean"
  echo "FA_NOT_YET_PASS errors=$(error_count "${EVIDENCE}/logs/FA-best-direct-1.log")" \
    | tee "${EVIDENCE}/status.txt"
  exit 20
fi
compile_one "$FA" FA-best-direct-2
strip_audit "$FA" | tee "${EVIDENCE}/FA-final-audit.txt"

# The integrated layer (the Mock3 bridge in this repository) must pass before QYM.
compile_one "$INTEGRATED" Integrated-direct-1
compile_one "$INTEGRATED" Integrated-direct-2
while IFS= read -r mock3; do
  [[ -n "$mock3" ]] || continue
  compile_one "$mock3" "$(basename "$mock3" .lean)-direct-1"
  compile_one "$mock3" "$(basename "$mock3" .lean)-direct-2"
done < <(find "$TARGET_DIR" -maxdepth 1 -type f -name 'Mock3*.lean' | sort)
compile_one "$QYM" QYM-direct-1
compile_one "$QYM" QYM-direct-2
strip_audit "$INTEGRATED" "$QYM" | tee "${EVIDENCE}/Integrated-QYM-audit.txt"

# Only the four requested source layers may be materialized here.
git diff --check
changed="$(git diff --name-only)"
while IFS= read -r path; do
  case "$path" in
    "$ADVANCED"|"$FA"|"$INTEGRATED"|"$QYM"|PrimalitySheafVerification/Mock3*.lean|'') ;;
    *) echo "unexpected changed path: $path" >&2; exit 91 ;;
  esac
done <<< "$changed"
remote_head="$(git ls-remote origin "refs/heads/${BRANCH}" | awk '{print $1}')"
trigger_head="$(git rev-parse HEAD)"
test "$remote_head" = "$trigger_head"
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "$ADVANCED" "$FA" "$INTEGRATED" "$QYM"
find "$TARGET_DIR" -maxdepth 1 -type f -name 'Mock3*.lean' -print0 | xargs -0 -r git add
git diff --cached --quiet || git commit -m 'fix: materialize PASS 327 FA and QYM sources'
git push origin "HEAD:${BRANCH}"
echo 'PASS_327_FA_INTEGRATED_QYM_SUCCESS' | tee "${EVIDENCE}/status.txt"
