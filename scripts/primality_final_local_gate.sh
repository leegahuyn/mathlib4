#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "${ROOT}"
TARGET_DIR='PrimalitySheafVerification'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE="${FINAL_EVIDENCE_DIR:-/tmp/primality-final-local-gate}"
PRIORITY_MARKER='build-logs/pass327-targets-pass.json'
MOCK1_MARKER='build-logs/mock1-family-pass.json'
FINAL_MARKER='build-logs/final-local-gate-pass.json'
mkdir -p "${EVIDENCE}/logs" "${EVIDENCE}/artifacts" "${EVIDENCE}/audit" build-logs

test -s "${PRIORITY_MARKER}"
test -s "${MOCK1_MARKER}"
python3 - "${PRIORITY_MARKER}" "${MOCK1_MARKER}" <<'PY'
import json,sys
for name in sys.argv[1:]:
    data=json.load(open(name,encoding='utf-8'))
    if data.get('status') != 'PASS':
        raise SystemExit(f'{name} is not a PASS marker: {data}')
PY

modules=(Spt1 Spt2 Spt3 Spt4 Spt5 Spt6 Spt7 Mock1 Mock1_Advanced Mock2 Mock2_Advanced Mock2_FunctionalAnalysis)
support=(Mock2_FunctionalAnalysis_Integrated)
while IFS= read -r file; do
  [[ -n "${file}" ]] || continue
  module="$(basename "${file}" .lean)"
  support+=("${module}")
done < <(find "${TARGET_DIR}" -maxdepth 1 -type f -name 'Mock3*.lean' | sort)
modules+=(QYM)

printf 'clean_pass,module,exit_code,error_count,warning_count,source_sha256,olean_sha256,ilean_sha256\n' \
  > "${EVIDENCE}/compile-summary.csv"

strip_audit() {
  python3 - "$@" <<'PY'
from pathlib import Path
import re,sys

def strip(source):
    out=[]; i=0; depth=0; string=False; esc=False
    while i < len(source):
        if depth:
            if source.startswith('/-',i): depth+=1; out+=[' ',' ']; i+=2
            elif source.startswith('-/',i): depth-=1; out+=[' ',' ']; i+=2
            else: out.append('\n' if source[i]=='\n' else ' '); i+=1
        elif string:
            c=source[i]; out.append('\n' if c=='\n' else ' ')
            if esc: esc=False
            elif c=='\\': esc=True
            elif c=='"': string=False
            i+=1
        elif source.startswith('/-',i): depth=1; out+=[' ',' ']; i+=2
        elif source.startswith('--',i):
            while i<len(source) and source[i]!='\n': out.append(' '); i+=1
        elif source[i]=='"': string=True; out.append(' '); i+=1
        else: out.append(source[i]); i+=1
    if depth or string: raise SystemExit('unterminated comment/string')
    return ''.join(out)
checks={
 'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
 'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b',
 'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
for item in sys.argv[1:]:
    path=Path(item); code=strip(path.read_text(encoding='utf-8'))
    print(f'[{path}]')
    for name,pat in checks.items():
        n=len(re.findall(pat,code)); print(f'{name}={n}'); bad |= n != 0
if bad: raise SystemExit(1)
PY
}

all_sources=()
for module in "${modules[@]}" "${support[@]}"; do
  path="${TARGET_DIR}/${module}.lean"
  [[ -f "${path}" ]] && all_sources+=("${path}")
done
all_sources+=("${TARGET_DIR}/BuildAll.lean")
strip_audit "${all_sources[@]}" | tee "${EVIDENCE}/audit/forbidden-token-audit.txt"

compile_one() {
  local pass="$1" module="$2" path log rc errors warnings source_sha olean_sha ilean_sha
  path="${TARGET_DIR}/${module}.lean"
  log="${EVIDENCE}/logs/pass${pass}-${module}.log"
  mkdir -p "${OUTDIR}"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean -DmaxErrors=2000 "${path}" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" \
    >"${log}" 2>&1
  rc=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  source_sha="$(sha256sum "${path}" | awk '{print $1}')"
  olean_sha=''; ilean_sha=''
  [[ -s "${OUTDIR}/${module}.olean" ]] && olean_sha="$(sha256sum "${OUTDIR}/${module}.olean" | awk '{print $1}')"
  [[ -s "${OUTDIR}/${module}.ilean" ]] && ilean_sha="$(sha256sum "${OUTDIR}/${module}.ilean" | awk '{print $1}')"
  printf '%s,%s,%s,%s,%s,%s,%s,%s\n' "$pass" "$module" "$rc" "$errors" "$warnings" \
    "$source_sha" "$olean_sha" "$ilean_sha" >> "${EVIDENCE}/compile-summary.csv"
  if [[ "$rc" -ne 0 || "$errors" -ne 0 || -z "$olean_sha" || -z "$ilean_sha" ]]; then
    grep -n 'error:' "${log}" | head -100 > "${EVIDENCE}/logs/pass${pass}-${module}-errors.txt" || true
    return 1
  fi
  if grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses ['\"]sorry|PANIC|segmentation fault|stack overflow" "${log}"; then
    return 1
  fi
}

for pass in 1 2; do
  rm -rf "${OUTDIR}"
  mkdir -p "${OUTDIR}"
  for module in Spt1 Spt2 Spt3 Spt4 Spt5 Spt6 Spt7 Mock1 Mock1_Advanced Mock2 Mock2_Advanced Mock2_FunctionalAnalysis; do
    compile_one "$pass" "$module"
  done
  for module in "${support[@]}"; do
    [[ -f "${TARGET_DIR}/${module}.lean" ]] && compile_one "$pass" "$module"
  done
  compile_one "$pass" QYM
  compile_one "$pass" BuildAll
  find "${OUTDIR}" -maxdepth 1 -type f \( -name '*.olean' -o -name '*.ilean' \) \
    -print0 | sort -z | xargs -0 sha256sum > "${EVIDENCE}/artifacts/pass${pass}-artifact-sha256.txt"
done

# Generate a whole-file public declaration audit for Spt5.  Existing private
# helpers are intentionally skipped because they are not addressable after import.
python3 - <<'PY'
from pathlib import Path
import re
src=Path('PrimalitySheafVerification/Spt5.lean').read_text(encoding='utf-8').splitlines()
stack=[]; names=[]
namespace_re=re.compile(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_\'\.]*|«[^»]+»)')
end_re=re.compile(r'^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_\'\.]*|«[^»]+»))?\s*$')
decl_re=re.compile(r'^\s*(?P<mods>(?:(?:noncomputable|protected|nonrec|private)\s+)*)'
                   r'(?P<kind>theorem|lemma|corollary|def|abbrev|opaque|instance)\s+'
                   r'(?P<name>[A-Za-z_][A-Za-z0-9_\'\.]*|«[^»]+»)')
comment=0
for raw in src:
    line=raw
    # Good enough for namespace/declaration prefixes; nested comments before a
    # declaration are stripped without trying to parse proof bodies.
    i=0; out=[]
    while i < len(line):
        if comment:
            if line.startswith('/-',i): comment+=1; i+=2
            elif line.startswith('-/',i): comment-=1; i+=2
            else: i+=1
        elif line.startswith('/-',i): comment=1; i+=2
        elif line.startswith('--',i): break
        else: out.append(line[i]); i+=1
    clean=''.join(out)
    m=namespace_re.match(clean)
    if m:
        stack.extend(m.group(1).split('.')); continue
    m=end_re.match(clean)
    if m and stack:
        explicit=m.group(1)
        if explicit:
            pieces=explicit.split('.')
            if stack[-len(pieces):] == pieces: del stack[-len(pieces):]
            else: stack.pop()
        else: stack.pop()
        continue
    m=decl_re.match(clean)
    if not m or 'private' in m.group('mods').split(): continue
    name=m.group('name')
    full='.'.join(stack+[name]) if stack else name
    if full not in names: names.append(full)
out=Path('.lake/Spt5WholeFileAudit.lean')
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text('import PrimalitySheafVerification.Spt5\n\n' +
               '\n'.join(f'#print axioms {name}' for name in names) + '\n',encoding='utf-8')
Path('/tmp/primality-final-local-gate/audit/Spt5-public-declarations.txt').write_text(
    '\n'.join(names)+'\n',encoding='utf-8')
if len(names) < 10: raise SystemExit(f'suspiciously few Spt5 declarations: {len(names)}')
PY

set +e
lake env lean .lake/Spt5WholeFileAudit.lean \
  > "${EVIDENCE}/audit/Spt5-whole-file-axioms.log" 2>&1
spt5_rc=$?
set -e
test "$spt5_rc" -eq 0
python3 - "${EVIDENCE}/audit/Spt5-whole-file-axioms.log" <<'PY'
from pathlib import Path
import re,sys
text=Path(sys.argv[1]).read_text(encoding='utf-8',errors='replace')
if 'sorryAx' in text or "declaration uses 'sorry'" in text:
    raise SystemExit('Spt5 audit contains sorryAx')
allowed={'propext','Classical.choice','Quot.sound'}
blocks=re.findall(r'depends on axioms:\s*\[(.*?)\]',text,flags=re.S)
seen=set()
for block in blocks:
    for token in re.findall(r'[A-Za-z_][A-Za-z0-9_\.]*',block):
        seen.add(token)
unexpected=seen-allowed
if unexpected:
    raise SystemExit(f'unexpected Spt5 axioms: {sorted(unexpected)}')
print('allowed_axioms=' + ','.join(sorted(seen)))
PY

python3 - <<'PY'
from pathlib import Path
import csv,json,subprocess,time
rows=list(csv.DictReader(open('/tmp/primality-final-local-gate/compile-summary.csv',encoding='utf-8')))
expected_passes={'1','2'}
if {r['clean_pass'] for r in rows} != expected_passes:
    raise SystemExit('both clean passes were not recorded')
for r in rows:
    if r['exit_code']!='0' or r['error_count']!='0' or not r['olean_sha256'] or not r['ilean_sha256']:
        raise SystemExit(f'failed row: {r}')
marker={
 'status':'PASS',
 'clean_rebuilds':2,
 'runtime_source_repair':False,
 'compile_rows':rows,
 'spt5_whole_file_axiom_audit':'PASS',
 'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'verified_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 'verified_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
}
Path('build-logs/final-local-gate-pass.json').write_text(
 json.dumps(marker,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
PY

echo 'FINAL_LOCAL_GATE_PASS' | tee "${EVIDENCE}/status.txt"
