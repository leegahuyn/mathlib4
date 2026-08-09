#!/usr/bin/env bash
set -euo pipefail

OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pass339-final-two-pass'
mkdir -p "${EVIDENCE}/logs" "${OUTDIR}" build-logs
echo 'pass,module,exit_code,error_count,warning_count,source_sha256' > "${EVIDENCE}/compile-summary.csv"

compile_module() {
  local pass="$1" module="$2"
  local source="PrimalitySheafVerification/${module}.lean"
  local log="${EVIDENCE}/logs/${module}-pass${pass}.log"
  local code errors warnings sha
  test -f "${source}"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" "${OUTDIR}/${module}.olean.private"
  sha="$(sha256sum "${source}" | awk '{print $1}')"
  set +e
  lake env lean -DmaxErrors=2000 "${source}" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s,%s\n' "${pass}" "${module}" "${code}" "${errors}" "${warnings}" "${sha}" \
    >> "${EVIDENCE}/compile-summary.csv"
  if [[ "${code}" -ne 0 || "${errors}" -ne 0 ]]; then
    {
      echo "pass=${pass} module=${module} exit=${code} errors=${errors}"
      grep -n 'error:' "${log}" | head -120 || true
      echo '--- last errors ---'
      grep -n 'error:' "${log}" | tail -80 || true
      tail -900 "${log}" || true
    } > "${EVIDENCE}/logs/${module}-pass${pass}-failure-summary.txt"
    return 1
  fi
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  ! grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" "${log}"
}

mapfile -t mock3_files < <(find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print | sort)
printf '%s\n' "${mock3_files[@]:-}" > "${EVIDENCE}/mock3-files.txt"
modules=(Mock2 Mock2_Advanced Mock2_FunctionalAnalysis_Integrated Mock2_FunctionalAnalysis)
for file in "${mock3_files[@]}"; do modules+=("$(basename "${file}" .lean)"); done
modules+=(QYM)

for pass in 1 2; do
  rm -rf "${OUTDIR}"
  mkdir -p "${OUTDIR}"
  for module in "${modules[@]}"; do compile_module "${pass}" "${module}"; done
done

python3 - \
  PrimalitySheafVerification/Mock2_Advanced.lean \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \
  "${mock3_files[@]}" \
  PrimalitySheafVerification/QYM.lean <<'PY' | tee "${EVIDENCE}/trust-audit.txt"
from pathlib import Path
import re,sys

def strip(s):
    out=[];i=0;depth=0;string=False;escaped=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            ch=s[i];out.append('\n' if ch=='\n' else ' ')
            if escaped:escaped=False
            elif ch=='\\':escaped=True
            elif ch=='"':string=False
            i+=1
        elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif s.startswith('--',i):
            while i<len(s) and s[i]!='\n':out.append(' ');i+=1
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    if depth or string:raise SystemExit('unterminated comment/string')
    return ''.join(out)
checks={'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b','Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
for raw in sys.argv[1:]:
    p=Path(raw);code=strip(p.read_text(encoding='utf-8'))
    print(f'[{p}]')
    for name,pat in checks.items():
        n=len(re.findall(pat,code));print(f'{name}={n}');bad|=n!=0
if bad:raise SystemExit('forbidden executable token detected')
PY

{
  echo 'PASS339_FINAL_TWO_PASS_SUCCESS'
  echo "verified_commit=$(git rev-parse HEAD)"
  echo "verified_utc=$(date -u +%FT%TZ)"
  echo 'required_order=Mock2 -> Mock2_Advanced -> Mock2_FunctionalAnalysis_Integrated -> Mock2_FunctionalAnalysis -> Mock3* -> QYM'
  echo 'passes=2'
  echo
  cat "${EVIDENCE}/compile-summary.csv"
  echo
  sha256sum \
    PrimalitySheafVerification/Mock2_Advanced.lean \
    PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
    PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \
    "${mock3_files[@]}" \
    PrimalitySheafVerification/QYM.lean
} > build-logs/PASS339_FINAL_TWO_PASS_SUCCESS.txt
cp build-logs/PASS339_FINAL_TWO_PASS_SUCCESS.txt "${EVIDENCE}/"
