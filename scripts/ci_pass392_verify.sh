#!/usr/bin/env bash
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
export PATH="${HOME}/.elan/bin:${PATH}"
EVIDENCE="${PASS392_EVIDENCE:-/tmp/pass392}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
LOG="${EVIDENCE}/logs"
mkdir -p "$OUT" "$LOG" "${EVIDENCE}/source"
echo 'module,run,exit_code,error_count,warning_count,first_line' \
  > "${EVIDENCE}/compile-summary.csv"

python3 - <<'PY'
from pathlib import Path
import json, re
src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text(encoding='utf-8')
out=[]; i=0; depth=0; string=False; esc=False
while i < len(src):
    if depth:
        if src.startswith('/-',i): depth+=1; out.extend('  '); i+=2
        elif src.startswith('-/',i): depth-=1; out.extend('  '); i+=2
        else: out.append('\n' if src[i]=='\n' else ' '); i+=1
    elif string:
        c=src[i]; out.append('\n' if c=='\n' else ' ')
        if esc: esc=False
        elif c=='\\': esc=True
        elif c=='"': string=False
        i+=1
    elif src.startswith('/-',i): depth=1; out.extend('  '); i+=2
    elif src.startswith('--',i):
        while i < len(src) and src[i]!='\n': out.append(' '); i+=1
    elif src[i]=='"': string=True; out.append(' '); i+=1
    else: out.append(src[i]); i+=1
if depth or string: raise SystemExit('unterminated comment/string')
code=''.join(out)
pats={'sorry':r'\bsorry\b','admit':r'\badmit\b','global_axiom':r'(?m)^\s*axiom\b',
      'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b',
      'Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
result={k:len(re.findall(v,code)) for k,v in pats.items()}
Path('/tmp/pass392/forbidden-token-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(result)
if any(result.values()): raise SystemExit(1)
PY

audit_rc=$?
if [[ "$audit_rc" -ne 0 ]]; then
  printf 'stage=trust-audit\nexit_code=1\n' > "${EVIDENCE}/final-status.txt"
  exit 1
fi

compile_one() {
  local module="$1" run="$2" log rc errors warnings first
  log="${LOG}/${module}-${run}.log"
  rm -f "${OUT}/${module}.olean" "${OUT}/${module}.ilean" \
    "${OUT}/${module}.olean.private"
  lake env lean -DmaxErrors=400 \
    "PrimalitySheafVerification/${module}.lean" \
    -o "${OUT}/${module}.olean" -i "${OUT}/${module}.ilean" \
    >"${log}" 2>&1
  rc=$?
  errors="$(grep -c 'error:' "$log" || true)"
  warnings="$(grep -c 'warning:' "$log" || true)"
  first="$(grep -m1 -oE '\.lean:[0-9]+' "$log" | sed 's/.*://' || true)"
  printf '%s,%s,%s,%s,%s,%s\n' \
    "$module" "$run" "$rc" "$errors" "$warnings" "$first" \
    >> "${EVIDENCE}/compile-summary.csv"
  {
    echo "module=${module}"; echo "run=${run}"; echo "exit_code=${rc}"
    echo "error_count=${errors}"; echo "warning_count=${warnings}"
    echo "first_line=${first}"; echo 'first_errors:'
    grep -n 'error:' "$log" | head -80 || true
    echo 'last_errors:'; grep -n 'error:' "$log" | tail -40 || true
    echo 'tail:'; tail -700 "$log" || true
  } > "${EVIDENCE}/${module}-${run}-result.txt"
  [[ "$rc" -eq 0 && "$errors" -eq 0 ]] || return 1
  test -s "${OUT}/${module}.olean" && test -s "${OUT}/${module}.ilean"
}

twice() { compile_one "$1" pass1 && compile_one "$1" pass2; }

final=0
stage='Mock2_FunctionalAnalysis'
if ! twice Mock2_FunctionalAnalysis; then
  final=1
else
  stage='Mock2_FunctionalAnalysis_Integrated'
  if ! twice Mock2_FunctionalAnalysis_Integrated; then
    final=1
  else
    stage='Mock3'
    mapfile -t mock3 < <(find PrimalitySheafVerification -maxdepth 1 \
      -type f -name 'Mock3*.lean' -printf '%f\n' | sort)
    for file in "${mock3[@]}"; do
      if ! twice "${file%.lean}"; then final=1; break; fi
    done
    if [[ "$final" -eq 0 ]]; then
      stage='QYM'
      if ! twice QYM; then final=1; fi
    fi
  fi
fi

printf 'stage=%s\nexit_code=%s\n' "$stage" "$final" \
  | tee "${EVIDENCE}/final-status.txt"
cp PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
  "${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass392.lean"
exit "$final"
