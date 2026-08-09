#!/usr/bin/env bash
set +e

candidate=${1:?candidate source required}
out=${2:-build-logs/fa419-ordered-final-gate}
mkdir -p "$out" .lake/build/lib/lean/PrimalitySheafVerification
rm -rf "$out"/*

cp "$candidate" PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean

compile_one() {
  local stem=$1
  local run=$2
  local src="PrimalitySheafVerification/${stem}.lean"
  local olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  rm -f "$olean" "$ilean"
  lake env lean -DmaxErrors=1800 -DwarningAsError=false \
    -o "$olean" -i "$ilean" "$src" > "$out/${stem}-run${run}.log" 2>&1
  local rc=$?
  printf '%s' "$rc" > "$out/${stem}-run${run}.exit"
  if test "$rc" -eq 0 && test -s "$olean" && test -s "$ilean"; then
    return 0
  fi
  return 1
}

final=1
compile_one Mock2 1; rc_m2=$?
compile_one Mock2_Advanced 1; rc_m2a=$?
rc_fa1=125; rc_fa2=125
rc_int1=125; rc_int2=125
rc_mock3=125; rc_qym1=125; rc_qym2=125

if test "$rc_m2" -eq 0 && test "$rc_m2a" -eq 0; then
  compile_one Mock2_FunctionalAnalysis 1; rc_fa1=$?
  if test "$rc_fa1" -eq 0; then
    compile_one Mock2_FunctionalAnalysis 2; rc_fa2=$?
  fi
fi

if test "$rc_fa2" -eq 0; then
  if test -f PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean; then
    compile_one Mock2_FunctionalAnalysis_Integrated 1; rc_int1=$?
    if test "$rc_int1" -eq 0; then
      compile_one Mock2_FunctionalAnalysis_Integrated 2; rc_int2=$?
    fi
  else
    rc_int1=126; rc_int2=126
    printf 'required Integrated source missing\n' > "$out/Integrated_MISSING.txt"
  fi
fi

if test "$rc_int2" -eq 0; then
  shopt -s nullglob
  mock3_sources=(PrimalitySheafVerification/Mock3*.lean)
  if test "${#mock3_sources[@]}" -eq 0; then
    rc_mock3=126
    printf 'required Mock3 source missing\n' > "$out/Mock3_MISSING.txt"
  else
    rc_mock3=0
    for src in "${mock3_sources[@]}"; do
      stem=$(basename "$src" .lean)
      compile_one "$stem" 1; r1=$?
      r2=125
      if test "$r1" -eq 0; then
        compile_one "$stem" 2; r2=$?
      fi
      if test "$r1" -ne 0 || test "$r2" -ne 0; then
        rc_mock3=1
      fi
    done
  fi
fi

if test "$rc_int2" -eq 0 && test "$rc_mock3" -eq 0; then
  if test -f PrimalitySheafVerification/QYM.lean; then
    compile_one QYM 1; rc_qym1=$?
    if test "$rc_qym1" -eq 0; then
      compile_one QYM 2; rc_qym2=$?
    fi
  else
    rc_qym1=126; rc_qym2=126
    printf 'required QYM source missing\n' > "$out/QYM_MISSING.txt"
  fi
fi

if test "$rc_fa1" -eq 0 && test "$rc_fa2" -eq 0 && \
   test "$rc_int1" -eq 0 && test "$rc_int2" -eq 0 && \
   test "$rc_mock3" -eq 0 && test "$rc_qym1" -eq 0 && test "$rc_qym2" -eq 0; then
  final=0
  touch "$out/ALL_REQUIRED_TARGETS_2X_PASS"
fi

export OUT="$out" RC_M2="$rc_m2" RC_M2A="$rc_m2a" RC_FA1="$rc_fa1" RC_FA2="$rc_fa2"
export RC_INT1="$rc_int1" RC_INT2="$rc_int2" RC_MOCK3="$rc_mock3"
export RC_QYM1="$rc_qym1" RC_QYM2="$rc_qym2" FINAL="$final"
python3 - <<'PY'
from pathlib import Path
import hashlib, json, os, re

d = Path(os.environ['OUT'])
pat = re.compile(r'\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)')
rows = {}
for p in sorted(d.glob('*-run*.log')):
    text = p.read_text(encoding='utf-8', errors='replace')
    matches = list(pat.finditer(text))
    exit_path = p.with_suffix('.exit')
    rows[p.stem] = {
        'exit_code': int(exit_path.read_text()) if exit_path.exists() else 999,
        'errors': len(matches),
        'first_line': int(matches[0].group(1)) if matches else 0,
        'first_col': int(matches[0].group(2)) if matches else 0,
    }
src = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
status = {
    'complete': os.environ['FINAL'] == '0' and (d / 'ALL_REQUIRED_TARGETS_2X_PASS').exists(),
    'fa_source_sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
    'summary_exit': {
        'Mock2': int(os.environ['RC_M2']),
        'Mock2_Advanced': int(os.environ['RC_M2A']),
        'FA_run1': int(os.environ['RC_FA1']),
        'FA_run2': int(os.environ['RC_FA2']),
        'Integrated_run1': int(os.environ['RC_INT1']),
        'Integrated_run2': int(os.environ['RC_INT2']),
        'Mock3_all_2x': int(os.environ['RC_MOCK3']),
        'QYM_run1': int(os.environ['RC_QYM1']),
        'QYM_run2': int(os.environ['RC_QYM2']),
    },
    'runs': rows,
}
(d / 'CURRENT.json').write_text(json.dumps(status, indent=2) + '\n', encoding='utf-8')
(d / 'CURRENT.txt').write_text(
    '\n'.join(f'{k}={v}' for k, v in status['summary_exit'].items()) +
    f"\ncomplete={status['complete']}\nfa_source_sha256={status['fa_source_sha256']}\n",
    encoding='utf-8')
print(json.dumps(status, indent=2))
PY

exit "$final"
