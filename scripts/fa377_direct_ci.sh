#!/usr/bin/env bash
set -u

export PATH="${HOME}/.elan/bin:${PATH}"
D=build-logs/fa377c-precommit
BASELINE_SHA=07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4
CANDIDATE_SHA=c500aeef3f920bd8451f0c2926c9cc8e63d87f2b39bb24f982f338b7f33370a8
rm -rf "$D"
mkdir -p "$D" .lake/build/lib/lean/PrimalitySheafVerification

actual=$(sha256sum PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean | awk '{print $1}')
if test "$actual" != "$BASELINE_SHA"; then
  printf 'unexpected baseline sha256: %s\n' "$actual" > "$D/INFRA_FAILURE.txt"
  printf '1' > "$D/FINAL_EXIT"
  exit 0
fi

if ! python3 scripts/fa377_exact_after_31725.py > "$D/repair.txt" 2>&1; then
  printf 'repair script failed\n' > "$D/INFRA_FAILURE.txt"
  printf '1' > "$D/FINAL_EXIT"
  exit 0
fi
candidate=$(sha256sum PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean | awk '{print $1}')
if test "$candidate" != "$CANDIDATE_SHA"; then
  printf 'unexpected candidate sha256: %s\n' "$candidate" > "$D/INFRA_FAILURE.txt"
  printf '1' > "$D/FINAL_EXIT"
  exit 0
fi
cp PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean "$D/Mock2_FunctionalAnalysis-candidate.lean"

set -e
curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
export PATH="${HOME}/.elan/bin:${PATH}"
elan toolchain install "$(cat lean-toolchain)"
lean --version | tee "$D/lean-version.txt"
lake --version | tee "$D/lake-version.txt"
lake exe cache get | tee "$D/cache-get.log"
set +e

compile_one() {
  local stem=$1
  local max_errors=$2
  local src="PrimalitySheafVerification/${stem}.lean"
  local olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  rm -f "$olean" "$ilean"
  lake env lean -DmaxErrors="$max_errors" -DwarningAsError=false \
    -o "$olean" -i "$ilean" "$src" > "$D/${stem}.log" 2>&1
  local rc=$?
  printf '%s' "$rc" > "$D/${stem}.exit"
  if test "$rc" -eq 0 && test -s "$olean" && test -s "$ilean"; then
    return 0
  fi
  return 1
}

compile_one Mock2 400
rc_m2=$?
compile_one Mock2_Advanced 400
rc_m2a=$?
rc_fa=125
if test "$rc_m2" -eq 0 && test "$rc_m2a" -eq 0; then
  compile_one Mock2_FunctionalAnalysis 600
  rc_fa=$?
else
  echo 'FA compile blocked by prerequisite failure' > "$D/Mock2_FunctionalAnalysis.log"
  printf '%s' "$rc_fa" > "$D/Mock2_FunctionalAnalysis.exit"
fi

export RC_M2="$rc_m2" RC_M2A="$rc_m2a" RC_FA="$rc_fa"
export BASELINE_SHA CANDIDATE_SHA D
python3 - <<'PY'
from pathlib import Path
import hashlib, json, os, re

d = Path(os.environ['D'])
src = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
pat = re.compile(r'\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)')
rows = {}
for stem in ['Mock2', 'Mock2_Advanced', 'Mock2_FunctionalAnalysis']:
    p = d / f'{stem}.log'
    text = p.read_text(encoding='utf-8', errors='replace') if p.exists() else ''
    ms = list(pat.finditer(text))
    ep = d / f'{stem}.exit'
    rows[stem] = {
        'exit_code': int(ep.read_text()) if ep.exists() else 999,
        'error_headers': len(ms),
        'first_error_line': int(ms[0].group(1)) if ms else 0,
        'first_error_col': int(ms[0].group(2)) if ms else 0,
    }
fa = rows['Mock2_FunctionalAnalysis']
prereq_ok = (
    rows['Mock2']['exit_code'] == 0 and rows['Mock2']['error_headers'] == 0 and
    rows['Mock2_Advanced']['exit_code'] == 0 and rows['Mock2_Advanced']['error_headers'] == 0
)
actual_sha = hashlib.sha256(src.read_bytes()).hexdigest()
improved = fa['exit_code'] == 0 or fa['first_error_line'] > 31725
promoted = (
    actual_sha == os.environ['CANDIDATE_SHA'] and
    actual_sha != os.environ['BASELINE_SHA'] and prereq_ok and improved
)
status = {
    'complete': promoted,
    'baseline_source_sha256': os.environ['BASELINE_SHA'],
    'baseline_first_error_line': 31725,
    'candidate_source_sha256': actual_sha,
    'expected_candidate_source_sha256': os.environ['CANDIDATE_SHA'],
    'repairs_applied': 11,
    'results': rows,
    'metric_improved': improved,
    'promoted': promoted,
    'authority': 'actual direct Lean compile metric',
    'promotion_rule': 'FA exit 0, otherwise first_error_line strictly greater than 31725',
}
(d / 'CURRENT.json').write_text(json.dumps(status, indent=2) + '\n', encoding='utf-8')
(d / 'CURRENT.txt').write_text(
    '\n'.join(
        f"{k}: exit={v['exit_code']} errors={v['error_headers']} first={v['first_error_line']}:{v['first_error_col']}"
        for k, v in rows.items()
    ) + f"\npromoted={str(promoted).lower()}\n",
    encoding='utf-8')
log_lines = (d / 'Mock2_FunctionalAnalysis.log').read_text(encoding='utf-8', errors='replace').splitlines()
context = []
if fa['first_error_line']:
    key = f".lean:{fa['first_error_line']}:"
    for i, line in enumerate(log_lines):
        if key in line:
            context = log_lines[max(0, i - 5):min(len(log_lines), i + 60)]
            break
(d / 'FIRST_ERROR_CONTEXT.txt').write_text('\n'.join(context) + ('\n' if context else ''), encoding='utf-8')
(d / ('PROMOTED' if promoted else 'REGRESSION')).touch()
(d / 'FINAL_EXIT').write_text('0' if promoted else '1', encoding='utf-8')
print(json.dumps(status, indent=2))
PY
exit 0
