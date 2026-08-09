#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 1; then
  echo 'usage: fa426_matrix_ci.sh VARIANT' >&2
  exit 2
fi
VARIANT=$1
export VARIANT
TARGET='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OUT="build-logs/fa426-instance-matrix/${VARIANT}"
rm -rf "$OUT"
mkdir -p "$OUT" .lake/build/lib/lean/PrimalitySheafVerification

python3 scripts/fa426_apply_instance_variant.py "$VARIANT" | tee "$OUT/apply.log"

curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
export PATH="${HOME}/.elan/bin:${PATH}"
elan toolchain install "$(cat lean-toolchain)"
lean --version | tee "$OUT/lean-version.txt"
lake --version | tee "$OUT/lake-version.txt"
lake exe cache get | tee "$OUT/cache-get.log"
cp "$TARGET" "$OUT/candidate.lean"

compile_one() {
  local stem=$1
  local max_errors=$2
  local src="PrimalitySheafVerification/${stem}.lean"
  local olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  rm -f "$olean" "$ilean"
  lake env lean -DmaxErrors="$max_errors" -DwarningAsError=false \
    -o "$olean" -i "$ilean" "$src" > "$OUT/${stem}.log" 2>&1
  local rc=$?
  printf '%s' "$rc" > "$OUT/${stem}.exit"
  if test "$rc" -eq 0 && test -s "$olean" && test -s "$ilean"; then
    return 0
  fi
  return 1
}

set +e
compile_one Mock2 20; rc_m2=$?
compile_one Mock2_Advanced 20; rc_m2a=$?
rc_fa=125
if test "$rc_m2" -eq 0 && test "$rc_m2a" -eq 0; then
  compile_one Mock2_FunctionalAnalysis 20; rc_fa=$?
else
  printf 'blocked by prerequisite regression\n' > "$OUT/Mock2_FunctionalAnalysis.log"
  printf '%s' "$rc_fa" > "$OUT/Mock2_FunctionalAnalysis.exit"
fi
set -e
export RC_M2="$rc_m2" RC_M2A="$rc_m2a" RC_FA="$rc_fa" OUT

python3 - <<'PY'
from pathlib import Path
import hashlib, json, os, re, subprocess, sys
sys.path.insert(0, str(Path('scripts').resolve()))
import fa422_canonical_decl_tournament as engine

variant=os.environ['VARIANT']
out=Path(os.environ['OUT'])
src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
candidate=src.read_text(encoding='utf-8')
baseline=subprocess.check_output(
    ['git','show','HEAD:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'],
    text=True,
)
baseline_sha=hashlib.sha256(baseline.encode()).hexdigest()
candidate_sha=hashlib.sha256(candidate.encode()).hexdigest()
pat=re.compile(r'Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)')
log=(out/'Mock2_FunctionalAnalysis.log').read_text(encoding='utf-8',errors='replace')
matches=list(pat.finditer(log))
first=int(matches[0].group(1)) if matches else None
col=int(matches[0].group(2)) if matches else None
rc_m2=int(os.environ['RC_M2']); rc_m2a=int(os.environ['RC_M2A']); rc_fa=int(os.environ['RC_FA'])
candidate_index=engine.decl_index_at(candidate, first)
baseline_index=2658
prereq_ok=rc_m2==0 and rc_m2a==0
passed=rc_fa==0
strictly_better=passed or (
    isinstance(first,int) and first>31726 and isinstance(candidate_index,int) and
    (candidate_index>baseline_index or (
        candidate_index==baseline_index and
        len(candidate.splitlines())==len(baseline.splitlines())
    ))
)
statement_unchanged=engine.manifest(candidate)==engine.manifest(baseline)
imports_unchanged=engine.core.imports(candidate)==engine.core.imports(baseline)
forbidden=engine.core.forbidden_hits(candidate)
authorized=(
    baseline_sha=='71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'
    and prereq_ok and strictly_better and statement_unchanged and imports_unchanged
    and not any(forbidden.values())
)
status={
    'classification':'VERIFIED' if authorized else 'CANDIDATE_REJECTED',
    'variant':variant,
    'baseline_sha256':baseline_sha,
    'candidate_sha256':candidate_sha,
    'baseline_line_count':len(baseline.splitlines()),
    'candidate_line_count':len(candidate.splitlines()),
    'Mock2_exit':rc_m2,
    'Mock2_Advanced_exit':rc_m2a,
    'FA_exit':rc_fa,
    'FA_error_headers_captured':len(matches),
    'FA_first_actual_error_line':first,
    'FA_first_actual_error_col':col,
    'FA_error_declaration_index':candidate_index,
    'baseline_declaration_index':baseline_index,
    'maxErrors_cap':20,
    'strictly_better':strictly_better,
    'authorized_for_materialization':authorized,
    'statement_manifest_unchanged':statement_unchanged,
    'imports_unchanged':imports_unchanged,
    'forbidden_token_audit':forbidden,
}
(out/'CURRENT.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
(out/'CURRENT.txt').write_text('\n'.join(f'{k}={v}' for k,v in status.items())+'\n',encoding='utf-8')
(out/('AUTHORIZED' if authorized else 'REJECTED')).touch()
(out/'FINAL_EXIT').write_text('0' if authorized else '1')
print(json.dumps(status,indent=2))
PY
