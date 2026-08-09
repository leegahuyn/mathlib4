#!/usr/bin/env bash
set -euo pipefail

ACTIVE_BRANCH='fix/fa425-instance-transport-controller-20260810'
VERIFIED_START_SHA='71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'
VERIFIED_START_FIRST=31726
VERIFIED_LINE_COUNT=60453
TARGET='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
SRC_EVIDENCE='build-logs/fa422-canonical-decl'
OUT='build-logs/fa425-instance-transport'

mkdir -p "$OUT/diagnostics"
rm -f "$OUT/FINAL_EXIT" "$OUT/PROMOTED" "$OUT/COMPLETE" "$OUT/NO_IMPROVEMENT"

actual=$(sha256sum "$TARGET" | awk '{print $1}')
lines=$(wc -l < "$TARGET" | tr -d ' ')
test "$actual" = "$VERIFIED_START_SHA"
test "$lines" = "$VERIFIED_LINE_COUNT"
test -s build-logs/fa423-proof-hunk/CURRENT.json

python3 - <<'PY'
import hashlib, json
from pathlib import Path
s=json.loads(Path('build-logs/fa423-proof-hunk/CURRENT.json').read_text())
src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
actual=hashlib.sha256(src.read_bytes()).hexdigest()
m=s['final_fa_metric']
assert actual == '71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'
assert m['source_sha256'] == actual
assert m['exit_code'] == 1
assert m['first_line'] == 31726 and m['first_col'] == 2
for name in ('Mock2','Mock2_Advanced'):
    assert s['prerequisites'][name]['exit_code'] == 0
    assert s['prerequisites'][name]['errors'] == 0
assert not any(s['forbidden_token_audit'].values())
PY

curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
export PATH="${HOME}/.elan/bin:${PATH}"
elan toolchain install "$(cat lean-toolchain)"
lean --version | tee "$OUT/lean-version.txt"
lake --version | tee "$OUT/lake-version.txt"
lake exe cache get | tee "$OUT/cache-get.log"

cat > /tmp/fa425-checks.lean <<'EOF'
import Mathlib.Analysis.Complex.Basic
#check @HasDerivAt
#check AddCommGroup.ext
#check Complex.addCommGroup
#check Complex.instNormedAddCommGroup
EOF
set +e
lake env lean -DwarningAsError=false /tmp/fa425-checks.lean > "$OUT/diagnostics/checks.log" 2>&1
printf '%s' "$?" > "$OUT/diagnostics/checks.exit"

write_probe() {
  local name=$1
  local proof=$2
  cat > "/tmp/fa425-${name}.lean" <<EOF
import Mathlib.Analysis.Complex.Basic
example : Complex.instNormedAddCommGroup.toAddCommGroup =
    Complex.addCommGroup := by
  ${proof}
EOF
  lake env lean -DmaxErrors=20 -DwarningAsError=false \
    "/tmp/fa425-${name}.lean" > "$OUT/diagnostics/${name}.log" 2>&1
  printf '%s' "$?" > "$OUT/diagnostics/${name}.exit"
}
write_probe rfl 'rfl'
write_probe ext 'ext <;> rfl'
write_probe structure_ext 'apply AddCommGroup.ext <;> rfl'
write_probe reducible 'with_reducible_and_instances rfl'
set -e

before=$(sha256sum "$TARGET" | awk '{print $1}')
before_lines=$(wc -l < "$TARGET" | tr -d ' ')
export FA422_MAX_FRONTIERS=6
export FA422_MAX_CANDIDATES=140
export FA422_DIRECT_FALLBACK=24
set +e
python3 scripts/fa425_instance_transport_tournament.py > "$OUT/repair.log" 2>&1
solver_rc=$?
set -e
cat "$OUT/repair.log"
after=$(sha256sum "$TARGET" | awk '{print $1}')
after_lines=$(wc -l < "$TARGET" | tr -d ' ')

test -s "$SRC_EVIDENCE/CURRENT.json"
test -s "$SRC_EVIDENCE/CURRENT.txt"
cp "$SRC_EVIDENCE/CURRENT.json" "$OUT/CURRENT.json"
cp "$SRC_EVIDENCE/CURRENT.txt" "$OUT/CURRENT.txt"
test ! -f "$SRC_EVIDENCE/FIRST_ERROR_CONTEXT.txt" || \
  cp "$SRC_EVIDENCE/FIRST_ERROR_CONTEXT.txt" "$OUT/FIRST_ERROR_CONTEXT.txt"
find "$SRC_EVIDENCE" -maxdepth 1 -type f -name 'frontier-*-PROMOTED.txt' \
  -exec cp {} "$OUT/" \;
test ! -f "$SRC_EVIDENCE/ALL_REQUIRED_TARGETS_2X_PASS" || \
  cp "$SRC_EVIDENCE/ALL_REQUIRED_TARGETS_2X_PASS" "$OUT/ALL_REQUIRED_TARGETS_2X_PASS"
printf '%s\n' "$before" > "$OUT/before-source-sha256.txt"
printf '%s\n' "$after" > "$OUT/after-source-sha256.txt"
printf '%s\n' "$before_lines" > "$OUT/before-line-count.txt"
printf '%s\n' "$after_lines" > "$OUT/after-line-count.txt"
printf '%s\n' "$solver_rc" > "$OUT/solver-exit.txt"

export ACTIVE_BRANCH VERIFIED_START_SHA VERIFIED_START_FIRST VERIFIED_LINE_COUNT OUT
python3 - <<'PY'
from pathlib import Path
import hashlib, json, os

out=Path(os.environ['OUT'])
s=json.loads((out/'CURRENT.json').read_text())
src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
actual=hashlib.sha256(src.read_bytes()).hexdigest()
line_count=len(src.read_text(encoding='utf-8').splitlines())
m=s['final_fa_metric']
complete=bool(s['complete'])
start=os.environ['VERIFIED_START_SHA']
changed=actual != start

if s.get('starting_sha256') != start:
    raise SystemExit(f"unexpected tournament starting SHA: {s.get('starting_sha256')}")
if m.get('source_sha256') != actual:
    raise SystemExit('source/evidence SHA mismatch')
if changed and not s.get('any_promotion'):
    raise SystemExit('source changed without direct-CLI promotion')
if not complete:
    first=m.get('first_line')
    if not isinstance(first,int) or first < int(os.environ['VERIFIED_START_FIRST']):
        raise SystemExit(f'direct CLI regression: {first}')
if any(s['forbidden_token_audit'].values()):
    raise SystemExit('forbidden-token audit failed')
if s['statement_policy'] != 'declaration header manifest unchanged; only proof bodies may vary':
    raise SystemExit('statement/header policy missing')
for name in ('Mock2','Mock2_Advanced'):
    p=s['prerequisites'][name]
    if p['exit_code'] != 0 or p['errors'] != 0:
        raise SystemExit(f'{name} prerequisite regression')

diag={}
for p in sorted((out/'diagnostics').glob('*.exit')):
    diag[p.stem]=int(p.read_text())
summary={
    'classification':'VERIFIED',
    'branch':os.environ['ACTIVE_BRANCH'],
    'starting_source_sha256':s['starting_sha256'],
    'final_source_sha256':actual,
    'line_count':line_count,
    'source_changed':changed,
    'any_promotion':bool(s.get('any_promotion')),
    'complete':complete,
    'Mock2':s['prerequisites']['Mock2'],
    'Mock2_Advanced':s['prerequisites']['Mock2_Advanced'],
    'FA_exit':m['exit_code'],
    'FA_error_headers_captured':m['errors'],
    'FA_first_actual_error_line':m.get('first_line'),
    'FA_first_actual_error_col':m.get('first_col'),
    'FA_first_message':m.get('first_message'),
    'FA_error_declaration_index':s.get('final_error_decl_index'),
    'maxErrors_cap_for_authoritative_replay':500,
    'diagnostic_exit_codes':diag,
    'forbidden_token_audit':s['forbidden_token_audit'],
    'statement_policy':s['statement_policy'],
    'promotion_policy':s['promotion_policy'],
    'downstream_failure':s.get('downstream_failure'),
}
(out/'VERIFIED_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
(out/'VERIFIED_SUMMARY.txt').write_text(
    '\n'.join(f'{k}={v}' for k,v in summary.items())+'\n',encoding='utf-8')
if complete:
    (out/'COMPLETE').touch()
    (out/'FINAL_EXIT').write_text('0')
elif changed:
    (out/'PROMOTED').touch()
    (out/'FINAL_EXIT').write_text('1')
else:
    (out/'NO_IMPROVEMENT').touch()
    (out/'FINAL_EXIT').write_text('1')
print(json.dumps(summary,indent=2))
PY
