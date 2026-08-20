#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"; cd "$ROOT"
LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/m2a-direct-v5}"
CANDIDATE="${FOCUSED_CANDIDATE_MARKER:-.ci/focused/m2a_candidate_v5.json}"
REPORT_OUT="${FOCUSED_REPORT_OUT:-/tmp/m2a_direct_pass_v5.json}"
BUNDLE_OUT="${FOCUSED_BUNDLE_OUT:-/tmp/m2a-direct-v5-proof.tar.gz}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
MOCK2='PrimalitySheafVerification/Mock2.lean'
TARGET='PrimalitySheafVerification/Mock2_Advanced.lean'
mkdir -p "$LOGDIR" "$OUT"
test -f "$CANDIDATE"
git status --porcelain=v1 > "$LOGDIR/initial-status.txt"; test ! -s "$LOGDIR/initial-status.txt"

python3 - "$CANDIDATE" <<'PY' > "$LOGDIR/candidate-verification.txt"
from pathlib import Path
import hashlib,json,subprocess,sys
x=json.load(open(sys.argv[1])); assert x['status']=='PASS'
p=Path('PrimalitySheafVerification/Mock2_Advanced.lean')
sha=hashlib.sha256(p.read_bytes()).hexdigest(); blob=subprocess.check_output(['git','hash-object',str(p)],text=True).strip()
print('sha256='+sha); print('blob='+blob)
assert sha==x['source_sha256']; assert blob==x['source_blob']
sig=subprocess.check_output(['python3','scripts/focused_source_audit_20260807.py','signature',str(p)],text=True).strip()
assert sig==x['theorem_signature_sha256']
PY
python3 scripts/focused_source_audit_20260807.py audit "$MOCK2" "$TARGET" > "$LOGDIR/static-trust.json"
git diff --exit-code

LAST=0
compile(){
  local mod="$1" label="$2" log="$LOGDIR/$label.log"
  rm -f "$OUT/$mod.olean" "$OUT/$mod.ilean" "$OUT/$mod.olean.private"
  set +e
  lake env lean "PrimalitySheafVerification/$mod.lean" -o "$OUT/$mod.olean" -i "$OUT/$mod.ilean" > "$log" 2>&1
  LAST=$?; set -e; echo "$LAST" > "$LOGDIR/$label.exit"
  if [[ "$LAST" -ne 0 ]]; then
    { echo "label=$label"; echo "exit_code=$LAST"; echo "first_error=$(grep -n 'error:' "$log" | head -1 || true)"; echo "total_errors=$(grep -c 'error:' "$log" || true)"; echo "last_error=$(grep -n 'error:' "$log" | tail -1 || true)"; } > "$LOGDIR/first-failure.env"
    grep -n 'error:' "$log" | head -10 > "$LOGDIR/$label.first-ten-errors.txt" || true
    tail -200 "$log" > "$LOGDIR/$label.tail.txt" || true
    return "$LAST"
  fi
  test -s "$OUT/$mod.olean"; test -s "$OUT/$mod.ilean"
  test "$(grep -c 'error:' "$log" || true)" -eq 0
  ! grep -Eqi "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" "$log"
  ! grep -a -q sorryAx "$OUT/$mod.olean"
}

for pass in 1 2; do
  compile Mock2 "Mock2-pass${pass}"
  compile Mock2_Advanced "Mock2_Advanced-pass${pass}"
done

python3 scripts/generate_axiom_audit_for_module_20260807.py \
  --import-module PrimalitySheafVerification.Mock2_Advanced \
  --output /tmp/m2a_axiom_audit_v5.lean "$TARGET" > "$LOGDIR/axiom-generation.txt"
lake env lean /tmp/m2a_axiom_audit_v5.lean > "$LOGDIR/axiom-audit.log" 2>&1
python3 - "$LOGDIR/axiom-audit.log" <<'PY' > "$LOGDIR/axiom-summary.json"
import json,re,sys
text=open(sys.argv[1],errors='replace').read(); allowed={'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text
seen=set()
for m in re.finditer(r'depends on axioms:\s*\[(.*?)\]',text,re.S):
  seen.update(x.strip() for x in m.group(1).split(',') if x.strip())
bad=sorted(seen-allowed)
print(json.dumps({'observed_axioms':sorted(seen),'nonstandard_axioms':bad,'sorryAx':0},indent=2))
assert not bad
PY

git status --porcelain=v1 > "$LOGDIR/final-status.txt"; test ! -s "$LOGDIR/final-status.txt"
sha256sum "$MOCK2" "$TARGET" "$OUT/Mock2.olean" "$OUT/Mock2.ilean" "$OUT/Mock2_Advanced.olean" "$OUT/Mock2_Advanced.ilean" > "$LOGDIR/source-and-artifact-sha256.txt"
python3 - "$REPORT_OUT" "$CANDIDATE" <<'PY'
from pathlib import Path
import hashlib,json,os,subprocess,sys
out,candidate=sys.argv[1:]; c=json.load(open(candidate)); obj=Path('.lake/build/lib/lean/PrimalitySheafVerification'); p=Path('PrimalitySheafVerification/Mock2_Advanced.lean')
def sha(x): return hashlib.sha256(Path(x).read_bytes()).hexdigest()
axioms=json.load(open(os.environ.get('FOCUSED_LOGDIR','/tmp/focused-proof/m2a-direct-v5')+'/axiom-summary.json'))
run=None
if os.environ.get('GITHUB_RUN_ID'): run=f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
x={'phase':'Mock2_Advanced-direct-v5','status':'PASS','verified_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
'base_master_sha':subprocess.check_output(['git','ls-remote','origin','refs/heads/master'],text=True).split()[0],'workflow_run':run,
'source_blob':subprocess.check_output(['git','hash-object',str(p)],text=True).strip(),'source_sha256':sha(p),
'olean_sha256':sha(obj/'Mock2_Advanced.olean'),'ilean_sha256':sha(obj/'Mock2_Advanced.ilean'),
'clean_pass_1':0,'clean_pass_2':0,'error_count':0,'maximum_error_limit':False,'forbidden_tokens':0,
'sorryAx':0,'observed_axioms':axioms['observed_axioms'],'nonstandard_axioms':axioms['nonstandard_axioms'],
'runtime_source_repair':False,'source_mutation':False,'theorem_statements_changed':False,'assumptions_changed':False,
'mock2_regression':'PASS','candidate_provenance':c}
Path(out).write_text(json.dumps(x,indent=2)+'\n')
PY
cp "$REPORT_OUT" "$LOGDIR/m2a_direct_pass_v5.json"
tar -czf "$BUNDLE_OUT" -C "$(dirname "$LOGDIR")" "$(basename "$LOGDIR")"
echo M2A_DIRECT_V5_PASS
