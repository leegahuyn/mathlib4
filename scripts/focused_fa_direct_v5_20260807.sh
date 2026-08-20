#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"; cd "$ROOT"
LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/fa-direct-v5}"
M2A_PASS="${FOCUSED_M2A_PASS_MARKER:-.ci/focused/m2a_direct_pass_v5.json}"
CANDIDATE="${FOCUSED_CANDIDATE_MARKER:-.ci/focused/fa_candidate_v5.json}"
REPORT_OUT="${FOCUSED_REPORT_OUT:-/tmp/fa_direct_pass_v5.json}"
BUNDLE_OUT="${FOCUSED_BUNDLE_OUT:-/tmp/fa-direct-v5-proof.tar.gz}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
M2A='PrimalitySheafVerification/Mock2_Advanced.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
mkdir -p "$LOGDIR" "$OUT"
test -f "$M2A_PASS"; test -f "$CANDIDATE"
git status --porcelain=v1 > "$LOGDIR/initial-status.txt"; test ! -s "$LOGDIR/initial-status.txt"

python3 - "$M2A_PASS" "$CANDIDATE" <<'PY' > "$LOGDIR/marker-verification.txt"
from pathlib import Path
import hashlib,json,subprocess,sys
m=json.load(open(sys.argv[1])); c=json.load(open(sys.argv[2])); assert m['status']=='PASS' and c['status']=='PASS'
checks=[('PrimalitySheafVerification/Mock2_Advanced.lean',m['source_sha256'],m['source_blob']),('PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean',c['integrated_source_sha256'],c['integrated_source_blob']),('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean',c['compatibility_source_sha256'],c['compatibility_source_blob'])]
for raw,sha0,blob0 in checks:
 p=Path(raw); sha=hashlib.sha256(p.read_bytes()).hexdigest(); blob=subprocess.check_output(['git','hash-object',str(p)],text=True).strip(); print(raw,sha,blob); assert sha==sha0 and blob==blob0
sig=subprocess.check_output(['python3','scripts/focused_source_audit_20260807.py','signature','PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'],text=True).strip(); assert sig==c['theorem_signature_sha256']
PY
python3 scripts/focused_source_audit_20260807.py audit "$M2A" "$INTEGRATED" "$FA" > "$LOGDIR/static-trust.json"
grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "$FA"
test "$(wc -l < "$INTEGRATED")" -gt 500
git diff --exit-code

LAST=0
compile(){
 local mod="$1" label="$2" log="$LOGDIR/$label.log"
 rm -f "$OUT/$mod.olean" "$OUT/$mod.ilean" "$OUT/$mod.olean.private"
 set +e; lake env lean "PrimalitySheafVerification/$mod.lean" -o "$OUT/$mod.olean" -i "$OUT/$mod.ilean" > "$log" 2>&1; LAST=$?; set -e
 echo "$LAST" > "$LOGDIR/$label.exit"
 if [[ "$LAST" -ne 0 ]]; then
   { echo "label=$label"; echo "exit_code=$LAST"; echo "first_error=$(grep -n 'error:' "$log" | head -1 || true)"; echo "total_errors=$(grep -c 'error:' "$log" || true)"; echo "last_error=$(grep -n 'error:' "$log" | tail -1 || true)"; } > "$LOGDIR/first-failure.env"
   grep -n 'error:' "$log" | head -10 > "$LOGDIR/$label.first-ten-errors.txt" || true; tail -200 "$log" > "$LOGDIR/$label.tail.txt" || true; return "$LAST"
 fi
 test -s "$OUT/$mod.olean"; test -s "$OUT/$mod.ilean"; test "$(grep -c 'error:' "$log" || true)" -eq 0
 ! grep -Eqi "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" "$log"
 ! grep -a -q sorryAx "$OUT/$mod.olean"
}
for pass in 1 2; do
 for mod in Mock2 Mock2_Advanced Mock2_FunctionalAnalysis_Integrated Mock2_FunctionalAnalysis; do compile "$mod" "$mod-pass$pass"; done
done

python3 scripts/generate_axiom_audit_for_module_20260807.py \
 --import-module PrimalitySheafVerification.Mock2_FunctionalAnalysis \
 --output /tmp/fa_axiom_audit_v5.lean "$INTEGRATED" > "$LOGDIR/axiom-generation.txt"
lake env lean /tmp/fa_axiom_audit_v5.lean > "$LOGDIR/axiom-audit.log" 2>&1
python3 - "$LOGDIR/axiom-audit.log" <<'PY' > "$LOGDIR/axiom-summary.json"
import json,re,sys
text=open(sys.argv[1],errors='replace').read(); allowed={'propext','Classical.choice','Quot.sound'}; assert 'sorryAx' not in text
seen=set()
for m in re.finditer(r'depends on axioms:\s*\[(.*?)\]',text,re.S): seen.update(x.strip() for x in m.group(1).split(',') if x.strip())
bad=sorted(seen-allowed); print(json.dumps({'observed_axioms':sorted(seen),'nonstandard_axioms':bad,'sorryAx':0},indent=2)); assert not bad
PY

git status --porcelain=v1 > "$LOGDIR/final-status.txt"; test ! -s "$LOGDIR/final-status.txt"
sha256sum PrimalitySheafVerification/Mock2.lean "$M2A" "$INTEGRATED" "$FA" \
 "$OUT/Mock2.olean" "$OUT/Mock2.ilean" "$OUT/Mock2_Advanced.olean" "$OUT/Mock2_Advanced.ilean" \
 "$OUT/Mock2_FunctionalAnalysis_Integrated.olean" "$OUT/Mock2_FunctionalAnalysis_Integrated.ilean" \
 "$OUT/Mock2_FunctionalAnalysis.olean" "$OUT/Mock2_FunctionalAnalysis.ilean" > "$LOGDIR/source-and-artifact-sha256.txt"
python3 - "$REPORT_OUT" "$CANDIDATE" <<'PY'
from pathlib import Path
import hashlib,json,os,subprocess,sys
out,cand=sys.argv[1:]; c=json.load(open(cand)); obj=Path('.lake/build/lib/lean/PrimalitySheafVerification'); logdir=Path(os.environ.get('FOCUSED_LOGDIR','/tmp/focused-proof/fa-direct-v5'))
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(p): return subprocess.check_output(['git','hash-object',str(p)],text=True).strip()
axioms=json.loads((logdir/'axiom-summary.json').read_text()); integ=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'); fa=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
run=f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}" if os.environ.get('GITHUB_RUN_ID') else None
x={'phase':'FunctionalAnalysis-direct-v5','status':'PASS','verified_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'base_master_sha':subprocess.check_output(['git','ls-remote','origin','refs/heads/master'],text=True).split()[0],'workflow_run':run,
'integrated_source_blob':blob(integ),'integrated_source_sha256':sha(integ),'compatibility_source_blob':blob(fa),'compatibility_source_sha256':sha(fa),
'integrated_olean_sha256':sha(obj/'Mock2_FunctionalAnalysis_Integrated.olean'),'integrated_ilean_sha256':sha(obj/'Mock2_FunctionalAnalysis_Integrated.ilean'),
'compatibility_olean_sha256':sha(obj/'Mock2_FunctionalAnalysis.olean'),'compatibility_ilean_sha256':sha(obj/'Mock2_FunctionalAnalysis.ilean'),
'clean_pass_1':0,'clean_pass_2':0,'error_count':0,'missing_project_object_files':0,'maximum_error_limit':False,'forbidden_tokens':0,'sorryAx':0,
'observed_axioms':axioms['observed_axioms'],'nonstandard_axioms':axioms['nonstandard_axioms'],'runtime_source_repair':False,'source_mutation':False,
'theorem_statements_changed':False,'assumptions_changed':False,'m2a_regression':'PASS','mock2_regression':'PASS',
'integrated_boundary':'substantive full source implementation with historical compatibility entry','candidate_provenance':c}
Path(out).write_text(json.dumps(x,indent=2)+'\n')
PY
cp "$REPORT_OUT" "$LOGDIR/fa_direct_pass_v5.json"; tar -czf "$BUNDLE_OUT" -C "$(dirname "$LOGDIR")" "$(basename "$LOGDIR")"
echo FA_DIRECT_V5_PASS
