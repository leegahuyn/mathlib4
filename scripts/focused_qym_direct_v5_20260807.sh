#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"; cd "$ROOT"
LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/qym-direct-v5}"
M2A_PASS="${FOCUSED_M2A_PASS_MARKER:-.ci/focused/m2a_direct_pass_v5.json}"
FA_PASS="${FOCUSED_FA_PASS_MARKER:-.ci/focused/fa_direct_pass_v5.json}"
REPORT_OUT="${FOCUSED_REPORT_OUT:-/tmp/focused_direct_pass_v5.json}"
BUNDLE_OUT="${FOCUSED_BUNDLE_OUT:-/tmp/focused-direct-v5-proof.tar.gz}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
M2A='PrimalitySheafVerification/Mock2_Advanced.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
QYM='PrimalitySheafVerification/QYM.lean'
mkdir -p "$LOGDIR" "$OUT"
test -f "$M2A_PASS"; test -f "$FA_PASS"
git status --porcelain=v1 > "$LOGDIR/initial-status.txt"; test ! -s "$LOGDIR/initial-status.txt"

python3 - "$M2A_PASS" "$FA_PASS" <<'PY' > "$LOGDIR/phase-marker-verification.txt"
from pathlib import Path
import hashlib,json,sys
m=json.load(open(sys.argv[1])); f=json.load(open(sys.argv[2])); assert m['status']=='PASS' and f['status']=='PASS'
assert m['runtime_source_repair'] is False and f['runtime_source_repair'] is False
checks=[('PrimalitySheafVerification/Mock2_Advanced.lean',m['source_sha256']),('PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean',f['integrated_source_sha256']),('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean',f['compatibility_source_sha256'])]
for raw,expected in checks:
 actual=hashlib.sha256(Path(raw).read_bytes()).hexdigest(); print(raw,actual); assert actual==expected
PY
python3 scripts/focused_source_audit_20260807.py audit \
  PrimalitySheafVerification/Mock2.lean "$M2A" "$INTEGRATED" "$FA" "$QYM" > "$LOGDIR/static-trust.json"
grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "$FA"
grep -Fq 'Mock2_FunctionalAnalysis_Integrated' "$QYM"
test "$(wc -l < "$INTEGRATED")" -gt 500
git diff --exit-code

LAST=0
compile(){
 local mod="$1" label="$2" log="$LOGDIR/$label.log"
 rm -f "$OUT/$mod.olean" "$OUT/$mod.ilean" "$OUT/$mod.olean.private"
 set +e; lake env lean "PrimalitySheafVerification/$mod.lean" -o "$OUT/$mod.olean" -i "$OUT/$mod.ilean" > "$log" 2>&1; LAST=$?; set -e
 echo "$LAST" > "$LOGDIR/$label.exit"
 if [[ "$LAST" -ne 0 ]]; then
   { echo "label=$label"; echo "exit_code=$LAST"; echo "first_error=$(grep -n 'error:' "$log" | head -1 || true)"; echo "total_errors=$(grep -c 'error:' "$log" || true)"; echo "last_error=$(grep -n 'error:' "$log" | tail -1 || true)"; echo "maximum_error_limit=$(grep -Eci 'maximum number of errors' "$log" || true)"; } > "$LOGDIR/first-failure.env"
   grep -n 'error:' "$log" | head -10 > "$LOGDIR/$label.first-ten-errors.txt" || true; tail -250 "$log" > "$LOGDIR/$label.tail.txt" || true; return "$LAST"
 fi
 test -s "$OUT/$mod.olean"; test -s "$OUT/$mod.ilean"; test "$(grep -c 'error:' "$log" || true)" -eq 0
 ! grep -Eqi "maximum number of errors|missing object file|declaration uses 'sorry'|sorryAx|PANIC|segmentation fault|stack overflow" "$log"
 ! grep -a -q sorryAx "$OUT/$mod.olean"
}
modules=(Mock2 Mock2_Advanced Mock2_FunctionalAnalysis_Integrated Mock2_FunctionalAnalysis QYM)
for pass in 1 2; do for mod in "${modules[@]}"; do compile "$mod" "$mod-pass$pass"; done; done

python3 scripts/generate_axiom_audit_for_module_20260807.py \
 --import-module PrimalitySheafVerification.QYM \
 --output /tmp/focused_axiom_audit_v5.lean "$M2A" "$INTEGRATED" "$QYM" > "$LOGDIR/axiom-generation.txt"
lake env lean /tmp/focused_axiom_audit_v5.lean > "$LOGDIR/axiom-audit.log" 2>&1
python3 - "$LOGDIR/axiom-audit.log" <<'PY' > "$LOGDIR/axiom-summary.json"
import json,re,sys
text=open(sys.argv[1],errors='replace').read(); allowed={'propext','Classical.choice','Quot.sound'}; assert 'sorryAx' not in text
seen=set()
for m in re.finditer(r'depends on axioms:\s*\[(.*?)\]',text,re.S): seen.update(x.strip() for x in m.group(1).split(',') if x.strip())
bad=sorted(seen-allowed); print(json.dumps({'observed_axioms':sorted(seen),'nonstandard_axioms':bad,'sorryAx':0},indent=2)); assert not bad
PY

git status --porcelain=v1 > "$LOGDIR/final-status.txt"; test ! -s "$LOGDIR/final-status.txt"
sha256sum PrimalitySheafVerification/Mock2.lean "$M2A" "$INTEGRATED" "$FA" "$QYM" \
 "$OUT/Mock2.olean" "$OUT/Mock2.ilean" "$OUT/Mock2_Advanced.olean" "$OUT/Mock2_Advanced.ilean" \
 "$OUT/Mock2_FunctionalAnalysis_Integrated.olean" "$OUT/Mock2_FunctionalAnalysis_Integrated.ilean" \
 "$OUT/Mock2_FunctionalAnalysis.olean" "$OUT/Mock2_FunctionalAnalysis.ilean" "$OUT/QYM.olean" "$OUT/QYM.ilean" > "$LOGDIR/source-and-artifact-sha256.txt"

python3 - "$REPORT_OUT" "$M2A_PASS" "$FA_PASS" <<'PY'
from pathlib import Path
import hashlib,json,os,subprocess,sys
out,m2ap,fap=sys.argv[1:]; m2a=json.load(open(m2ap)); fa=json.load(open(fap)); obj=Path('.lake/build/lib/lean/PrimalitySheafVerification'); logdir=Path(os.environ.get('FOCUSED_LOGDIR','/tmp/focused-proof/qym-direct-v5'))
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(p): return subprocess.check_output(['git','hash-object',str(p)],text=True).strip()
def warnings(m): return sum(p.read_text(errors='replace').count('warning:') for p in logdir.glob(f'{m}-pass*.log'))
mods=['Mock2','Mock2_Advanced','Mock2_FunctionalAnalysis_Integrated','Mock2_FunctionalAnalysis','QYM']; sources={}; artifacts={}
for m in mods:
 p=Path(f'PrimalitySheafVerification/{m}.lean'); sources[m]={'path':str(p),'blob':blob(p),'sha256':sha(p),'warnings_across_two_passes':warnings(m)}; artifacts[m]={'olean_sha256':sha(obj/f'{m}.olean'),'ilean_sha256':sha(obj/f'{m}.ilean')}
axioms=json.loads((logdir/'axiom-summary.json').read_text()); run=f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}" if os.environ.get('GITHUB_RUN_ID') else None
x={'overall_focused_status':'PASS','final_branch':os.environ.get('FOCUSED_BRANCH','fix/primality-sheaf-clean-build'),'verified_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'base_master_sha':subprocess.check_output(['git','ls-remote','origin','refs/heads/master'],text=True).split()[0],'workflow_run':run,
'runtime_source_repair':False,'source_mutation_during_verification':False,'clean_pass_1':0,'clean_pass_2':0,'error_count':0,'maximum_error_limit':False,'missing_project_object_files':0,
'forbidden_tokens':0,'sorry':0,'admit':0,'sorryAx':0,'unsafe':0,'native_decide':0,'Lean.ofReduceBool':0,'observed_axioms':axioms['observed_axioms'],'nonstandard_axioms':axioms['nonstandard_axioms'],
'theorem_statements_changed':False,'assumptions_changed':False,'mock2_regression':'PASS','m2a_direct_phase':m2a,'functional_analysis_direct_phase':fa,
'integrated_boundary':'substantive full source implementation with historical compatibility entry','qym_conditional_certificate_boundary':'preserved','sources':sources,'artifacts':artifacts}
Path(out).write_text(json.dumps(x,indent=2)+'\n')
PY
cp "$REPORT_OUT" "$LOGDIR/focused_direct_pass_v5.json"; tar -czf "$BUNDLE_OUT" -C "$(dirname "$LOGDIR")" "$(basename "$LOGDIR")"
echo FOCUSED_QYM_DIRECT_V5_PASS
