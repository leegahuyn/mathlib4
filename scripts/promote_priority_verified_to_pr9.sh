#!/usr/bin/env bash
set -euo pipefail

status_json=${1:?usage: promote_priority_verified_to_pr9.sh STATUS_JSON MARKER}
marker=${2:?usage: promote_priority_verified_to_pr9.sh STATUS_JSON MARKER}
test -f "$status_json"
test -f "$marker"
grep -qx 'SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS' "$marker"
export PATH="${HOME}/.elan/bin:${PATH}"

git fetch origin ci/fa319-isolated-20260807
remote_sha=$(git rev-parse FETCH_HEAD)
tmp=$(mktemp -d)
cleanup() {
  cd "$GITHUB_WORKSPACE" 2>/dev/null || true
  git worktree remove "$tmp" --force 2>/dev/null || true
}
trap cleanup EXIT
git worktree add --detach "$tmp" "$remote_sha"

for f in \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \
  PrimalitySheafVerification/QYM.lean; do
  cp "$f" "$tmp/$f"
done
while IFS= read -r f; do
  cp "$f" "$tmp/$f"
done < <(find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' | sort)

rm -rf "$tmp/.lake"
ln -s "$GITHUB_WORKSPACE/.lake" "$tmp/.lake"
mkdir -p "$tmp/build-logs/pr9-promoted-2x/logs"
cd "$tmp"

python3 - <<'PY'
from pathlib import Path
import json, re
root=Path('PrimalitySheafVerification')
targets=[root/'Mock2_FunctionalAnalysis.lean',root/'Mock2_FunctionalAnalysis_Integrated.lean',*sorted(root.glob('Mock3*.lean')),root/'QYM.lean']
def strip(text):
    out=[]; i=0; depth=0; string=False; escape=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; out+=[' ',' ']; i+=2; continue
            if text.startswith('-/',i): depth-=1; out+=[' ',' ']; i+=2; continue
            out.append('\n' if text[i]=='\n' else ' '); i+=1; continue
        if string:
            c=text[i]; out.append('\n' if c=='\n' else ' ')
            if escape: escape=False
            elif c=='\\': escape=True
            elif c=='"': string=False
            i+=1; continue
        if text.startswith('/-',i): depth=1; out+=[' ',' ']; i+=2; continue
        if text.startswith('--',i):
            while i<len(text) and text[i]!='\n': out.append(' '); i+=1
            continue
        if text[i]=='"': string=True; out.append(' '); i+=1; continue
        out.append(text[i]); i+=1
    return ''.join(out)
pats={
 'sorry':re.compile(r'\bsorry\b'),'admit':re.compile(r'\badmit\b'),
 'global_axiom':re.compile(r'(?m)^\s*(?:public\s+)?axiom\b'),
 'unsafe':re.compile(r'(?m)^\s*unsafe\b'),
 'native_decide':re.compile(r'\bnative_decide\b'),
 'Lean.ofReduceBool':re.compile(r'\bLean\.ofReduceBool\b')}
report={}; bad=False
for path in targets:
    if not path.exists(): continue
    clean=strip(path.read_text(encoding='utf-8'))
    counts={k:len(p.findall(clean)) for k,p in pats.items()}
    report[str(path)]=counts; bad |= any(counts.values())
Path('build-logs/pr9-promoted-2x/forbidden-audit.json').write_text(json.dumps(report,indent=2))
if bad: raise SystemExit(f'forbidden proof escape: {report}')
PY

for stem in Mock2 Mock2_Advanced; do
  rm -f ".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean" \
        ".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  lake env lean -DmaxErrors=200 "PrimalitySheafVerification/${stem}.lean" \
    > "build-logs/pr9-promoted-2x/logs/${stem}-prerequisite.log" 2>&1
  test -s ".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  test -s ".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
done

mapfile -t modules < <(
  printf '%s\n' Mock2_FunctionalAnalysis Mock2_FunctionalAnalysis_Integrated
  find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' \
    -printf '%f\n' | sed 's/\.lean$//' | sort
  printf '%s\n' QYM
)
printf '%s\n' "${modules[@]}" > build-logs/pr9-promoted-2x/module-order.txt
: > build-logs/pr9-promoted-2x/results.tsv
for pass in 1 2; do
  for stem in "${modules[@]}"; do
    rm -f ".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean" \
          ".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
    set +e
    lake env lean -DmaxErrors=250 "PrimalitySheafVerification/${stem}.lean" \
      > "build-logs/pr9-promoted-2x/logs/${stem}-pass${pass}.log" 2>&1
    rc=$?
    set -e
    errors=$(grep -c 'error:' "build-logs/pr9-promoted-2x/logs/${stem}-pass${pass}.log" || true)
    warnings=$(grep -c 'warning:' "build-logs/pr9-promoted-2x/logs/${stem}-pass${pass}.log" || true)
    olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
    ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
    artifacts=missing
    test -s "$olean" && test -s "$ilean" && artifacts=ok
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$pass" "$stem" "$rc" "$errors" "$warnings" "$artifacts" >> \
      build-logs/pr9-promoted-2x/results.tsv
    test "$rc" -eq 0
    test "$errors" -eq 0
    test "$artifacts" = ok
  done
done

cp "$GITHUB_WORKSPACE/$status_json" build-logs/PR9_FA_INTEGRATED_MOCK3_QYM_FINAL_2X_PASS.json
python3 - <<'PY'
from pathlib import Path
import hashlib,json,os
summary=json.loads(Path('build-logs/PR9_FA_INTEGRATED_MOCK3_QYM_FINAL_2X_PASS.json').read_text())
rows=[]
for line in Path('build-logs/pr9-promoted-2x/results.tsv').read_text().splitlines():
    p,stem,rc,errors,warnings,artifacts=line.split('\t')
    rows.append({'pass':int(p),'module':stem,'exit_code':int(rc),'errors':int(errors),'warnings':int(warnings),'artifacts':artifacts})
summary['status']='SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS'
summary['pr9_base_head_before_promotion']=os.environ.get('remote_sha','')
summary['workflow_run_id']=os.environ.get('GITHUB_RUN_ID','')
summary['pr9_context_results']=rows
summary['pr9_context_forbidden_audit']=json.loads(Path('build-logs/pr9-promoted-2x/forbidden-audit.json').read_text())
summary['pr9_context_sources']={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'),Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'),*sorted(Path('PrimalitySheafVerification').glob('Mock3*.lean')),Path('PrimalitySheafVerification/QYM.lean')]}
text=json.dumps(summary,indent=2)
Path('build-logs/PR9_FA_INTEGRATED_MOCK3_QYM_FINAL_2X_PASS.json').write_text(text)
Path('build-logs/PR9_PRIORITY_FINAL_2X_VERIFIED.json').write_text(text)
PY

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \
  PrimalitySheafVerification/QYM.lean \
  build-logs/PR9_FA_INTEGRATED_MOCK3_QYM_FINAL_2X_PASS.json \
  build-logs/PR9_PRIORITY_FINAL_2X_VERIFIED.json \
  build-logs/pr9-promoted-2x/results.tsv \
  build-logs/pr9-promoted-2x/module-order.txt \
  build-logs/pr9-promoted-2x/forbidden-audit.json
find PrimalitySheafVerification -maxdepth 1 -type f -name 'Mock3*.lean' -print0 | xargs -0 -r git add
if ! git diff --cached --quiet; then
  git commit -m 'fix: promote independently verified FA Mock3 QYM sources'
  git push origin HEAD:ci/fa319-isolated-20260807
fi
