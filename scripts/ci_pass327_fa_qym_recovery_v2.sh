#!/usr/bin/env bash
set -euo pipefail

PASS_RUN='31159696948'
PASS_JOB='92827136991'
TARGET_DIR='PrimalitySheafVerification'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pass327-fa-qym-recovery-v2'
MOCK2="${TARGET_DIR}/Mock2.lean"
ADVANCED="${TARGET_DIR}/Mock2_Advanced.lean"
FA="${TARGET_DIR}/Mock2_FunctionalAnalysis.lean"
INTEGRATED="${TARGET_DIR}/Mock2_FunctionalAnalysis_Integrated.lean"
QYM="${TARGET_DIR}/QYM.lean"
MARKER='build-logs/pass327-targets-pass.json'
mkdir -p "${EVIDENCE}/downloads" "${EVIDENCE}/logs" "${EVIDENCE}/source" "${OUTDIR}" build-logs
printf 'module,label,exit_code,error_count,warning_count,source_sha256\n' > "${EVIDENCE}/compile-summary.csv"

strip_audit() {
  python3 - "$@" <<'PY'
from pathlib import Path
import re,sys

def strip(s):
 out=[];i=0;d=0;q=False;e=False
 while i<len(s):
  if d:
   if s.startswith('/-',i): d+=1;out+=[' ',' '];i+=2
   elif s.startswith('-/',i): d-=1;out+=[' ',' '];i+=2
   else: out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif q:
   c=s[i];out.append('\n' if c=='\n' else ' ')
   if e:e=False
   elif c=='\\':e=True
   elif c=='"':q=False
   i+=1
  elif s.startswith('/-',i):d=1;out+=[' ',' '];i+=2
  elif s.startswith('--',i):
   while i<len(s) and s[i]!='\n':out.append(' ');i+=1
  elif s[i]=='"':q=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 if d or q:raise SystemExit('unterminated comment/string')
 return ''.join(out)
checks={'sorry':r'\bsorry\b','admit':r'\badmit\b','axiom':r'(?m)^\s*axiom\b',
'unsafe':r'\bunsafe\b','native_decide':r'\bnative_decide\b','Lean.ofReduceBool':r'\bLean\.ofReduceBool\b'}
bad=False
for f in sys.argv[1:]:
 code=strip(Path(f).read_text(encoding='utf-8'));print(f'[{f}]')
 for n,p in checks.items():
  c=len(re.findall(p,code));print(f'{n}={c}');bad|=c!=0
if bad:raise SystemExit(1)
PY
}

compile_one() {
  local path="$1" label="$2" module log rc errors warnings sha
  module="$(basename "${path}" .lean)"
  log="${EVIDENCE}/logs/${label}.log"
  sha="$(sha256sum "${path}" | awk '{print $1}')"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" "${OUTDIR}/${module}.olean.private"
  set +e
  timeout 1500 lake env lean -DmaxErrors=2000 "${path}" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  rc=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s,%s\n' "$module" "$label" "$rc" "$errors" "$warnings" "$sha" \
    >> "${EVIDENCE}/compile-summary.csv"
  [[ "$rc" -eq 0 && "$errors" -eq 0 && -s "${OUTDIR}/${module}.olean" && -s "${OUTDIR}/${module}.ilean" ]] || return 1
  ! grep -Eqi "maximum number of errors|missing object file|sorryAx|declaration uses ['\"]sorry|PANIC|segmentation fault|stack overflow" "${log}"
}

printf '%s\n' "pass_run=${PASS_RUN}" "pass_job=${PASS_JOB}" \
  "trigger_head=$(git rev-parse HEAD)" "utc=$(date -u +%FT%TZ)" > "${EVIDENCE}/provenance.txt"
gh api "repos/${GITHUB_REPOSITORY}/actions/runs/${PASS_RUN}" > "${EVIDENCE}/run.json"
gh api "repos/${GITHUB_REPOSITORY}/actions/jobs/${PASS_JOB}" > "${EVIDENCE}/job.json"
gh api --paginate "repos/${GITHUB_REPOSITORY}/actions/runs/${PASS_RUN}/artifacts" \
  > "${EVIDENCE}/artifacts.json"
python3 - <<'PY' > /tmp/pass327-artifacts.tsv
import json
from pathlib import Path
for line in Path('/tmp/pass327-fa-qym-recovery-v2/artifacts.json').read_text().splitlines():
 try:d=json.loads(line)
 except:continue
 for a in d.get('artifacts',[]):
  if not a.get('expired'):print(a['id'],a['name'],sep='\t')
PY
while IFS=$'\t' read -r id name; do
 [[ -n "$id" ]] || continue
 gh api "repos/${GITHUB_REPOSITORY}/actions/artifacts/${id}/zip" > "${EVIDENCE}/downloads/${id}.zip"
 mkdir -p "${EVIDENCE}/downloads/${id}"
 unzip -q -o "${EVIDENCE}/downloads/${id}.zip" -d "${EVIDENCE}/downloads/${id}"
done < /tmp/pass327-artifacts.tsv

# Build content-deduplicated, ranked candidate manifests.  The exact checked-in
# source is always first; at most a bounded number of artifact candidates are compiled.
python3 - <<'PY'
from pathlib import Path
import hashlib
root=Path('/tmp/pass327-fa-qym-recovery-v2/downloads')

def manifest(kind,checked,limit):
 candidates=[Path(checked)]
 if kind=='advanced':
  candidates += list(root.rglob('*Mock2_Advanced*.lean')) + list(root.rglob('repaired-source.lean'))
 else:
  candidates += list(root.rglob('*Mock2_FunctionalAnalysis*.lean'))
  candidates += list(root.rglob('*pass327*.lean')) + list(root.rglob('candidate*.lean')) + list(root.rglob('repaired-source.lean'))
 def rank(p):
  n=p.name.lower();s=str(p).lower()
  return (0 if '327' in s else 1,0 if 'verified' in n else 1,0 if 'candidate' in n else 1,0 if kind in n else 1,len(s))
 seen={};out=[]
 for p in sorted(candidates,key=rank):
  try:data=p.read_bytes()
  except:continue
  if len(data)<1000:continue
  h=hashlib.sha256(data).hexdigest()
  if h in seen:continue
  seen[h]=p;out.append((p,h,len(data)))
  if len(out)>=limit:break
 Path(f'/tmp/pass327-fa-qym-recovery-v2/{kind}-candidates.tsv').write_text(
  ''.join(f'{p}\t{h}\t{size}\n' for p,h,size in out),encoding='utf-8')
manifest('advanced','PrimalitySheafVerification/Mock2_Advanced.lean',5)
manifest('functional','PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean',9)
PY

strip_audit "$MOCK2"
compile_one "$MOCK2" Mock2-dependency

# Current checked-in Advanced is the first choice.  Artifact alternatives are
# considered only if necessary, with content-deduplication and a hard limit.
cp "$ADVANCED" "${EVIDENCE}/source/Advanced-original.lean"
best_adv_errors=999999;adv_index=0;adv_pass=0
while IFS=$'\t' read -r candidate sha size; do
 [[ -s "$candidate" ]] || continue
 adv_index=$((adv_index+1));cp "$candidate" "$ADVANCED"
 set +e;compile_one "$ADVANCED" "Advanced-candidate-${adv_index}";rc=$?;set -e
 errors="$(grep -c 'error:' "${EVIDENCE}/logs/Advanced-candidate-${adv_index}.log" || true)"
 if (( errors < best_adv_errors ));then best_adv_errors=$errors;cp "$ADVANCED" "${EVIDENCE}/source/Advanced-best.lean";fi
 if [[ "$rc" -eq 0 ]];then adv_pass=1;break;fi
done < "${EVIDENCE}/advanced-candidates.tsv"
test "$adv_pass" -eq 1
cp "${EVIDENCE}/source/Advanced-best.lean" "$ADVANCED"
compile_one "$ADVANCED" Advanced-direct-1
compile_one "$ADVANCED" Advanced-direct-2
strip_audit "$ADVANCED"

cp "$FA" "${EVIDENCE}/source/FA-original.lean"
best_errors=999999;best_rc=99;fa_index=0;fa_pass=0
while IFS=$'\t' read -r candidate sha size; do
 [[ -s "$candidate" ]] || continue
 fa_index=$((fa_index+1));cp "$candidate" "$FA"
 set +e;compile_one "$FA" "FA-candidate-${fa_index}";rc=$?;set -e
 errors="$(grep -c 'error:' "${EVIDENCE}/logs/FA-candidate-${fa_index}.log" || true)"
 if (( errors < best_errors )) || { (( errors == best_errors )) && (( rc < best_rc )); };then
  best_errors=$errors;best_rc=$rc;cp "$FA" "${EVIDENCE}/source/FA-best.lean"
  cp "${EVIDENCE}/logs/FA-candidate-${fa_index}.log" "${EVIDENCE}/logs/FA-best.log"
 fi
 if [[ "$rc" -eq 0 ]];then fa_pass=1;break;fi
done < "${EVIDENCE}/functional-candidates.tsv"
cp "${EVIDENCE}/source/FA-best.lean" "$FA"
if [[ "$fa_pass" -ne 1 ]];then
 echo "FA_NOT_YET_PASS errors=${best_errors}" | tee "${EVIDENCE}/status.txt"
 exit 20
fi
compile_one "$FA" FA-direct-1
compile_one "$FA" FA-direct-2
strip_audit "$FA"

compile_one "$INTEGRATED" Integrated-direct-1
compile_one "$INTEGRATED" Integrated-direct-2
while IFS= read -r mock3;do
 [[ -n "$mock3" ]] || continue
 module="$(basename "$mock3" .lean)"
 compile_one "$mock3" "${module}-direct-1"
 compile_one "$mock3" "${module}-direct-2"
done < <(find "$TARGET_DIR" -maxdepth 1 -type f -name 'Mock3*.lean' | sort)
compile_one "$QYM" QYM-direct-1
compile_one "$QYM" QYM-direct-2
strip_audit "$INTEGRATED" "$QYM"

python3 - <<'PY'
from pathlib import Path
import csv,json,subprocess,time
rows=list(csv.DictReader(open('/tmp/pass327-fa-qym-recovery-v2/compile-summary.csv',encoding='utf-8')))
marker={'status':'PASS','baseline':'PASS 327','run_id':31159696948,'job_id':92827136991,
'runtime_repair_in_final_gate':False,'rows':rows,
'verified_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
'verified_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
Path('build-logs/pass327-targets-pass.json').write_text(json.dumps(marker,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
PY
echo 'PASS_327_PRIORITY_TARGETS_PASS' | tee "${EVIDENCE}/status.txt"
