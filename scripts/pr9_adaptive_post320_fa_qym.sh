#!/usr/bin/env bash
set -uo pipefail

BRANCH='ci/fa319-isolated-20260807'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
MOCK2='PrimalitySheafVerification/Mock2.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/pr9-adaptive-post320'
mkdir -p "${EVIDENCE}/logs" "${EVIDENCE}/source" "${EVIDENCE}/artifacts" "${OUTDIR}"
printf 'stage,exit_code,error_count,warning_count,source_sha256\n' > "${EVIDENCE}/compile-summary.csv"

compile_one() {
  local path="$1" label="$2" module log rc errors warnings sha
  module="$(basename "${path}" .lean)"
  log="${EVIDENCE}/logs/${label}.log"
  sha="$(sha256sum "${path}" | awk '{print $1}')"
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean -DmaxErrors=500 "${path}" \
    -o "${OUTDIR}/${module}.olean" -i "${OUTDIR}/${module}.ilean" \
    >"${log}" 2>&1
  rc=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s\n' "${label}" "${rc}" "${errors}" "${warnings}" "${sha}" \
    | tee -a "${EVIDENCE}/compile-summary.csv"
  grep -n 'error:' "${log}" | head -120 > "${EVIDENCE}/logs/${label}.errors.txt" || true
  return "${rc}"
}

audit() {
  python3 - "$1" <<'PY'
from pathlib import Path
import re,sys
p=Path(sys.argv[1]);s=p.read_text(encoding='utf-8')
out=[];i=0;d=0;q=False;e=False
while i<len(s):
    if d:
        if s.startswith('/-',i):d+=1;out+=[' ',' '];i+=2
        elif s.startswith('-/',i):d-=1;out+=[' ',' '];i+=2
        else:out.append('\n' if s[i]=='\n' else ' ');i+=1
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
if d or q:raise SystemExit(1)
code=''.join(out)
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*axiom\b',r'\bunsafe\b',
            r'\bnative_decide\b',r'\bLean\.ofReduceBool\b']:
    if re.search(pat,code):raise SystemExit(f'forbidden token {pat} in {p}')
PY
}

# First attempt the exact PASS 320 path.  On a normal success this exits here.
set +e
bash scripts/pr9_apply_exact_pass320_resilient.sh
base_code=$?
set -e
if [[ "${base_code}" -eq 0 ]]; then
  echo 'exact PASS 320 path already completed' | tee "${EVIDENCE}/status.txt"
  exit 0
fi

candidate='/tmp/pr9-exact-pass320/source/Mock2_FunctionalAnalysis-pass320.lean'
if [[ -s "${candidate}" ]]; then
  cp "${candidate}" "${FA}"
fi
test -s "${FA}"
audit "${FA}"
cp "${FA}" "${EVIDENCE}/source/FA-start.lean"

applied=0
success=0
for round in $(seq 1 50); do
  current_sha="$(sha256sum "${FA}" | awk '{print $1}')"
  next_script="$(python3 - "${current_sha}" <<'PY'
import ast,glob,sys
current=sys.argv[1]
choices=[]
for name in glob.glob('scripts/apply_*_pass_functional_analysis_repairs.py'):
    try:
        tree=ast.parse(open(name,encoding='utf-8').read())
    except Exception:
        continue
    vals={}
    for node in tree.body:
        if isinstance(node,ast.Assign):
            for t in node.targets:
                if isinstance(t,ast.Name) and t.id in {'EXPECTED_INPUT_SHA256','EXPECTED_OUTPUT_SHA256'}:
                    try: vals[t.id]=ast.literal_eval(node.value)
                    except Exception: pass
        elif isinstance(node,ast.AnnAssign) and isinstance(node.target,ast.Name):
            if node.target.id in {'EXPECTED_INPUT_SHA256','EXPECTED_OUTPUT_SHA256'}:
                try: vals[node.target.id]=ast.literal_eval(node.value)
                except Exception: pass
    if vals.get('EXPECTED_INPUT_SHA256')==current and vals.get('EXPECTED_OUTPUT_SHA256')!=current:
        choices.append((name,vals.get('EXPECTED_OUTPUT_SHA256','')))
for name,out in sorted(choices):
    print(name)
    break
PY
)"

  if [[ -z "${next_script}" ]]; then
    echo "no hash-chained FunctionalAnalysis repair script for ${current_sha}" \
      | tee -a "${EVIDENCE}/repair-chain.txt"
    break
  fi

  echo "round=${round} input=${current_sha} script=${next_script}" \
    | tee -a "${EVIDENCE}/repair-chain.txt"
  python3 "${next_script}" 2>&1 | tee "${EVIDENCE}/logs/repair-${round}.log"
  applied=$((applied + 1))
  output_sha="$(sha256sum "${FA}" | awk '{print $1}')"
  echo "round=${round} output=${output_sha}" | tee -a "${EVIDENCE}/repair-chain.txt"
  audit "${FA}"

  set +e
  compile_one "${FA}" "FA-round-${round}"
  rc=$?
  set -e
  if [[ "${rc}" -eq 0 ]]; then
    success=1
    break
  fi
done

if [[ "${success}" -ne 1 ]]; then
  echo "adaptive repair exhausted; applied=${applied}" | tee "${EVIDENCE}/status.txt"
  exit 1
fi

# A successful candidate must pass the complete dependency chain twice.
audit "${MOCK2}"; audit "${ADVANCED}"; audit "${FA}"; audit "${INTEGRATED}"; audit "${QYM}"
compile_one "${MOCK2}" Mock2-final
compile_one "${ADVANCED}" Advanced-final
compile_one "${FA}" FA-final-pass1
compile_one "${FA}" FA-final-pass2
compile_one "${INTEGRATED}" Integrated-final-pass1
compile_one "${INTEGRATED}" Integrated-final-pass2
compile_one "${QYM}" QYM-final-pass1
compile_one "${QYM}" QYM-final-pass2

cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-verified.lean"
cp "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.olean" \
   "${OUTDIR}/Mock2_FunctionalAnalysis_Integrated.ilean" \
   "${OUTDIR}/QYM.olean" "${OUTDIR}/QYM.ilean" \
   "${EVIDENCE}/artifacts/"
sha256sum "${EVIDENCE}/artifacts/"* | tee "${EVIDENCE}/artifact-sha256.txt"

verified="${EVIDENCE}/source/Mock2_FunctionalAnalysis-verified.lean"
verified_sha="$(sha256sum "${verified}" | awk '{print $1}')"
git fetch --no-tags origin "+refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}"
git reset --hard "origin/${BRANCH}"
cp "${verified}" "${FA}"
test "$(sha256sum "${FA}" | awk '{print $1}')" = "${verified_sha}"
# Recheck directly at the newest head before push.
compile_one "${MOCK2}" Mock2-new-head
compile_one "${ADVANCED}" Advanced-new-head
compile_one "${FA}" FA-new-head-pass1
compile_one "${FA}" FA-new-head-pass2
compile_one "${INTEGRATED}" Integrated-new-head-pass1
compile_one "${INTEGRATED}" Integrated-new-head-pass2
compile_one "${QYM}" QYM-new-head-pass1
compile_one "${QYM}" QYM-new-head-pass2

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add "${FA}"
test "$(git diff --cached --name-only)" = "${FA}"
git diff --cached --check
if ! git diff --cached --quiet; then
  git commit -m 'fix: materialize hash-chained post-PASS320 FunctionalAnalysis source'
  git push origin "HEAD:${BRANCH}"
fi
echo "adaptive repair passed; applied=${applied} sha256=${verified_sha}" \
  | tee "${EVIDENCE}/status.txt"
