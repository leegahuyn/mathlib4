#!/usr/bin/env bash
set -euo pipefail

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/diagnose-pass349-frontier'
PASS348_SHA='2c4376b7b6adaabe7917bbfbc327c622da252a585835461881a9e3ac336dc607'
EXPECTED_SHA256='2facdbe0afb09d0cd4771a517188591e7aca619832cd89f3ba30e35ec91e6609'
mkdir -p "${EVIDENCE}/source" "${EVIDENCE}/logs" "${OUTDIR}"

# Reconstruct the exact PASS 348 candidate. PASS 348 is expected to fail its
# own compile; that exit code is diagnostic and does not stop this next pass.
set +e
bash scripts/diagnose_pass348_frontier.sh \
  > "${EVIDENCE}/logs/reconstruct-pass348.log" 2>&1
reconstruct_rc=$?
set -e
before_sha="$(sha256sum "${FA}" | awk '{print $1}')"
printf 'reconstruct_exit=%s\npass348_sha256=%s\n' \
  "${reconstruct_rc}" "${before_sha}" > "${EVIDENCE}/provenance.txt"
test "${before_sha}" = "${PASS348_SHA}"

python3 scripts/fa349_frontier_repair.py \
  2>&1 | tee "${EVIDENCE}/logs/fa349-repair.log"
actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
printf 'expected_sha256=%s\nactual_sha256=%s\n' \
  "${EXPECTED_SHA256}" "${actual_sha}" | tee "${EVIDENCE}/candidate-sha256.txt"
test "${actual_sha}" = "${EXPECTED_SHA256}"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass349-frontier.lean"

rm -f "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.olean.private"
set +e
lake env lean -DmaxErrors=150 "${FA}" \
  -o "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  -i "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  > "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass349-frontier.log" 2>&1
code=$?
set -e
errors="$(grep -c 'error:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass349-frontier.log" || true)"
warnings="$(grep -c 'warning:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass349-frontier.log" || true)"
olean=false
ilean=false
[[ -s "${OUTDIR}/Mock2_FunctionalAnalysis.olean" ]] && olean=true
[[ -s "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" ]] && ilean=true
printf '%s\n' \
  "source_sha256=${actual_sha}" \
  "exit_code=${code}" \
  "error_header_count=${errors}" \
  "warning_count=${warnings}" \
  "olean_present=${olean}" \
  "ilean_present=${ilean}" \
  > "${EVIDENCE}/summary.txt"
{
  grep -n 'error:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass349-frontier.log" | head -360 || true
  echo '--- last errors ---'
  grep -n 'error:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass349-frontier.log" | tail -180 || true
  echo '--- log tail ---'
  tail -1800 "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass349-frontier.log" || true
} > "${EVIDENCE}/logs/failure-summary.txt"
exit "${code}"
