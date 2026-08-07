#!/usr/bin/env bash
set -euo pipefail

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE='/tmp/diagnose-pass342-frontier-v2'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
FA_BASELINE_COMMIT='402e2b7aa053b9c43d95f24e6146efbc5ccf714b'
EXPECTED_SHA256='c562c864be74e94e618ad3ad54dd7ee6442f81d17bc748754782718f4f7ca0e0'

mkdir -p "${EVIDENCE}/source" "${EVIDENCE}/logs" "${OUTDIR}"
cp "${ADVANCED}" /tmp/diagnose-pass342-current-advanced.lean

git -c fetch.writeCommitGraph=false fetch \
  --no-tags --no-recurse-submodules origin \
  "${ADVANCED_BASELINE_COMMIT}" "${FA_BASELINE_COMMIT}" \
  2>&1 | tee "${EVIDENCE}/logs/fetch-baselines.log"
git show "${FA_BASELINE_COMMIT}:${FA}" > "${FA}"
git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"

apply_repair() {
  local script="$1"
  echo "===== ${script} =====" | tee -a "${EVIDENCE}/logs/repair-chain.log"
  python3 "scripts/${script}" 2>&1 | tee -a "${EVIDENCE}/logs/repair-chain.log"
  printf '%s,%s\n' "${script}" "$(sha256sum "${FA}" | awk '{print $1}')" \
    >> "${EVIDENCE}/repair-source-sha256.csv"
}

: > "${EVIDENCE}/logs/repair-chain.log"
echo 'script,fa_source_sha256' > "${EVIDENCE}/repair-source-sha256.csv"
for script in \
  apply_two_hundred_eighty_ninth_pass_repairs.py \
  apply_two_hundred_ninetieth_pass_repairs.py \
  apply_two_hundred_ninety_first_pass_repairs.py \
  apply_two_hundred_ninety_second_pass_repairs.py \
  apply_two_hundred_ninety_third_pass_repairs.py \
  apply_two_hundred_ninety_fourth_pass_repairs.py \
  apply_two_hundred_ninety_fifth_pass_repairs.py \
  apply_two_hundred_ninety_seventh_pass_repairs.py \
  apply_two_hundred_ninety_eighth_pass_repairs.py \
  apply_two_hundred_ninety_ninth_pass_repairs.py \
  apply_three_hundredth_pass_repairs.py \
  apply_three_hundred_ninth_pass_repairs.py \
  apply_three_hundred_tenth_pass_repairs.py \
  apply_three_hundred_eleventh_pass_repairs.py \
  apply_three_hundred_twelfth_pass_repairs.py \
  apply_three_hundred_thirteenth_pass_repairs.py \
  apply_three_hundred_fourteenth_pass_repairs.py \
  apply_three_hundred_fifteenth_pass_repairs.py \
  fa316_driver.py \
  apply_three_hundred_seventeenth_pass_functional_analysis_repairs.py \
  apply_three_hundred_eighteenth_pass_functional_analysis_repairs.py \
  apply_three_hundred_nineteenth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twentieth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_first_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_second_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_third_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_fourth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_fifth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_sixth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_seventh_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py \
  apply_three_hundred_twenty_ninth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirtieth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_first_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_second_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_third_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_fourth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_fifth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_sixth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_seventh_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_eighth_pass_functional_analysis_repairs.py \
  apply_three_hundred_thirty_ninth_pass_functional_analysis_repairs.py \
  fa340_repair.py \
  fa341_repair.py \
  fa342_repair.py; do
  apply_repair "${script}"
done

cp /tmp/diagnose-pass342-current-advanced.lean "${ADVANCED}"
actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
printf 'expected_sha256=%s\nactual_sha256=%s\n' \
  "${EXPECTED_SHA256}" "${actual_sha}" | tee "${EVIDENCE}/candidate-sha256.txt"
test "${actual_sha}" = "${EXPECTED_SHA256}"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass342-frontier-v2.lean"

rm -f "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  "${OUTDIR}/Mock2_FunctionalAnalysis.olean.private"
set +e
lake env lean -DmaxErrors=25 "${FA}" \
  -o "${OUTDIR}/Mock2_FunctionalAnalysis.olean" \
  -i "${OUTDIR}/Mock2_FunctionalAnalysis.ilean" \
  > "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass342-frontier-v2.log" 2>&1
code=$?
set -e
errors="$(grep -c 'error:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass342-frontier-v2.log" || true)"
warnings="$(grep -c 'warning:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass342-frontier-v2.log" || true)"
printf '%s\n' \
  "source_sha256=${actual_sha}" \
  "exit_code=${code}" \
  "error_header_count=${errors}" \
  "warning_count=${warnings}" \
  > "${EVIDENCE}/summary.txt"
{
  grep -n 'error:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass342-frontier-v2.log" | head -160 || true
  echo '--- last errors ---'
  grep -n 'error:' "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass342-frontier-v2.log" | tail -80 || true
  echo '--- log tail ---'
  tail -1000 "${EVIDENCE}/logs/Mock2_FunctionalAnalysis-pass342-frontier-v2.log" || true
} > "${EVIDENCE}/logs/failure-summary.txt"
exit "${code}"
