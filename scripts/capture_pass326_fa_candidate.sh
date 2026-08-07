#!/usr/bin/env bash
set -euo pipefail

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
EVIDENCE='/tmp/capture-pass326-fa-candidate'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
FA_BASELINE_COMMIT='402e2b7aa053b9c43d95f24e6146efbc5ccf714b'
EXPECTED_OUTPUT_SHA256='14350571cc83f03849f21d4f12ba09a97e3e8897a35bca8dd3e59103d9799468'

mkdir -p "${EVIDENCE}/source" "${EVIDENCE}/logs"
printf '%s\n' \
  "authority=PASS327" \
  "source_head=$(git rev-parse HEAD)" \
  "utc_started=$(date -u +%FT%TZ)" \
  > "${EVIDENCE}/snapshot.txt"

cp "${ADVANCED}" /tmp/capture-pass326-current-advanced.lean

git -c fetch.writeCommitGraph=false fetch \
  --no-tags --no-recurse-submodules origin \
  "${ADVANCED_BASELINE_COMMIT}" "${FA_BASELINE_COMMIT}" \
  2>&1 | tee "${EVIDENCE}/logs/fetch-baselines.log"
git show "${FA_BASELINE_COMMIT}:${FA}" > "${FA}"
git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"

apply() {
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
  apply_three_hundred_twenty_sixth_pass_functional_analysis_repairs.py; do
  apply "${script}"
done

cp /tmp/capture-pass326-current-advanced.lean "${ADVANCED}"
actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
test "${actual_sha}" = "${EXPECTED_OUTPUT_SHA256}"
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass326.lean"
wc -l -c "${FA}" | tee "${EVIDENCE}/source-size.txt"
printf '%s\n' \
  "candidate_sha256=${actual_sha}" \
  "candidate_blob=$(git hash-object "${FA}")" \
  "utc_completed=$(date -u +%FT%TZ)" \
  | tee "${EVIDENCE}/status.txt"
