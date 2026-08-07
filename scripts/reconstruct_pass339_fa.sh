#!/usr/bin/env bash
set -euo pipefail

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
FA_BASELINE_COMMIT='402e2b7aa053b9c43d95f24e6146efbc5ccf714b'
EXPECTED='6c277b2a7eefc7c4bd776ddd2b37550268a058d333b2457a6b5428d5cf419599'

cp "${ADVANCED}" /tmp/pass339-current-advanced.lean
git -c fetch.writeCommitGraph=false fetch \
  --no-tags --no-recurse-submodules origin \
  "${ADVANCED_BASELINE_COMMIT}" "${FA_BASELINE_COMMIT}"
git show "${FA_BASELINE_COMMIT}:${FA}" > "${FA}"
git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"

apply() {
  local script="$1"
  echo "===== ${script} ====="
  python3 "scripts/${script}"
}

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
  apply_three_hundred_thirty_ninth_pass_functional_analysis_repairs.py; do
  apply "${script}"
done

cp /tmp/pass339-current-advanced.lean "${ADVANCED}"
actual="$(sha256sum "${FA}" | awk '{print $1}')"
echo "pass339_source_sha256=${actual}"
test "${actual}" = "${EXPECTED}"
