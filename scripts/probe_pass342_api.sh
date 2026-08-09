#!/usr/bin/env bash
set -euo pipefail

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
ADVANCED='PrimalitySheafVerification/Mock2_Advanced.lean'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'
FA_BASELINE_COMMIT='402e2b7aa053b9c43d95f24e6146efbc5ccf714b'
EXPECTED_PASS341_SHA256='d9bce9ec296c799fe144786111da5a6e8f7f0232f55fd34df9cf09be8b140b4e'
OUT='/tmp/pass342-api-probe'
rm -rf "${OUT}"
mkdir -p "${OUT}/logs" "${OUT}/source"

cp "${ADVANCED}" /tmp/pass342-current-advanced.lean
git -c fetch.writeCommitGraph=false fetch \
  --no-tags --no-recurse-submodules origin \
  "${ADVANCED_BASELINE_COMMIT}" "${FA_BASELINE_COMMIT}" \
  >"${OUT}/logs/fetch.log" 2>&1
git show "${FA_BASELINE_COMMIT}:${FA}" > "${FA}"
git show "${ADVANCED_BASELINE_COMMIT}:${ADVANCED}" > "${ADVANCED}"

apply() {
  local script="$1"
  echo "===== ${script} =====" >> "${OUT}/logs/repair-chain.log"
  python3 "scripts/${script}" >> "${OUT}/logs/repair-chain.log" 2>&1
}

for script in \
  apply_two_hundred_eighty_ninth_pass_repairs.py \
  apply_two_hundred_ninetieth_pass_repairs.py \
  apply_two_hundred_ninty_first_pass_repairs.py; do
  :
done

repair_scripts=(
  apply_two_hundred_eighty_ninth_pass_repairs.py
  apply_two_hundred_ninetieth_pass_repairs.py
  apply_two_hundred_ninety_first_pass_repairs.py
  apply_two_hundred_ninety_second_pass_repairs.py
  apply_two_hundred_ninety_third_pass_repairs.py
  apply_two_hundred_ninety_fourth_pass_repairs.py
  apply_two_hundred_ninety_fifth_pass_repairs.py
  apply_two_hundred_ninety_seventh_pass_repairs.py
  apply_two_hundred_ninety_eighth_pass_repairs.py
  apply_two_hundred_ninety_ninth_pass_repairs.py
  apply_three_hundredth_pass_repairs.py
  apply_three_hundred_ninth_pass_repairs.py
  apply_three_hundred_tenth_pass_repairs.py
  apply_three_hundred_eleventh_pass_repairs.py
  apply_three_hundred_twelfth_pass_repairs.py
  apply_three_hundred_thirteenth_pass_repairs.py
  apply_three_hundred_fourteenth_pass_repairs.py
  apply_three_hundred_fifteenth_pass_repairs.py
  fa316_driver.py
  apply_three_hundred_seventeenth_pass_functional_analysis_repairs.py
  apply_three_hundred_eighteenth_pass_functional_analysis_repairs.py
  apply_three_hundred_nineteenth_pass_functional_analysis_repairs.py
  apply_three_hundred_twentieth_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_first_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_second_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_third_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_fourth_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_fifth_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_sixth_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_seventh_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py
  apply_three_hundred_twenty_ninth_pass_functional_analysis_repairs.py
  apply_three_hundred_thirtieth_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_first_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_second_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_third_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_fourth_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_fifth_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_sixth_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_seventh_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_eighth_pass_functional_analysis_repairs.py
  apply_three_hundred_thirty_ninth_pass_functional_analysis_repairs.py
  fa340_repair.py
  fa341_repair.py
)
: > "${OUT}/logs/repair-chain.log"
for script in "${repair_scripts[@]}"; do
  apply "${script}"
done
cp /tmp/pass342-current-advanced.lean "${ADVANCED}"
actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
test "${actual_sha}" = "${EXPECTED_PASS341_SHA256}"
cp "${FA}" "${OUT}/source/Mock2_FunctionalAnalysis-pass341.lean"

# Stop immediately before the first PASS 341 local instance declaration.
head -n 19654 "${FA}" > /tmp/Pass342CoreInstances.lean
cat >> /tmp/Pass342CoreInstances.lean <<'LEAN'

#synth AddCommGroup SmoothFunction
#synth Module ℂ SmoothFunction
#synth AddCommGroup SmoothQuotientCompactFunction
#synth Module ℂ SmoothQuotientCompactFunction
#synth AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule 0)
#synth Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule 0)

example : AddCommGroup SmoothFunction := by infer_instance
example : Module ℂ SmoothFunction := by infer_instance
example : AddCommGroup SmoothQuotientCompactFunction := by infer_instance
example : Module ℂ SmoothQuotientCompactFunction := by infer_instance
example : AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule 0) := by
  infer_instance
example : Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule 0) := by
  infer_instance
LEAN

cat > /tmp/Pass342NNRealA.lean <<'LEAN'
import Mathlib

open MeasureTheory Set Function Topology

noncomputable def probeHyperbolicDensityA (z : UpperHalfPlane) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

example : Continuous probeHyperbolicDensityA := by
  exact ((continuous_const.div UpperHalfPlane.continuous_im
    (fun z => z.im_ne_zero)).pow 2).subtype_mk _
LEAN

cat > /tmp/Pass342NNRealB.lean <<'LEAN'
import Mathlib

open MeasureTheory Set Function Topology

noncomputable def probeHyperbolicDensityB (z : UpperHalfPlane) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

example : Continuous probeHyperbolicDensityB := by
  refine Continuous.subtype_mk ?_
  exact (continuous_const.div UpperHalfPlane.continuous_im
    (fun z => z.im_ne_zero)).pow 2
LEAN

cat > /tmp/Pass342NNRealC.lean <<'LEAN'
import Mathlib

open MeasureTheory Set Function Topology

noncomputable def probeHyperbolicDensityC (z : UpperHalfPlane) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

example : Continuous probeHyperbolicDensityC := by
  change Continuous fun z : UpperHalfPlane => (⟨(1 / z.im) ^ 2, sq_nonneg _⟩ : NNReal)
  fun_prop
LEAN

cat > /tmp/Pass342Names.lean <<'LEAN'
import Mathlib
#check Continuous.subtype_mk
#check continuous_subtype_mk
#check Continuous.div
#check Continuous.div₀
#check Submodule.toAddSubmonoid
#check Submodule.toAddSubgroup
#check Submodule.instAddCommGroup
#check Submodule.instModule
LEAN

printf 'probe,exit_code,error_count\n' > "${OUT}/summary.csv"
for probe in Pass342CoreInstances Pass342NNRealA Pass342NNRealB Pass342NNRealC Pass342Names; do
  set +e
  lake env lean -DmaxErrors=30 "/tmp/${probe}.lean" > "${OUT}/${probe}.log" 2>&1
  code=$?
  set -e
  errors="$(grep -Ec 'error:|error\(' "${OUT}/${probe}.log" || true)"
  printf '%s,%s,%s\n' "${probe}" "${code}" "${errors}" >> "${OUT}/summary.csv"
  cp "/tmp/${probe}.lean" "${OUT}/"
done
cat "${OUT}/summary.csv"
exit 0
