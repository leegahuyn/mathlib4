#!/usr/bin/env bash
set -euo pipefail

# Reconstruct the exact PASS 341 candidate and preserve the existing API-probe
# evidence first.
bash scripts/probe_pass342_api.sh

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OUT='/tmp/pass342-api-probe'

head -n 19654 "${FA}" > /tmp/Pass342AddGroup.lean
cat >> /tmp/Pass342AddGroup.lean <<'LEAN'

noncomputable section

#check AddSubgroup.toAddGroup
#check AddSubgroup.toAddCommGroup

#synth AddCommGroup ↥((inverseEtaFixedPhaseStableCoreSubmodule 0).toAddSubgroup)

example : AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule 0) := by
  change AddCommGroup ↥((inverseEtaFixedPhaseStableCoreSubmodule 0).toAddSubgroup)
  infer_instance
LEAN

set +e
lake env lean -DmaxErrors=30 /tmp/Pass342AddGroup.lean \
  > "${OUT}/Pass342AddGroup.log" 2>&1
code=$?
set -e
errors="$(grep -Ec 'error:|error\(' "${OUT}/Pass342AddGroup.log" || true)"
printf '%s,%s,%s\n' Pass342AddGroup "${code}" "${errors}" \
  >> "${OUT}/summary.csv"
cp /tmp/Pass342AddGroup.lean "${OUT}/"

head -n 19654 "${FA}" > /tmp/Pass342ManualCore.lean
cat >> /tmp/Pass342ManualCore.lean <<'LEAN'

noncomputable section

noncomputable def probeStableAddSubgroup (n : ℤ) :
    AddSubgroup SmoothQuotientCompactFunction where
  carrier := inverseEtaFixedPhaseStableCoreSubmodule n
  zero_mem' := (inverseEtaFixedPhaseStableCoreSubmodule n).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (inverseEtaFixedPhaseStableCoreSubmodule n).add_mem hx hy
  neg_mem' := by
    intro x hx
    have h := (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    simpa using h

noncomputable local instance probeStableAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  let S := probeStableAddSubgroup n
  change AddCommGroup ↥S
  exact S.toAddCommGroup

noncomputable local instance probeStableModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) where
  one_smul x := by
    apply Subtype.ext
    simp
  mul_smul a b x := by
    apply Subtype.ext
    simp [mul_smul]
  smul_zero a := by
    apply Subtype.ext
    simp
  smul_add a x y := by
    apply Subtype.ext
    simp [smul_add]
  add_smul a b x := by
    apply Subtype.ext
    simp [add_smul]
  zero_smul x := by
    apply Subtype.ext
    simp

#synth AddCommGroup (InverseEtaFixedPhaseCore 0)
#synth Module ℂ (InverseEtaFixedPhaseCore 0)

example (x y : InverseEtaFixedPhaseCore 0) : x - y = x + (-y) := by
  exact sub_eq_add_neg x y
LEAN

set +e
lake env lean -DmaxErrors=40 /tmp/Pass342ManualCore.lean \
  > "${OUT}/Pass342ManualCore.log" 2>&1
manual_code=$?
set -e
manual_errors="$(grep -Ec 'error:|error\(' "${OUT}/Pass342ManualCore.log" || true)"
printf '%s,%s,%s\n' Pass342ManualCore "${manual_code}" "${manual_errors}" \
  >> "${OUT}/summary.csv"
cp /tmp/Pass342ManualCore.lean "${OUT}/"

cat "${OUT}/summary.csv"
exit 0
