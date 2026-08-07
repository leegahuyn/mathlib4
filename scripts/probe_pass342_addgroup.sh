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
#check AddSubgroup.instAddGroup
#check AddSubgroup.instAddCommGroup
#check AddSubgroup.addCommGroup

#synth AddCommGroup ↥((inverseEtaFixedPhaseStableCoreSubmodule 0).toAddSubgroup)

example : AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule 0) := by
  change AddCommGroup ↥((inverseEtaFixedPhaseStableCoreSubmodule 0).toAddSubgroup)
  infer_instance

example : AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule 0) := by
  exact inferInstanceAs
    (AddCommGroup ↥((inverseEtaFixedPhaseStableCoreSubmodule 0).toAddSubgroup))
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
cat "${OUT}/summary.csv"
exit 0
