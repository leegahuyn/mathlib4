#!/usr/bin/env bash
set -euo pipefail

OUT='/tmp/pass342-api-probe'
mkdir -p "${OUT}"

cat > /tmp/Pass342NNRealA.lean <<'LEAN'
import PrimalitySheafVerification.Mock2_Advanced

open MeasureTheory Set Function Topology

noncomputable def probeHyperbolicDensityA (z : ℍ) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

example : Continuous probeHyperbolicDensityA := by
  exact ((continuous_const.div UpperHalfPlane.continuous_im
    (fun z => z.im_ne_zero)).pow 2).subtype_mk _
LEAN

cat > /tmp/Pass342NNRealB.lean <<'LEAN'
import PrimalitySheafVerification.Mock2_Advanced

open MeasureTheory Set Function Topology

noncomputable def probeHyperbolicDensityB (z : ℍ) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

example : Continuous probeHyperbolicDensityB := by
  fun_prop
LEAN

cat > /tmp/Pass342Instance.lean <<'LEAN'
import PrimalitySheafVerification.Mock2_Advanced

namespace Mock2FA.PaperCorrections.AutomorphicSobolev
open HalfWeightDifferentialOperators

noncomputable local instance probeCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance probeCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

#synth AddCommGroup (InverseEtaFixedPhaseCore 0)
#synth Module ℂ (InverseEtaFixedPhaseCore 0)

end Mock2FA.PaperCorrections.AutomorphicSobolev
LEAN

printf 'probe,exit_code,error_count\n' > "${OUT}/summary.csv"
for probe in Pass342NNRealA Pass342NNRealB Pass342Instance; do
  set +e
  lake env lean "/tmp/${probe}.lean" > "${OUT}/${probe}.log" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${OUT}/${probe}.log" || true)"
  printf '%s,%s,%s\n' "${probe}" "${code}" "${errors}" >> "${OUT}/summary.csv"
  cp "/tmp/${probe}.lean" "${OUT}/"
done
cat "${OUT}/summary.csv"
# The probe job itself succeeds so every candidate log is uploaded.
exit 0
