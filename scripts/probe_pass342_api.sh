#!/usr/bin/env bash
set -euo pipefail

OUT='/tmp/pass342-api-probe'
rm -rf "${OUT}"
mkdir -p "${OUT}"

cat > /tmp/Pass342NNRealA.lean <<'LEAN'
import Mathlib

open MeasureTheory Set Function Topology

noncomputable def probeHyperbolicDensityA (z : ℍ) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

example : Continuous probeHyperbolicDensityA := by
  exact ((continuous_const.div UpperHalfPlane.continuous_im
    (fun z => z.im_ne_zero)).pow 2).subtype_mk _
LEAN

cat > /tmp/Pass342NNRealB.lean <<'LEAN'
import Mathlib

open MeasureTheory Set Function Topology

noncomputable def probeHyperbolicDensityB (z : ℍ) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

example : Continuous probeHyperbolicDensityB := by
  fun_prop
LEAN

cat > /tmp/Pass342Instance.lean <<'LEAN'
import Mathlib

noncomputable abbrev ProbeCore := (⊤ : Submodule ℂ ℂ)

noncomputable local instance probeCoreAddCommGroup : AddCommGroup ProbeCore := by
  change AddCommGroup ↥(⊤ : Submodule ℂ ℂ)
  exact inferInstanceAs (AddCommGroup ↥(⊤ : Submodule ℂ ℂ))

noncomputable local instance probeCoreModule : Module ℂ ProbeCore := by
  change Module ℂ ↥(⊤ : Submodule ℂ ℂ)
  exact inferInstanceAs (Module ℂ ↥(⊤ : Submodule ℂ ℂ))

#synth AddCommGroup ProbeCore
#synth Module ℂ ProbeCore
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
exit 0
