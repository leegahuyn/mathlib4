#!/usr/bin/env bash
set -euo pipefail

OUT='/tmp/probe-pass348-core-coherence'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OLEAN='.lake/build/lib/lean/PrimalitySheafVerification'
mkdir -p "${OUT}/logs" "${OUT}/source" "${OLEAN}"

# Reconstruct the authoritative PASS 347 candidate. Its expected compile failure
# is irrelevant here; the resulting source remains available for the probes.
set +e
bash scripts/diagnose_pass347_frontier.sh > "${OUT}/logs/reconstruct-pass347.log" 2>&1
reconstruct_rc=$?
set -e
base_sha="$(sha256sum "${FA}" | awk '{print $1}')"
printf 'reconstruct_exit=%s\nbase_sha256=%s\n' "${reconstruct_rc}" "${base_sha}" \
  > "${OUT}/provenance.txt"
test "${base_sha}" = 'c980501c4a7f0f6582c5d67ec7fa08c7af37ffd6aa3335a3724928f94c2de03f'

python3 - <<'PY'
from pathlib import Path

source = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text(encoding='utf-8')
out = Path('/tmp/probe-pass348-core-coherence/source')

old_coordinates = '''/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
noncomputable def coordinates (n : ℤ) := by
  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=
    inverseEtaFixedPhaseCoreAddCommGroup n
  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=
    inverseEtaFixedPhaseCoreModule n
  exact QuotientHilbertCoordinates.mk
    (l2Coordinate n) (raisedCoordinate n) (loweredCoordinate n)
'''
new_coordinates = '''/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
noncomputable def coordinates (n : ℤ) :
    QuotientHilbertCoordinates
      (InverseEtaFixedPhaseCore n)
      (OrbitPeterssonHilbert n)
      (OrbitPeterssonHilbert (n + 1))
      (OrbitPeterssonHilbert (n - 1)) where
  base := l2Coordinate n
  raised := raisedCoordinate n
  lowered := loweredCoordinate n
'''
if source.count(old_coordinates) != 1:
    raise SystemExit(f'coordinate block count={source.count(old_coordinates)}')
base = source.replace(old_coordinates, new_coordinates, 1)

needle = '''noncomputable instance inverseEtaFixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) where
'''
if base.count(needle) != 1:
    raise SystemExit(f'module marker count={base.count(needle)}')
priority_parent = '''noncomputable instance (priority := 2000)
    inverseEtaFixedPhaseCoreAddCommMonoid (n : ℤ) :
    AddCommMonoid (InverseEtaFixedPhaseCore n) :=
  (inverseEtaFixedPhaseCoreAddCommGroup n).toAddCommMonoid

'''
variant_a = base.replace(needle, priority_parent + needle, 1)

old_instances_start = base.index('/- The all-word stable core is a complex submodule')
old_instances_end = base.index('/-- Once the one-step covariance theorem', old_instances_start)
minimal = '''/- The stable core keeps its existing addition and scalar action.  Negation is
scalar multiplication by `-1`; the high-priority parent instance makes the
additive group and module share exactly one `AddCommMonoid`. -/
noncomputable instance inverseEtaFixedPhaseCoreNeg (n : ℤ) :
    Neg (InverseEtaFixedPhaseCore n) where
  neg x :=
    ⟨(-1 : ℂ) • x.1,
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) x.2⟩

noncomputable instance inverseEtaFixedPhaseCoreAddGroup (n : ℤ) :
    AddGroup (InverseEtaFixedPhaseCore n) :=
  AddGroup.ofLeftAxioms
    (fun x y z => by apply Subtype.ext; exact add_assoc _ _ _)
    (fun x => by apply Subtype.ext; exact zero_add _)
    (fun x => by
      apply Subtype.ext
      change (-1 : ℂ) • x.1 + x.1 = 0
      simp)

noncomputable instance inverseEtaFixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) :=
  { inverseEtaFixedPhaseCoreAddGroup n with
    add_comm := fun x y => by apply Subtype.ext; exact add_comm _ _ }

noncomputable instance (priority := 2000)
    inverseEtaFixedPhaseCoreAddCommMonoid (n : ℤ) :
    AddCommMonoid (InverseEtaFixedPhaseCore n) :=
  (inverseEtaFixedPhaseCoreAddCommGroup n).toAddCommMonoid

noncomputable instance (priority := 2000)
    inverseEtaFixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) where
  one_smul x := by apply Subtype.ext; simp
  mul_smul a b x := by apply Subtype.ext; simp [mul_smul]
  smul_zero a := by apply Subtype.ext; simp
  smul_add a x y := by apply Subtype.ext; simp [smul_add]
  add_smul a b x := by apply Subtype.ext; simp [add_smul]
  zero_smul x := by apply Subtype.ext; simp

'''
variant_b = base[:old_instances_start] + minimal + base[old_instances_end:]

marker = '''/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
'''
smoke = '''#synth AddCommGroup (InverseEtaFixedPhaseCore 0)
#synth AddCommMonoid (InverseEtaFixedPhaseCore 0)
#synth Module ℂ (InverseEtaFixedPhaseCore 0)

'''
for name, text in [('parent-priority', variant_a), ('minimal-priority', variant_b)]:
    if text.count(marker) != 1:
        raise SystemExit(f'{name}: coordinates marker count={text.count(marker)}')
    text = text.replace(marker, smoke + marker, 1)
    (out / f'{name}.lean').write_text(text, encoding='utf-8')
PY

printf 'probe,exit_code,error_count,first_error\n' > "${OUT}/summary.csv"
for probe in parent-priority minimal-priority; do
  log="${OUT}/logs/${probe}.log"
  rm -f "${OLEAN}/Mock2_FunctionalAnalysis.olean" \
    "${OLEAN}/Mock2_FunctionalAnalysis.ilean" \
    "${OLEAN}/Mock2_FunctionalAnalysis.olean.private"
  set +e
  lake env lean -DmaxErrors=1 "${OUT}/source/${probe}.lean" \
    -o "${OLEAN}/Mock2_FunctionalAnalysis.olean" \
    -i "${OLEAN}/Mock2_FunctionalAnalysis.ilean" \
    > "${log}" 2>&1
  rc=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  first="$(grep -m1 -E ':[0-9]+:[0-9]+: error' "${log}" | tr ',' ';' || true)"
  printf '%s,%s,%s,%s\n' "${probe}" "${rc}" "${errors}" "${first}" \
    >> "${OUT}/summary.csv"
done
cat "${OUT}/summary.csv"
exit 0
