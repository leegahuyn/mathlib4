#!/usr/bin/env bash
set -euo pipefail

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OUT='/tmp/probe-pass344-core-instances-v2'
OLEAN='.lake/build/lib/lean/PrimalitySheafVerification'
mkdir -p "${OUT}/logs" "${OLEAN}"

set +e
bash scripts/diagnose_pass344_frontier_v2.sh \
  > "${OUT}/logs/reconstruct-pass344.log" 2>&1
reconstruct_rc=$?
set -e
actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
printf 'reconstruct_exit=%s\nsource_sha256=%s\n' \
  "${reconstruct_rc}" "${actual_sha}" > "${OUT}/provenance.txt"
test "${actual_sha}" = \
  '59d4bcc02ff615190da0691c9bef52fe3d8bfcb0b8cdf573c300e258757376b6'

python3 - <<'PY'
from pathlib import Path

source = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text(encoding='utf-8')
out = Path('/tmp/probe-pass344-core-instances-v2')
coordinates = '''/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
'''
count = source.count(coordinates)
print(f'coordinates marker={count}')
if count != 1:
    raise SystemExit(f'expected unique coordinates marker, found {count}')


def write(name: str, text: str) -> None:
    (out / f'{name}.lean').write_text(text, encoding='utf-8')

current_probe = '''set_option diagnostics true in
set_option trace.Meta.synthInstance true in
#synth AddCommGroup (InverseEtaFixedPhaseCore 0)

set_option diagnostics true in
set_option trace.Meta.synthInstance true in
#synth Module ℂ (InverseEtaFixedPhaseCore 0)

#check fixedPhaseGraphCoreAddCommGroup
#check fixedPhaseGraphCoreModule

example (n : ℤ) : AddCommGroup (InverseEtaFixedPhaseCore n) :=
  fixedPhaseGraphCoreAddCommGroup n

example (n : ℤ) : Module ℂ (InverseEtaFixedPhaseCore n) :=
  fixedPhaseGraphCoreModule n

'''
write('current-local', source.replace(coordinates, current_probe + coordinates, 1))

old_block = '''/- The stable core was defined while its ambient function space exposed only
an additive monoid instance. Repackage the same carrier as an additive
subgroup, then rebuild the compatible complex-module laws on that carrier. -/
private noncomputable def fixedPhaseGraphCoreAddSubgroup (n : ℤ) :
    AddSubgroup SmoothQuotientCompactFunction where
  carrier := inverseEtaFixedPhaseStableCoreSubmodule n
  zero_mem' := (inverseEtaFixedPhaseStableCoreSubmodule n).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (inverseEtaFixedPhaseStableCoreSubmodule n).add_mem hx hy
  neg_mem' := by
    intro x hx
    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    have hneg :
        (-x : SmoothQuotientCompactFunction) = (-1 : ℂ) • x := by
      apply Subtype.ext
      apply Subtype.ext
      funext z
      simp
    rw [hneg]
    exact h

noncomputable local instance fixedPhaseGraphCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  let S := fixedPhaseGraphCoreAddSubgroup n
  change AddCommGroup ↥S
  exact S.toAddCommGroup

noncomputable local instance fixedPhaseGraphCoreModule (n : ℤ) :
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

'''
if source.count(old_block) != 1:
    raise SystemExit(f'current instance block count={source.count(old_block)}')

minimal_block = '''/- Preserve the canonical subtype addition and scalar action.  Supply only
negation, then derive an additive group from the minimal group axioms. -/
noncomputable local instance fixedPhaseGraphCoreNeg (n : ℤ) :
    Neg (InverseEtaFixedPhaseCore n) where
  neg x :=
    ⟨-x.1, by
      have h :=
        (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) x.2
      simpa only [neg_one_smul] using h⟩

noncomputable local instance fixedPhaseGraphCoreAddGroup (n : ℤ) :
    AddGroup (InverseEtaFixedPhaseCore n) :=
  AddGroup.ofLeftAxioms
    (fun x y z => by apply Subtype.ext; exact add_assoc _ _ _)
    (fun x => by apply Subtype.ext; exact zero_add _)
    (fun x => by apply Subtype.ext; exact neg_add_cancel _)

noncomputable local instance fixedPhaseGraphCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) :=
  { fixedPhaseGraphCoreAddGroup n with
    add_comm := fun x y => by apply Subtype.ext; exact add_comm _ _ }

noncomputable local instance fixedPhaseGraphCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact (inverseEtaFixedPhaseStableCoreSubmodule n).module

'''
minimal_source = source.replace(old_block, minimal_block, 1)
minimal_probe = '''set_option diagnostics true in
set_option trace.Meta.synthInstance true in
#synth AddCommGroup (InverseEtaFixedPhaseCore 0)

set_option diagnostics true in
set_option trace.Meta.synthInstance true in
#synth Module ℂ (InverseEtaFixedPhaseCore 0)

example (n : ℤ) : Module ℂ (InverseEtaFixedPhaseCore n) :=
  fixedPhaseGraphCoreModule n

'''
write('minimal-axioms', minimal_source.replace(coordinates, minimal_probe + coordinates, 1))

let_source = source.replace(
    coordinates,
    '''example (n : ℤ) :
    QuotientHilbertCoordinates
      (InverseEtaFixedPhaseCore n)
      (OrbitPeterssonHilbert n)
      (OrbitPeterssonHilbert (n + 1))
      (OrbitPeterssonHilbert (n - 1)) := by
  letI := fixedPhaseGraphCoreAddCommGroup n
  letI := fixedPhaseGraphCoreModule n
  exact
    { base := l2Coordinate n
      raised := raisedCoordinate n
      lowered := loweredCoordinate n }

''' + coordinates,
    1,
)
write('explicit-letI', let_source)
PY

printf 'probe,exit_code,error_count,first_error\n' > "${OUT}/summary.csv"
for probe in current-local minimal-axioms explicit-letI; do
  log="${OUT}/logs/${probe}.log"
  rm -f "${OLEAN}/Mock2_FunctionalAnalysis.olean" \
    "${OLEAN}/Mock2_FunctionalAnalysis.ilean" \
    "${OLEAN}/Mock2_FunctionalAnalysis.olean.private"
  set +e
  lake env lean -DmaxErrors=1 "${OUT}/${probe}.lean" \
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
