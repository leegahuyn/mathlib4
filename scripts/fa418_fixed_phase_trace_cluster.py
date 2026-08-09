from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected = '53b5cd8cfb5be38214f918269515a40621e6340eba93e9fc5b90a081375c120a'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected:
    raise SystemExit(f'unexpected PASS417 input sha256: {actual}')

repairs = 0

def replace_once(old: str, new: str, label: str) -> None:
    global text, repairs
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected once, found {count}')
    text = text.replace(old, new)
    repairs += 1

# The restricted measure and every theorem using it must elaborate under the
# same measurable-space structure.
replace_once(
    'namespace FixedPhaseHorocycleTrace\n\nopen MeasureTheory Set Filter Topology\n',
    'namespace FixedPhaseHorocycleTrace\nnoncomputable local instance fixedPhaseHorocycleTraceMeasurableSpaceReal : MeasurableSpace ℝ := Real.measureSpace.toMeasurableSpace\nopen MeasureTheory Set Filter Topology\n',
    'fixed-phase measurable-space scope')

replace_once('    hcomplex.subtype_mk _\n', '    hcomplex.upperHalfPlaneMk _\n',
    'UpperHalfPlane continuous constructor')
replace_once('      apply Subtype.ext\n      apply Complex.ext <;> simp)\n',
    '      apply UpperHalfPlane.ext\n      apply Complex.ext <;> simp)\n',
    'UpperHalfPlane extensionality')

replace_once(
'''  change
    (selectedCuspTraceWeight n q Y t : ℂ) *
        (((u : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t)) +
         ((v : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t))) = _
  ring
''',
'''  change
    (selectedCuspTraceWeight n q Y t : ℂ) *
        (((u : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t)) +
         ((v : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t))) = (selectedCuspTraceWeight n q Y t : ℂ) * ((u : SmoothQuotientCompactFunction) (gammaTwoSelectedHorocycleParam q Y t)) + (selectedCuspTraceWeight n q Y t : ℂ) * ((v : SmoothQuotientCompactFunction) (gammaTwoSelectedHorocycleParam q Y t))
  exact mul_add _ _ _
''',
    'pointwise trace addition')

replace_once(
'''  simpa only [selectedCuspCoreTrace] using
    MemLp.coeFn_toLp
      (selectedCuspRestrictionRepresentative_memLp n q Y u)
''',
'''  change ⇑((selectedCuspRestrictionRepresentative_memLp n q Y u).toLp (selectedCuspRestrictionRepresentative n q Y u)) =ᵐ[selectedHorocycleParameterMeasure]
    selectedCuspRestrictionRepresentative n q Y u
  exact MemLp.coeFn_toLp (selectedCuspRestrictionRepresentative_memLp n q Y u)
''',
    'literal Lp representative')

old_tail = '''  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)
      .eventually_zero_on_horocycleBoundary with
    ⟨Y₀, hY₀, hZero⟩
'''
new_tail = '''  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with
    -- Parse the certificate projection before the `rcases` pattern.
    ⟨Y₀, hY₀, hZero⟩
'''
count = text.count(old_tail)
if count != 2:
    raise SystemExit(f'tail projection: expected twice, found {count}')
text = text.replace(old_tail, new_tail)
repairs += count

replace_once(
    '    simp only [selectedCuspRestrictionRepresentative, Pi.zero_apply,\n      hz.1, mul_zero]\n',
    '  simp only [selectedCuspRestrictionRepresentative, Pi.zero_apply,\n    hz.1, mul_zero]\n',
    'pointwise tail tactic indentation')

replace_once(
'''  filter_upwards [coeFn_selectedCuspCoreTrace n q Z u,
    hZero Z hYZ q] with t htrace hrep
  simpa using htrace.trans hrep
''',
'''  filter_upwards [coeFn_selectedCuspCoreTrace n q Z u, hZero Z hYZ q,
    MeasureTheory.Lp.coeFn_zero ℂ 2 selectedHorocycleParameterMeasure] with t htrace hrep hzero
  exact (htrace.trans hrep).trans hzero.symm
''',
    'Lp zero representative')

line_count = len(text.splitlines())
if line_count != 60453:
    raise SystemExit(f'line-count drift: {line_count}, expected 60453')
path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('lines=' + str(line_count))
print('repairs=' + str(repairs))
