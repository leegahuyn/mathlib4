from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected_input = 'c500aeef3f920bd8451f0c2926c9cc8e63d87f2b39bb24f982f338b7f33370a8'
expected_output = 'be153c8a935960dfbf3b3f30158ddd582249ca89c8cd671e05ae41bf9f21f844'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected_input:
    raise SystemExit(f'unexpected FA377 input sha256: {actual}')
repairs = 0

def replace_once(old: str, new: str, label: str) -> None:
    global text, repairs
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected once, found {count}')
    text = text.replace(old, new)
    repairs += 1

replace_once(
'''open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
''',
'''open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

local instance gammaTwoGlobalStokesBridgeMeasurableConstSMul :
    MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul g :=
    (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
''',
'measurable SL2Z action')

replace_once(
'        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n',
'        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n',
'height membership')

replace_once('    hcomplex.subtype_mk _\n', '    hcomplex.upperHalfPlaneMk _\n',
             'UpperHalfPlane constructor')
replace_once(
'''      apply Subtype.ext
      apply Complex.ext <;> simp)
''',
'''      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp)
''',
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
          (gammaTwoSelectedHorocycleParam q Y t))) =
      (selectedCuspTraceWeight n q Y t : ℂ) *
          ((u : SmoothQuotientCompactFunction)
            (gammaTwoSelectedHorocycleParam q Y t)) +
        (selectedCuspTraceWeight n q Y t : ℂ) *
          ((v : SmoothQuotientCompactFunction)
            (gammaTwoSelectedHorocycleParam q Y t))
  exact mul_add _ _ _
''',
'pointwise addition')

replace_once(
'''theorem coeFn_selectedCuspCoreTrace
    (n : ℤ) (q : GammaTwoRightCoset) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ⇑(selectedCuspCoreTrace n q Y u) =ᵐ[
      selectedHorocycleParameterMeasure]
        selectedCuspRestrictionRepresentative n q Y u := by
  simpa only [selectedCuspCoreTrace] using
    MemLp.coeFn_toLp
      (selectedCuspRestrictionRepresentative_memLp n q Y u)
''',
'''theorem coeFn_selectedCuspCoreTrace
    (n : ℤ) (q : GammaTwoRightCoset) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ⇑(selectedCuspCoreTrace n q Y u) =ᵐ[
      selectedHorocycleParameterMeasure]
        selectedCuspRestrictionRepresentative n q Y u := by
  change
    ⇑((selectedCuspRestrictionRepresentative_memLp n q Y u).toLp
      (selectedCuspRestrictionRepresentative n q Y u)) =ᵐ[
        selectedHorocycleParameterMeasure]
      selectedCuspRestrictionRepresentative n q Y u
  exact MemLp.coeFn_toLp
    (selectedCuspRestrictionRepresentative_memLp n q Y u)
''',
'Lp representative')

old_tail = '''  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)
      .eventually_zero_on_horocycleBoundary with
'''
new_tail = '''  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with
'''
count = text.count(old_tail)
if count != 2:
    raise SystemExit(f'tail projection: expected twice, found {count}')
text = text.replace(old_tail, new_tail)
repairs += count

replace_once('  simpa using htrace.trans hrep\n',
             '  simpa only [Pi.zero_apply] using htrace.trans hrep\n',
             'zero function coercion')

output = hashlib.sha256(text.encode()).hexdigest()
if output != expected_output:
    raise SystemExit(f'unexpected FA378 output sha256: {output}')
path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + output)
print('repairs=' + str(repairs))
