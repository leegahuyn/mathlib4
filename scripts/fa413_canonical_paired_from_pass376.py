from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected:
    raise SystemExit(f'unexpected PASS376 champion input sha256: {actual}')

repairs = 0


def replace_once(old: str, new: str, label: str) -> None:
    global text, repairs
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected once, found {count}')
    text = text.replace(old, new)
    repairs += 1


# Preserve the theorem's line count while selecting the same canonical additive
# structure used by the composed derivative term.
replace_once(
    '  letI : AddCommGroup Complex := Complex.addCommGroup\n',
    '  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n',
    '31725 canonical Complex AddCommGroup',
)

# `paired` is a function.  Parenthesize the complete application so it is
# passed as one edge argument to the surrounding integral/integrand calls.
for edge, expected_count in {
    'circularArc': 5,
    'leftVerticalSegment': 2,
    'rightVerticalSegment': 2,
}.items():
    old = (
        'GammaTwoActualPolygonEdge.paired '
        f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)'
    )
    new = (
        '(GammaTwoActualPolygonEdge.paired '
        f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))'
    )
    count = text.count(old)
    if count != expected_count:
        raise SystemExit(f'{edge} paired application: expected {expected_count}, found {count}')
    text = text.replace(old, new)
    repairs += count

replace_once(
"""  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]

/-- Explicit enumeration of the three base-edge labels. -/
""",
"""  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]
  simp

/-- Explicit enumeration of the three base-edge labels. -/
""",
    '32380 scalar normalization',
)

# The set-membership goal unfolds to the displayed height inequality.
replace_once(
    '        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n',
    '        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n',
    '32754 height membership',
)

# The integral matrices act continuously on the upper half-plane, hence every
# constant action is measurable.  One local instance removes both downstream
# MeasurableConstSMul synthesis failures.
replace_once(
"""open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
""",
"""open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

local instance gammaTwoGlobalStokesBridgeMeasurableConstSMul :
    MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul g :=
    (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
""",
    '32590 and 33063 measurable SL2Z action',
)

# UpperHalfPlane is a structure with its own continuous constructor and ext
# theorem; it is not a subtype in the pinned Mathlib version.
replace_once(
"""    hcomplex.subtype_mk _
""",
"""    hcomplex.upperHalfPlaneMk _
""",
    '33552 UpperHalfPlane constructor',
)
replace_once(
"""      apply Subtype.ext
      apply Complex.ext <;> simp)
""",
"""      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp)
""",
    '33558 UpperHalfPlane extensionality',
)

# Expose pointwise function addition before applying distributivity.
replace_once(
"""  change
    (selectedCuspTraceWeight n q Y t : ℂ) *
        (((u : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t)) +
         ((v : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t))) = _
  ring
""",
"""  change
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
""",
    '33624 pointwise addition',
)

# Unfold the linear-map application explicitly so the literal MemLp.toLp
# representative is visible to the standard coercion theorem.
replace_once(
"""theorem coeFn_selectedCuspCoreTrace
    (n : ℤ) (q : GammaTwoRightCoset) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ⇑(selectedCuspCoreTrace n q Y u) =ᵐ[
      selectedHorocycleParameterMeasure]
        selectedCuspRestrictionRepresentative n q Y u := by
  simpa only [selectedCuspCoreTrace] using
    MemLp.coeFn_toLp
      (selectedCuspRestrictionRepresentative_memLp n q Y u)
""",
"""theorem coeFn_selectedCuspCoreTrace
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
""",
    '33703 Lp representative',
)

# The projection belongs to the returned tail certificate.  Keep the period
# inside parentheses so Lean does not parse it as a new function argument.
old_tail = """  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)
      .eventually_zero_on_horocycleBoundary with
"""
new_tail = """  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with
"""
count = text.count(old_tail)
if count != 2:
    raise SystemExit(f'33794/33817 tail projection: expected twice, found {count}')
text = text.replace(old_tail, new_tail)
repairs += count

replace_once(
    '  simpa using htrace.trans hrep\n',
    '  simpa only [Pi.zero_apply] using htrace.trans hrep\n',
    '33840 zero function coercion',
)

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('repairs=' + str(repairs))
