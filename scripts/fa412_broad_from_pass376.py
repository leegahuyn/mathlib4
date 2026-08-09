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

# PASS411 deterministic frontier repairs.
replace_once(
"""theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  letI : AddCommGroup Complex := Complex.addCommGroup
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
""",
"""theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
""",
'31725 canonical Complex instance')

for edge, expected_count in {
    'circularArc': 5,
    'leftVerticalSegment': 2,
    'rightVerticalSegment': 2,
}.items():
    old = (
        'GammaTwoActualPolygonEdge.paired '
        f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)'
    )
    new = f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired'
    count = text.count(old)
    if count != expected_count:
        raise SystemExit(f'{edge}: expected {expected_count}, found {count}')
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
'32380 scalar normalization')

replace_once(
"""        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩
""",
"""        (show z.im ≤ H from le_of_not_gt hHigh)⟩
""",
'32754 set membership')

# One measurable-action instance discharges both 32590 and 33063.
replace_once(
"""open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
""",
"""open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

/-- The integral matrices act through their real `GL₂` realization, whose
Möbius action is continuous and hence measurable. -/
local instance gammaTwoGlobalStokesBridgeMeasurableConstSMul :
    MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul g := by
    change Measurable (fun z : ℍ => ((g : GL (Fin 2) ℝ) • z))
    exact (continuous_const_smul _).measurable

/-! #### A. The selected open and half-open tiles agree almost everywhere -/
""",
'32590/33063 measurable SL2Z action')

# Current UpperHalfPlane is a structure, not a subtype.  Use its official
# continuous constructor and structure extensionality theorem.
replace_once(
"""  have hbase' : Continuous (fun t : ℝ =>
      (⟨(t : ℂ) + (gammaTwoCuspLevel Y : ℂ) * Complex.I,
        lt_of_lt_of_le zero_lt_one
          (by simpa using one_le_gammaTwoCuspLevel Y)⟩ : ℍ)) :=
    hcomplex.subtype_mk _
""",
"""  have hbase' : Continuous (fun t : ℝ =>
      (⟨(t : ℂ) + (gammaTwoCuspLevel Y : ℂ) * Complex.I,
        lt_of_lt_of_le zero_lt_one
          (by simpa using one_le_gammaTwoCuspLevel Y)⟩ : ℍ)) :=
    hcomplex.upperHalfPlaneMk _
""",
'33552 UpperHalfPlane constructor')

replace_once(
"""    hbase'.congr (fun t => by
      apply Subtype.ext
      apply Complex.ext <;> simp)
""",
"""    hbase'.congr (fun t => by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp)
""",
'33558 UpperHalfPlane extensionality')

# Expose pointwise function addition explicitly instead of leaving an opaque
# right-hand side for `ring`.
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
'33624 pointwise add')

# Unfold the actual linear-map application before invoking the `MemLp` API.
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
'33703 Lp representative')

# Parenthesize field projection before use; the old line break parsed it as a
# function application to `.eventually_zero_on_horocycleBoundary`.
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
"""  simpa using htrace.trans hrep
""",
"""  simpa only [Pi.zero_apply] using htrace.trans hrep
""",
'33840 zero function coercion')

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('repairs=' + str(repairs))
