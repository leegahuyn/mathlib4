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

# Isolate the target derivative theorem and elaborate both its statement and
# proof under the same canonical (noncomputable) additive structure.
replace_once(
    '/-! #### Selected-coset actual edges -/\n\n/-- Ambient formula for an actual edge obtained from a selected right-coset\n',
    '/-! #### Selected-coset actual edges -/\nsection actualEdgeCanonicalDerivative\n/-- Ambient formula for an actual edge obtained from a selected right-coset\n',
    'open derivative instance scope')
replace_once(
    '  exact selectedCoset_smulFDeriv_apply e.1\n    (modularTileEdgeParam e.2 t) (modularTileEdgeVelocity e.2 t)\n\n/-- The Mobius-composed actual edge has the declared native tangent. -/\n',
    '  exact selectedCoset_smulFDeriv_apply e.1\n    (modularTileEdgeParam e.2 t) (modularTileEdgeVelocity e.2 t)\nnoncomputable local instance actualEdgeCanonicalComplexAddCommGroup : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n/-- The Mobius-composed actual edge has the declared native tangent. -/\n',
    'canonical derivative instance')
replace_once(
    '  letI : AddCommGroup Complex := Complex.addCommGroup\n  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t\n',
    '  -- Statement and chain rule share the declaration-scoped canonical instance.\n  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t\n',
    'remove legacy proof-local instance')
replace_once(
    '  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp\n\n/-! #### Native tangent compatibility under the actual side pairing -/\n',
    '  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp\nend actualEdgeCanonicalDerivative\n/-! #### Native tangent compatibility under the actual side pairing -/\n',
    'close derivative instance scope')

# Pairing is a function application. Parenthesize the complete paired edge.
for edge, expected_count in {
    'circularArc': 5,
    'leftVerticalSegment': 2,
    'rightVerticalSegment': 2,
}.items():
    old = ('GammaTwoActualPolygonEdge.paired '
           f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)')
    new = ('(GammaTwoActualPolygonEdge.paired '
           f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))')
    count = text.count(old)
    if count != expected_count:
        raise SystemExit(f'{edge}: expected {expected_count}, found {count}')
    text = text.replace(old, new)
    repairs += count

replace_once(
    '  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n/-- Explicit enumeration of the three base-edge labels. -/\n',
    '  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  simp\n/-- Explicit enumeration of the three base-edge labels. -/\n',
    'native left-edge scalar closure')

# Add exactly the action interfaces needed by the global Stokes namespaces,
# using already-proved continuous Möbius action and GL-invariant volume.
replace_once(
'''open GammaTwoQuotientGeometry GammaTwoQuotientGreenBoundary
open GammaTwoCurvilinearTileStokes GammaTwoMoebiusPiola
open GammaTwoOrientedBoundaryIntegral
open HalfWeightDifferentialOperators SmoothCompactCoreGeometry
''',
'''open GammaTwoQuotientGeometry GammaTwoQuotientGreenBoundary GammaTwoCurvilinearTileStokes GammaTwoMoebiusPiola
open GammaTwoOrientedBoundaryIntegral HalfWeightDifferentialOperators SmoothCompactCoreGeometry
local instance gammaTwoGlobalStokesBridgeMeasurableConstSMul : MeasurableConstSMul SL(2, ℤ) ℍ where measurable_const_smul g := (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable
local instance gammaTwoGlobalStokesBridgeInvariantMeasure : SMulInvariantMeasure SL(2, ℤ) ℍ hyperbolicMeasure where measure_preimage_smul g s hs := by change volume ((fun z : ℍ => ((g : GL (Fin 2) ℝ) • z)) ⁻¹' s) = volume s; exact SMulInvariantMeasure.measure_preimage_smul _ hs
''',
    'global Stokes action instances')

replace_once(
    '        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n',
    '        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n',
    'closed truncation height membership')

replace_once(
'''open GammaTwoOrientedBoundaryIntegral GammaTwoGlobalStokesBridge
open HalfWeightDifferentialOperators SmoothCompactCoreGeometry

/-- Integrability counterpart of the selected-coset Bochner Jacobian
''',
'''open GammaTwoOrientedBoundaryIntegral GammaTwoGlobalStokesBridge
open HalfWeightDifferentialOperators SmoothCompactCoreGeometry
local instance gammaTwoGlobalStokesCompositionMeasurableConstSMul : MeasurableConstSMul SL(2, ℤ) ℍ where measurable_const_smul g := (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable
/-- Integrability counterpart of the selected-coset Bochner Jacobian
''',
    'composition-support measurable action')

line_count = len(text.splitlines())
if line_count != 60453:
    raise SystemExit(f'line-count drift: {line_count}, expected 60453')
path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('lines=' + str(line_count))
print('repairs=' + str(repairs))
