from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected:
    raise SystemExit(f'unexpected champion input sha256: {actual}')

old = """theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  letI : AddCommGroup Complex := Complex.addCommGroup
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
"""
new = """theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
"""
if text.count(old) != 1:
    raise SystemExit(f'31725 instance repair expected once, found {text.count(old)}')
text = text.replace(old, new)

paired_counts = {
    'circularArc': 5,
    'leftVerticalSegment': 2,
    'rightVerticalSegment': 2,
}
for edge, expected_count in paired_counts.items():
    old = (
        'GammaTwoActualPolygonEdge.paired '
        f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)'
    )
    new = f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired'
    count = text.count(old)
    if count != expected_count:
        raise SystemExit(
            f'{edge} pairing repair expected {expected_count}, found {count}'
        )
    text = text.replace(old, new)

old = """  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]

/-- Explicit enumeration of the three base-edge labels. -/
"""
new = """  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]
  simp

/-- Explicit enumeration of the three base-edge labels. -/
"""
if text.count(old) != 1:
    raise SystemExit(f'32380 closure repair expected once, found {text.count(old)}')
text = text.replace(old, new)

old = """        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩
"""
new = """        (show z.im ≤ H from le_of_not_gt hHigh)⟩
"""
if text.count(old) != 1:
    raise SystemExit(f'32754 membership repair expected once, found {text.count(old)}')
text = text.replace(old, new)

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('repairs=12')
