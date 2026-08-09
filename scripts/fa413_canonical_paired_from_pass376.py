from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')

baseline_sha = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
expected_output_sha = 'c500aeef3f920bd8451f0c2926c9cc8e63d87f2b39bb24f982f338b7f33370a8'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != baseline_sha:
    raise SystemExit(f'unexpected baseline sha256: {actual}')

old = '''theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  letI : AddCommGroup Complex := Complex.addCommGroup
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
'''
new = '''theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
'''
if text.count(old) != 1:
    raise SystemExit(f'31725 instance removal expected once, found {text.count(old)}')
text = text.replace(old, new)

for edge, expected_count in [
    ('circularArc', 5),
    ('leftVerticalSegment', 2),
    ('rightVerticalSegment', 2),
]:
    old = (
        'GammaTwoActualPolygonEdge.paired '
        f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)'
    )
    new = f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired'
    count = text.count(old)
    if count != expected_count:
        raise SystemExit(f'{edge} paired repair expected {expected_count}, found {count}')
    text = text.replace(old, new)

old = '''  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]

/-- Explicit enumeration of the three base-edge labels. -/
'''
new = '''  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]
  ring

/-- Explicit enumeration of the three base-edge labels. -/
'''
if text.count(old) != 1:
    raise SystemExit(f'32380 normalization expected once, found {text.count(old)}')
text = text.replace(old, new)

output_sha = hashlib.sha256(text.encode()).hexdigest()
if output_sha != expected_output_sha:
    raise SystemExit(f'unexpected output sha256: {output_sha}')

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + output_sha)
print('repairs=11')
