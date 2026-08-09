from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')

baseline_sha = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
expected_output_sha = 'c500aeef3f920bd8451f0c2926c9cc8e63d87f2b39bb24f982f338b7f33370a8'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != baseline_sha:
    raise SystemExit(f'unexpected baseline sha256: {actual}')

old_block = '''theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  letI : AddCommGroup Complex := Complex.addCommGroup
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
'''
new_block = '''theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
'''
if text.count(old_block) != 1:
    raise SystemExit(f'instance repair expected once, found {text.count(old_block)}')
text = text.replace(old_block, new_block)

paired_repairs = [
    ('GammaTwoActualPolygonEdge.paired ((q, GammaTwoModularTileEdge.circularArc) : GammaTwoActualPolygonEdge)',
     '((q, GammaTwoModularTileEdge.circularArc) : GammaTwoActualPolygonEdge).paired', 5),
    ('GammaTwoActualPolygonEdge.paired ((q, GammaTwoModularTileEdge.leftVerticalSegment) : GammaTwoActualPolygonEdge)',
     '((q, GammaTwoModularTileEdge.leftVerticalSegment) : GammaTwoActualPolygonEdge).paired', 2),
    ('GammaTwoActualPolygonEdge.paired ((q, GammaTwoModularTileEdge.rightVerticalSegment) : GammaTwoActualPolygonEdge)',
     '((q, GammaTwoModularTileEdge.rightVerticalSegment) : GammaTwoActualPolygonEdge).paired', 2),
]
for old, new, expected_count in paired_repairs:
    count = text.count(old)
    if count != expected_count:
        raise SystemExit(f'paired repair expected {expected_count}, found {count}: {old}')
    text = text.replace(old, new)

ring_anchor = '''  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]

/-- Explicit enumeration of the three base-edge labels. -/
'''
ring_replacement = '''  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]
  ring

/-- Explicit enumeration of the three base-edge labels. -/
'''
if text.count(ring_anchor) != 1:
    raise SystemExit(f'ring repair expected once, found {text.count(ring_anchor)}')
text = text.replace(ring_anchor, ring_replacement)

output_sha = hashlib.sha256(text.encode()).hexdigest()
if output_sha != expected_output_sha:
    raise SystemExit(f'unexpected output sha256: {output_sha}')

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + output_sha)
print('repairs=11')
