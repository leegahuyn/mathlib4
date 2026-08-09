from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
baseline_sha = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
expected_output_sha = '6dcce7863ed957307a7297e530247d6d177dc27bc3d126d9801bba84e1913814'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != baseline_sha:
    raise SystemExit(f'unexpected PASS376 champion sha256: {actual}')

old = '''theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    HasDerivAt (actualEdgeAmbientParam e)
      (actualEdgeNativeVelocity e t) (t : Real) := by
  letI : AddCommGroup Complex := Complex.addCommGroup
'''
new = '''theorem actualEdgeAmbientParam_hasDerivAt
    (e : GammaTwoActualPolygonEdge)
    (t : modularTileEdgeParameterSet e.2) :
    @HasDerivAt ℝ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup _ _ _
      (actualEdgeAmbientParam e) (actualEdgeNativeVelocity e t) (t : Real) := by
  -- Pin the theorem statement to the canonical complex additive structure.
'''
if text.count(old) != 1:
    raise SystemExit(f'explicit canonical HasDerivAt repair expected once, found {text.count(old)}')
text = text.replace(old, new)

for edge, expected_count in [
    ('circularArc', 5),
    ('leftVerticalSegment', 2),
    ('rightVerticalSegment', 2),
]:
    old = ('GammaTwoActualPolygonEdge.paired '
           f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)')
    new = ('(GammaTwoActualPolygonEdge.paired '
           f'((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))')
    count = text.count(old)
    if count != expected_count:
        raise SystemExit(f'{edge} paired repair expected {expected_count}, found {count}')
    text = text.replace(old, new)

old = '  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n'
new = '  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]; ring\n'
if text.count(old) != 1:
    raise SystemExit(f'scalar normalization expected once, found {text.count(old)}')
text = text.replace(old, new)

output_sha = hashlib.sha256(text.encode()).hexdigest()
line_count = len(text.splitlines())
if output_sha != expected_output_sha or line_count != 60453:
    raise SystemExit(f'unexpected FA382 output: sha={output_sha} lines={line_count}')
path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + output_sha)
print('lines=' + str(line_count))
print('repairs=11')
