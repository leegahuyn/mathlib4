from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
baseline_sha = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
expected_output_sha = '580a9924dac76884e56cb3773c0d7f49055a26ee96ea494f06ef35777addc1ab'
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
count = text.count(old)
if count != 1:
    raise SystemExit(f'explicit canonical HasDerivAt repair expected once, found {count}')
text = text.replace(old, new)

output_sha = hashlib.sha256(text.encode()).hexdigest()
line_count = len(text.splitlines())
if output_sha != expected_output_sha or line_count != 60453:
    raise SystemExit(f'unexpected FA381 output: sha={output_sha} lines={line_count}')
path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + output_sha)
print('lines=' + str(line_count))
print('repairs=1')
