from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected:
    raise SystemExit(f'unexpected PASS376 champion input sha256: {actual}')

repls = [
    (
        "/-! #### Selected-coset actual edges -/\n\n/-- Ambient formula for an actual edge obtained from a selected right-coset\n",
        "/-! #### Selected-coset actual edges -/\nsection actualEdgeCanonicalDerivative\n/-- Ambient formula for an actual edge obtained from a selected right-coset\n",
        'open isolated declaration scope',
    ),
    (
        "  exact selectedCoset_smulFDeriv_apply e.1\n    (modularTileEdgeParam e.2 t) (modularTileEdgeVelocity e.2 t)\n\n/-- The Mobius-composed actual edge has the declared native tangent. -/\n",
        "  exact selectedCoset_smulFDeriv_apply e.1\n    (modularTileEdgeParam e.2 t) (modularTileEdgeVelocity e.2 t)\nnoncomputable local instance actualEdgeCanonicalComplexAddCommGroup : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n/-- The Mobius-composed actual edge has the declared native tangent. -/\n",
        'declare noncomputable canonical instance before theorem statement',
    ),
    (
        "  letI : AddCommGroup Complex := Complex.addCommGroup\n  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t\n",
        "  -- The theorem statement and derivative chain share the declaration-scoped canonical instance.\n  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t\n",
        'remove proof-local legacy instance while preserving line count',
    ),
    (
        "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp\n\n/-! #### Native tangent compatibility under the actual side pairing -/\n",
        "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp\nend actualEdgeCanonicalDerivative\n/-! #### Native tangent compatibility under the actual side pairing -/\n",
        'close isolated declaration scope',
    ),
]

for old, new, label in repls:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected once, found {count}')
    text = text.replace(old, new)

line_count = len(text.splitlines())
if line_count != 60453:
    raise SystemExit(f'line-count drift: {line_count}, expected 60453')

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('lines=' + str(line_count))
print('repairs=4')
