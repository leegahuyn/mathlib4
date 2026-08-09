from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected_input = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
expected_output = '49c1c0eac33f5e758d66a99955a1690592803406a21277d5b4b4d230072d1f74'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected_input:
    raise SystemExit(f'unexpected PASS376 champion input sha256: {actual}')

old = '''  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp
'''
new = '''  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity, Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp
'''
count = text.count(old)
if count != 1:
    raise SystemExit(f'derivative-wrapper unfold repair expected once, found {count}')
text = text.replace(old, new)

output = hashlib.sha256(text.encode()).hexdigest()
line_count = len(text.splitlines())
if output != expected_output or line_count != 60453:
    raise SystemExit(f'unexpected FA381b output: sha={output} lines={line_count}')
path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + output)
print('lines=' + str(line_count))
print('repairs=1')
