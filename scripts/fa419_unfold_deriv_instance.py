from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected:
    raise SystemExit(f'unexpected PASS376 champion input sha256: {actual}')

old = """  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp
"""
new = """  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity, Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp
"""
count = text.count(old)
if count != 1:
    raise SystemExit(f'31725 derivative-unfold repair expected once, found {count}')
text = text.replace(old, new)

line_count = len(text.splitlines())
if line_count != 60453:
    raise SystemExit(f'line-count drift: {line_count}, expected 60453')

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('lines=' + str(line_count))
print('repairs=1')
