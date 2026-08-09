from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected = '9aab0df48bcf864302e004c7b3032c4f2dcc470f55aaf7bf03077e397d14090b'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected:
    raise SystemExit(f'unexpected input sha256: {actual}')

needle = """variable [CompleteSpace H₀] [CompleteSpace HR] [CompleteSpace HL]

/-- Isometric closure of the graph range inside the Hilbert direct sum. -/
"""
replacement = """variable [CompleteSpace H₀] [CompleteSpace HR] [CompleteSpace HL]

/-- Keep every declaration in the completed-graph section on the canonical
`UniformSpace.Completion` normed-space instance.  This prevents elaboration
from alternating between the direct completion instance and the normed-space
parent projected from the completion inner-product instance. -/
local instance completionNormedSpace : NormedSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange

/-- Isometric closure of the graph range inside the Hilbert direct sum. -/
"""
if text.count(needle) != 1:
    raise SystemExit(f'section insertion expected once, found {text.count(needle)}')
text = text.replace(needle, replacement)

old = """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion :=
  innerSLFlip ℂ
"""
new = """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion :=
  (innerSLFlip ℂ :
    Q.SobolevCompletion →L[ℂ] StrongAntiDual Q.SobolevCompletion)
"""
if text.count(old) != 1:
    raise SystemExit(f'energy operator annotation expected once, found {text.count(old)}')
text = text.replace(old, new)

path.write_text(text, encoding='utf-8')
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('repairs=2')
