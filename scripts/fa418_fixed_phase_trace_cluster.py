from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
expected = '7c8cc3a0002b8e23de3230767278a46f0e718dabce2269f153908bbc75e4447d'
actual = hashlib.sha256(path.read_bytes()).hexdigest()
lines = len(path.read_text(encoding='utf-8').splitlines())
if actual != expected or lines != 60453:
    raise SystemExit(f'unexpected cumulative FA380 candidate: sha={actual} lines={lines}')
print('input_sha256=' + actual)
print('output_sha256=' + actual)
print('lines=' + str(lines))
print('repairs=0')
