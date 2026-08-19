#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

INPUT_SHA256 = '214800658b1de6c5685947061e9483fb65a803db0e0f4145ea27cc15e4dd28b6'
OLD1 = '''  simp only [actualFixedPhaseCuspHorocyclePoint,
    actualFixedPhaseHorizontalHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [div_eq_mul_inv]
  apply ContDiff.mul
  · fun_prop
  · apply ContDiff.inv
    · fun_prop
    · exact hden
'''
NEW1 = '''  simp only [actualFixedPhaseCuspHorocyclePoint,
    actualFixedPhaseHorizontalHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · exact hden
'''
OLD2 = '''  change ContDiff ℝ ∞
    (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
      fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))
  exact hcomp
'''
NEW2 = '''  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_def] using hcomp
'''

def blob(raw: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()

def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit('usage: qym_probe40b_horocycle_patch.py QYM.lean [result.json]')
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != INPUT_SHA256:
        raise SystemExit(f'input SHA mismatch: expected {INPUT_SHA256}, got {actual}')
    text = raw.decode('utf-8')
    if text.count(OLD1) != 1:
        raise SystemExit(f'OLD1 count {text.count(OLD1)}')
    if text.count(OLD2) != 1:
        raise SystemExit(f'OLD2 count {text.count(OLD2)}')
    text = text.replace(OLD1, NEW1, 1).replace(OLD2, NEW2, 1)
    path.write_text(text, encoding='utf-8', newline='\n')
    result_raw = path.read_bytes()
    decoded = result_raw.decode('utf-8')
    forbidden = {
        'sorry': len(re.findall(r'\bsorry\b', decoded)),
        'admit': len(re.findall(r'\badmit\b', decoded)),
        'native_decide': len(re.findall(r'\bnative_decide\b', decoded)),
        'Lean.ofReduceBool': decoded.count('Lean.ofReduceBool'),
        'global_axiom': len(re.findall(r'(?m)^\s*axiom\s+', decoded)),
        'unsafe': len(re.findall(r'(?m)^\s*unsafe\s+', decoded)),
        'maxHeartbeats_zero': len(re.findall(r'set_option\s+maxHeartbeats\s+0\b', decoded)),
    }
    if any(forbidden.values()):
        raise SystemExit(f'forbidden token audit failed: {forbidden}')
    result = {
        'schema': 'qym-probe40b-horocycle-patch-v1',
        'input_sha256': actual,
        'candidate_qym_sha256': hashlib.sha256(result_raw).hexdigest(),
        'candidate_qym_blob': blob(result_raw),
        'bytes': len(result_raw),
        'lf': result_raw.count(b'\n'),
        'forbidden': forbidden,
    }
    if len(sys.argv) == 3:
        Path(sys.argv[2]).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
