#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, sys

BASELINE_SHA256 = '830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217'
BASELINE_BLOB = 'e796aa6ae9f01965116902a9345ed69f81bcfc42'
VARIANTS = {'ofReal_pow', 'change_rfl', 'norm_cast'}

OLD = '''@[simp]
theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
'''

VARIANT_PROOFS = {
'ofReal_pow': '''@[simp]
theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow, Complex.ofReal_re]
''',
'change_rfl': '''@[simp]
theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  change
    ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2
  rfl
''',
'norm_cast': '''@[simp]
theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_cast
''',
}

def blob(raw: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()

def audit(text: str) -> dict[str, int]:
    return {
        'sorry': len(re.findall(r'\bsorry\b', text)),
        'admit': len(re.findall(r'\badmit\b', text)),
        'native_decide': len(re.findall(r'\bnative_decide\b', text)),
        'Lean.ofReduceBool': text.count('Lean.ofReduceBool'),
        'global_axiom': len(re.findall(r'(?m)^\s*axiom\s+', text)),
        'unsafe': len(re.findall(r'(?m)^\s*unsafe\s+', text)),
        'maxHeartbeats_zero': len(re.findall(r'set_option\s+maxHeartbeats\s+0\b', text)),
    }

def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit('usage: qym_c13_variants.py VARIANT QYM.lean')
    variant = sys.argv[1]
    path = Path(sys.argv[2])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASELINE_SHA256 or blob(before) != BASELINE_BLOB:
        raise SystemExit('GB88 authority mismatch')
    text = before.decode('utf-8')
    before_audit = audit(text)
    count = text.count(OLD)
    if count != 1:
        raise SystemExit(f'C13 replacement count={count}, expected 1')
    text = text.replace(OLD, VARIANT_PROOFS[variant], 1)
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f'forbidden-token delta: {before_audit} -> {after_audit}')
    path.write_text(text, encoding='utf-8')
    after = path.read_bytes()
    print(json.dumps({
        'schema': 'qym-c13-v1',
        'variant': variant,
        'input_sha256': BASELINE_SHA256,
        'input_blob': BASELINE_BLOB,
        'candidate_sha256': hashlib.sha256(after).hexdigest(),
        'candidate_blob': blob(after),
        'bytes': len(after),
        'lf': after.count(b'\n'),
        'fixed_producers_targeted': ['coordinateHamiltonianForm_re_self'],
        'forbidden_before': before_audit,
        'forbidden_after': after_audit,
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
