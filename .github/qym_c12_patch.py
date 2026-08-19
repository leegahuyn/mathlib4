#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, sys

BASELINE_SHA256 = '830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217'
BASELINE_BLOB = 'e796aa6ae9f01965116902a9345ed69f81bcfc42'

REPLACEMENTS = [
('add', '''  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, huv]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, add_zero]
''', '''  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, naturalStageSet,
      Set.indicator_of_mem hx, huv, Pi.add_apply]
  · simp only [globalStageProjectionRepresentative, naturalStageSet,
      Set.indicator_of_notMem hx, huv, Pi.add_apply, add_zero]
'''),
('smul', '''  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, hcu]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, smul_zero]
''', '''  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, naturalStageSet,
      Set.indicator_of_mem hx, hcu, Pi.smul_apply]
  · simp only [globalStageProjectionRepresentative, naturalStageSet,
      Set.indicator_of_notMem hx, hcu, Pi.smul_apply, smul_zero]
'''),
('density_le', '''  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
''', '''  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, naturalStageSet, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, naturalStageSet, hx]
'''),
('eventually_zero', '''  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hn]
''', '''  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, naturalStageSet, hn]
'''),
('tendsto_pointwise', '''  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hx]
''', '''  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, naturalStageSet, hx]
'''),
]

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
    if len(sys.argv) != 2:
        raise SystemExit('usage: qym_c12_patch.py QYM.lean')
    path = Path(sys.argv[1])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASELINE_SHA256 or blob(before) != BASELINE_BLOB:
        raise SystemExit('GB88 authority mismatch')
    text = before.decode('utf-8')
    before_audit = audit(text)
    for label, old, new in REPLACEMENTS:
        count = text.count(old)
        if count != 1:
            raise SystemExit(f'{label} replacement count={count}, expected 1')
        text = text.replace(old, new, 1)
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f'forbidden-token delta: {before_audit} -> {after_audit}')
    path.write_text(text, encoding='utf-8')
    after = path.read_bytes()
    print(json.dumps({
        'schema': 'qym-c12-v1',
        'variant': 'unfold_natural_stage',
        'input_sha256': BASELINE_SHA256,
        'input_blob': BASELINE_BLOB,
        'candidate_sha256': hashlib.sha256(after).hexdigest(),
        'candidate_blob': blob(after),
        'bytes': len(after),
        'lf': after.count(b'\n'),
        'fixed_producers_targeted': [
            'globalStageProjection_add',
            'globalStageProjection_smul',
            'globalStageProjectionErrorDensity_le',
            'globalStageProjectionErrorDensity_eventually_zero',
            'globalStageProjectionErrorDensity_tendsto_pointwise'
        ],
        'forbidden_before': before_audit,
        'forbidden_after': after_audit,
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
