#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import importlib.util
import json
import sys

OLD_PATH = Path('.github/qym_patch_gb83_v10_normalize4.py')
spec = importlib.util.spec_from_file_location('qym_v10_old_patcher', OLD_PATH)
if spec is None or spec.loader is None:
    raise SystemExit('cannot load V10 patcher')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)

BASE_SHA256 = old.BASE_SHA256
BASE_BLOB = old.BASE_BLOB
BASE_EDGE = old.PREFIX + old.CIRCULAR_RW + old.VERTICALS

DET_HEAD = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  letI : AddCommGroup ℂ := Complex.addCommGroup
  have hdet : (selectedRepresentativeRealMatrix q).val.det = 1 := by
    simpa [selectedRepresentativeRealMatrix] using
      (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
        SL(2, ℝ)).det_coe
  have hpos : 0 < (selectedRepresentativeRealMatrix q).val.det := by
    rw [hdet]
    norm_num
  have hraw :=
    UpperHalfPlane.hasStrictDerivAt_smul
      (g := selectedRepresentativeRealMatrix q) hpos z
'''

VARIANTS = {
    'rw_det_coe': DET_HEAD + r'''  have hchart :
      selectedRepresentativeChart q =
        (fun w : ℂ =>
          ((selectedRepresentativeRealMatrix q • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) := by
    funext w
    change
      ((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q •
          UpperHalfPlane.ofComplex w : ℍ) : ℂ) =
        ((selectedRepresentativeRealMatrix q • UpperHalfPlane.ofComplex w : ℍ) : ℂ)
    rw [MulAction.compHom_smul_def]
    rfl
  rw [hchart]
  rw [hdet] at hraw
  simpa [selectedRepresentativeDenom] using hraw
''',
    'rw_det_change': DET_HEAD + r'''  have hchart :
      selectedRepresentativeChart q =
        (fun w : ℂ =>
          ((selectedRepresentativeRealMatrix q • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) := by
    funext w
    simp only [selectedRepresentativeChart, selectedRepresentativeCoordinate]
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
    rfl
  rw [hchart]
  rw [hdet] at hraw
  simpa [selectedRepresentativeDenom] using hraw
''',
    'congr_det_gl': DET_HEAD + r'''  have hchart :
      selectedRepresentativeChart q =
        (fun w : ℂ =>
          ((selectedRepresentativeRealMatrix q • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) := by
    funext w
    simp only [selectedRepresentativeChart, selectedRepresentativeCoordinate]
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
    simp [selectedRepresentativeRealMatrix, UpperHalfPlane.num, UpperHalfPlane.denom]
  rw [hchart]
  rw [hdet] at hraw
  simpa [selectedRepresentativeDenom] using hraw
''',
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def replace_one(pattern, replacement: str, text: str, label: str) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f'expected one {label}, found {len(matches)}')
    match = matches[0]
    return text[:match.start()] + replacement.rstrip() + '\n\n' + text[match.end():]


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit('usage: qym_patch_gb83_v10_1_chartbridge.py VARIANT QYM.lean')
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f'unknown variant {variant!r}')
    path = Path(filename)
    before = path.read_bytes()
    if sha256(before) != BASE_SHA256 or git_blob(before) != BASE_BLOB:
        raise SystemExit('unexpected GB83 baseline')
    text = before.decode('utf-8')
    before_audit = old.audit(text)
    text = replace_one(old.BASE_RE, BASE_EDGE, text, 'base-edge theorem')
    text = replace_one(old.DET_RE, VARIANTS[variant], text, 'chart derivative theorem')
    after_audit = old.audit(text)
    if after_audit != before_audit:
        raise SystemExit(f'forbidden-token delta: {before_audit} -> {after_audit}')
    path.write_text(text, encoding='utf-8')
    after = path.read_bytes()
    marker = 'theorem edgeParameterTransport_hasDerivAt'
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit('V11 gate marker missing')
    print(json.dumps({
        'schema': 'qym-gb83-v10-1-chartbridge-patch-v1',
        'variant': variant,
        'input_sha256': BASE_SHA256,
        'input_blob': BASE_BLOB,
        'candidate_sha256': sha256(after),
        'candidate_blob': git_blob(after),
        'bytes': len(after),
        'lf': after.count(b'\n'),
        'gate_line': text.count('\n', 0, marker_index) + 1,
        'forbidden': after_audit,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
