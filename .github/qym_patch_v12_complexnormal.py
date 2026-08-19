#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

REAL_RE = re.compile(
    r'(?ms)^theorem conj_mul_hyperbolicRightNormal_realMultiple_re\b.*?'
    r'(?=^/-- Exact signed-area formula for the right normal\.)'
)
IM_RE = re.compile(
    r'(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?'
    r'(?=^/-! ## 2\. The actual geometric normal and its three unconditional laws)'
)

REAL_FACTOR = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  have hvstar : star v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' v
  rw [hyperbolicRightNormal,
    show star v *
        ((((y / ‖(((s : ℝ) : ℂ) * v)‖ : ℝ) : ℂ) * (-Complex.I)) *
          (((s : ℝ) : ℂ) * v)) =
      ((((y / ‖(((s : ℝ) : ℂ) * v)‖ : ℝ) : ℂ) * ((s : ℝ) : ℂ)) *
          (-Complex.I)) * (star v * v) by ring,
    hvstar]
  simp [Complex.mul_re]
'''

REAL_GENERALIZE = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  rw [hyperbolicRightNormal]
  generalize y / ‖(((s : ℝ) : ℂ) * v)‖ = a
  have hvstar : star v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' v
  rw [show star v *
        ((((a : ℝ) : ℂ) * (-Complex.I)) * (((s : ℝ) : ℂ) * v)) =
      ((((a : ℝ) : ℂ) * ((s : ℝ) : ℂ)) * (-Complex.I)) *
        (star v * v) by ring,
    hvstar]
  simp [Complex.mul_re]
'''

REAL_CASES = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  by_cases hs : s = 0
  · simp [hs, hyperbolicRightNormal]
  · have h :=
      conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
    have hscale :
        star (((s : ℝ) : ℂ) * v) = ((s : ℝ) : ℂ) * star v := by
      simp [Complex.star_def]
    rw [hscale, mul_assoc] at h
    have hsMul :
        s * (star v *
          hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
      simpa [Complex.mul_re] using h
    exact (mul_eq_zero.mp hsMul).resolve_left hs
'''

IM_FACTOR = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hwstar : star w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' w
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hwstar]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, neg_zero, mul_zero, zero_mul,
    sub_zero, zero_sub, add_zero]
  field_simp [hn]
  ring
'''

IM_COMPONENT = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hwEq : star w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' w
  have hwRe : (star w * w).re = ‖w‖ ^ 2 := by
    simpa using congrArg Complex.re hwEq
  have hwIm : (star w * w).im = 0 := by
    simpa using congrArg Complex.im hwEq
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, neg_zero, mul_zero, zero_mul,
    sub_zero, zero_sub, add_zero]
  rw [hwRe, hwIm]
  field_simp [hn]
  ring
'''

VARIANTS = {
    'factor_normsq': (REAL_FACTOR, IM_FACTOR),
    'generalize_normsq': (REAL_GENERALIZE, IM_FACTOR),
    'cases_components': (REAL_CASES, IM_COMPONENT),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


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


def replace_one(pattern, replacement: str, text: str, label: str) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f'expected one {label}, found {len(matches)}')
    match = matches[0]
    return text[:match.start()] + replacement.rstrip() + '\n\n' + text[match.end():]


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: qym_patch_v12_complexnormal.py VARIANT QYM.lean [EXPECTED_SHA256]')
    variant, filename = sys.argv[1], sys.argv[2]
    expected_sha = sys.argv[3] if len(sys.argv) == 4 else None
    if variant not in VARIANTS:
        raise SystemExit(f'unknown variant {variant!r}')
    path = Path(filename)
    before = path.read_bytes()
    if expected_sha is not None and sha256(before) != expected_sha:
        raise SystemExit(f'unexpected input SHA256: {sha256(before)} != {expected_sha}')
    text = before.decode('utf-8')
    before_audit = audit(text)
    real_block, im_block = VARIANTS[variant]
    text = replace_one(REAL_RE, real_block, text, 'real-multiple theorem')
    text = replace_one(IM_RE, im_block, text, 'signed-area theorem')
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f'forbidden-token delta: {before_audit} -> {after_audit}')
    path.write_text(text, encoding='utf-8')
    after = path.read_bytes()
    marker = 'theorem actualOutwardHyperbolicUnitNormal_norm'
    marker_index = text.find(marker)
    if marker_index < 0:
        marker = '/-! ## 2. The actual geometric normal and its three unconditional laws -/'
        marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit('post-V12 gate marker missing')
    print(json.dumps({
        'schema': 'qym-v12-complexnormal-patch-v1',
        'variant': variant,
        'input_sha256': sha256(before),
        'input_blob': git_blob(before),
        'candidate_sha256': sha256(after),
        'candidate_blob': git_blob(after),
        'bytes': len(after),
        'lf': after.count(b'\n'),
        'gate_line': text.count('\n', 0, marker_index) + 1,
        'forbidden': after_audit,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
