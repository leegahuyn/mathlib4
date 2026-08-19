#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, sys

VARIANTS = {
    'cases_simpa_conj_mul',
    'cases_explicit_conj_mul',
    'cases_simpa_normsq',
    'cases_explicit_normsq',
}

OLD_REAL = '''/-- The same right normal is orthogonal to `v` when the oriented vector is
any real multiple `s v`. -/
theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im]
  ring_nf

'''

OLD_IM = '''/-- Exact signed-area formula for the right normal. -/
theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub,
    pow_two]
  field_simp [hn]
  <;> ring_nf

'''

REAL_CASES_SIMPA = '''/-- The same right normal is orthogonal to `v` when the oriented vector is
any real multiple `s v`. -/
theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  by_cases hs : s = 0
  · subst s
    simp [hyperbolicRightNormal]
  · have h :=
      conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
    have hsMul :
        s * (star v *
          hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
      simpa [Complex.star_def, Complex.mul_re, mul_assoc] using h
    exact (mul_eq_zero.mp hsMul).resolve_left hs

'''

REAL_CASES_EXPLICIT = '''/-- The same right normal is orthogonal to `v` when the oriented vector is
any real multiple `s v`. -/
theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  by_cases hs : s = 0
  · subst s
    simp [hyperbolicRightNormal]
  · have h :=
      conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
    have hscale :
        star (((s : ℝ) : ℂ) * v) =
          ((s : ℝ) : ℂ) * star v := by
      change conj (((s : ℝ) : ℂ) * v) =
        ((s : ℝ) : ℂ) * conj v
      simp
    rw [hscale, mul_assoc] at h
    have hsMul :
        s * (star v *
          hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
      simpa [Complex.mul_re] using h
    exact (mul_eq_zero.mp hsMul).resolve_left hs

'''

IM_CONJ_MUL = '''/-- Exact signed-area formula for the right normal. -/
theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar :
      star w * w = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    simpa [Complex.star_def] using (Complex.conj_mul' w)
  calc
    (star w * hyperbolicRightNormal y w).im =
        (((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (((‖w‖ ^ 2 : ℝ) : ℂ)))).im := by
          rw [hyperbolicRightNormal,
            show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
                (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
                  (star w * w) by ring,
            hstar]
    _ = -(y / ‖w‖) * (‖w‖ ^ 2) := by
          simp [Complex.mul_re, Complex.mul_im]
    _ = -y * ‖w‖ := by
          field_simp [hn]
          <;> ring

'''

IM_NORMSQ = '''/-- Exact signed-area formula for the right normal. -/
theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar :
      star w * w = (Complex.normSq w : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  calc
    (star w * hyperbolicRightNormal y w).im =
        (((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (Complex.normSq w : ℂ))).im := by
          rw [hyperbolicRightNormal,
            show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
                (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
                  (star w * w) by ring,
            hstar]
    _ = -(y / ‖w‖) * Complex.normSq w := by
          simp [Complex.mul_re, Complex.mul_im]
    _ = -y * ‖w‖ := by
          rw [Complex.normSq_eq_norm_sq]
          field_simp [hn]
          <;> ring

'''


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
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


def main() -> None:
    if len(sys.argv) != 4 or sys.argv[1] not in VARIANTS:
        raise SystemExit('usage: patch.py VARIANT QYM.lean EXPECTED_SHA256')
    variant, path, expected = sys.argv[1], Path(sys.argv[2]), sys.argv[3]
    before = path.read_bytes()
    if sha(before) != expected:
        raise SystemExit(f'unexpected input sha {sha(before)} != {expected}')
    text = before.decode('utf-8')
    if text.count(OLD_REAL) != 1 or text.count(OLD_IM) != 1:
        raise SystemExit(f'block counts real={text.count(OLD_REAL)} im={text.count(OLD_IM)}')
    a0 = audit(text)
    real = REAL_CASES_EXPLICIT if 'explicit' in variant else REAL_CASES_SIMPA
    imag = IM_NORMSQ if variant.endswith('normsq') else IM_CONJ_MUL
    text = text.replace(OLD_REAL, real, 1).replace(OLD_IM, imag, 1)
    a1 = audit(text)
    if a1 != a0:
        raise SystemExit(f'forbidden delta {a0} -> {a1}')
    path.write_text(text, encoding='utf-8')
    after = path.read_bytes()
    marker = '/-! ## 2. The actual geometric normal and its three unconditional laws -/'
    if marker not in text:
        raise SystemExit('gate marker missing')
    print(json.dumps({
        'schema': 'qym-v15-complexnormal-patch-v1',
        'variant': variant,
        'input_sha256': sha(before),
        'input_blob': blob(before),
        'candidate_sha256': sha(after),
        'candidate_blob': blob(after),
        'gate_line': text.count('\n', 0, text.index(marker)) + 1,
        'forbidden': a1,
        'bytes': len(after),
        'lf': after.count(b'\n'),
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
