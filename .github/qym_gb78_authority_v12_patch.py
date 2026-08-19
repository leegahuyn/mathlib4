#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "1a1abeeb248031cd91577034329944caab08fd9f9e6c70f7a913c1dd66e0e714"
BASE_BLOB = "029620c5d7085dbc7a11c8eaaa485a67fe9312fe"

C8_DIRECT_INV = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im] <;> ring
'''

C8_DIRECT_NORM = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, norm_mul, Real.norm_eq_abs] <;> ring
'''

C8_STRUCTURAL = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  by_cases hs : s = 0
  · subst s
    simp [hyperbolicRightNormal]
  · have horth :=
      conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
    have hscaled :
        s * (star v *
          hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
      simpa [map_mul, Complex.star_def, Complex.mul_re,
        mul_assoc, mul_comm, mul_left_comm] using horth
    exact (mul_eq_zero.mp hscaled).resolve_left hs
'''

C8_STRUCTURAL_RW = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  by_cases hs : s = 0
  · subst s
    simp [hyperbolicRightNormal]
  · have horth :=
      conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
    have hstar :
        star (((s : ℝ) : ℂ) * v) = ((s : ℝ) : ℂ) * star v := by
      simp [map_mul, Complex.star_def, mul_comm]
    rw [hstar] at horth
    have hscaled :
        s * (star v *
          hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
      simpa [Complex.mul_re, mul_assoc] using horth
    exact (mul_eq_zero.mp hscaled).resolve_left hs
'''

C9_NORMSQ = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn] <;> ring
'''

C9_NORM_SQ_CAST = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
  simp [Complex.mul_im]
  field_simp [hn] <;> ring
'''

C9_NORMSQ_FIELD = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    simpa only [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
  change -(y / ‖w‖) * Complex.normSq w = -y * ‖w‖
  rw [Complex.normSq_eq_norm_sq]
  field_simp [hn] <;> ring
'''

C8_VARIANTS = {
    "direct_inv": C8_DIRECT_INV,
    "direct_norm": C8_DIRECT_NORM,
    "structural": C8_STRUCTURAL,
    "structural_rw": C8_STRUCTURAL_RW,
}

C9_VARIANTS = {
    "normsq": C9_NORMSQ,
    "norm_sq_cast": C9_NORM_SQ_CAST,
    "normsq_field": C9_NORMSQ_FIELD,
}

VARIANTS = {
    **{f"{c8}_only": (c8, None) for c8 in C8_VARIANTS},
    "direct_inv_normsq": ("direct_inv", "normsq"),
    "direct_inv_norm_sq_cast": ("direct_inv", "norm_sq_cast"),
    "direct_inv_normsq_field": ("direct_inv", "normsq_field"),
    "direct_norm_normsq": ("direct_norm", "normsq"),
    "direct_norm_norm_sq_cast": ("direct_norm", "norm_sq_cast"),
    "structural_normsq": ("structural", "normsq"),
    "structural_normsq_field": ("structural", "normsq_field"),
    "structural_rw_normsq": ("structural_rw", "normsq"),
}

C8_RE = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_realMultiple_re\b.*?"
    r"(?=^/-- Exact signed-area formula)"
)
C9_RE = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?"
    r"(?=^/-! ## 2\. The actual geometric normal)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def replace_one(text: str, pattern: re.Pattern[str], replacement: str, label: str) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"{label}: expected one match, found {len(matches)}")
    m = matches[0]
    return text[:m.start()] + replacement.rstrip() + "\n\n" + text[m.end():]


def line_of(text: str, needle: str) -> int:
    pos = text.index(needle)
    return text.count("\n", 0, pos) + 1


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: qym_gb78_authority_v12_patch.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("unexpected authoritative GB78 input SHA256")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected authoritative GB78 input blob")
    text = before.decode("utf-8")
    before_audit = audit(text)
    c8_key, c9_key = VARIANTS[variant]
    text = replace_one(text, C8_RE, C8_VARIANTS[c8_key], "C8 real-multiple theorem")
    if c9_key is not None:
        text = replace_one(text, C9_RE, C9_VARIANTS[c9_key], "C9 signed-area theorem")
        gate_marker = "/-! ## 2. The actual geometric normal and its three unconditional laws -/"
    else:
        gate_marker = "theorem conj_mul_hyperbolicRightNormal_im"
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden proof-escape delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    decoded = after.decode("utf-8")
    print(json.dumps({
        "schema": "qym-gb78-authority-v12-patch-v1",
        "variant": variant,
        "c8_strategy": c8_key,
        "c9_strategy": c9_key,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": line_of(decoded, gate_marker),
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
