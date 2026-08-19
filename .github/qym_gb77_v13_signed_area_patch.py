#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd"
BASE_BLOB = "c6e8883353b350f22b7f48d955fc5cfa4e61f88f"

COMMON_HSTAR = r'''  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
'''

RW_PREFIX = r'''  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
'''

PROOFS: dict[str, str] = {}

PROOFS["rw_ofReal_pow"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
''' + COMMON_HSTAR + RW_PREFIX + r'''  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn]
  rw [← Complex.ofReal_pow]
  simp
'''

PROOFS["simpa_ofReal_pow"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
''' + COMMON_HSTAR + RW_PREFIX + r'''  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn]
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re]
'''

PROOFS["pow_two_mul_re"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
''' + COMMON_HSTAR + RW_PREFIX + r'''  simp [Complex.mul_im, Complex.normSq_eq_norm_sq,
    pow_two, Complex.mul_re]
  field_simp [hn] <;> ring
'''

PROOFS["norm_num_pow_two"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
''' + COMMON_HSTAR + RW_PREFIX + r'''  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn]
  norm_num [pow_two, Complex.mul_re]
'''

PROOFS["hpow_re"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hpow_re : (((‖w‖ : ℂ) ^ 2).re) = ‖w‖ ^ 2 := by
    rw [← Complex.ofReal_pow]
    simp
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
''' + RW_PREFIX + r'''  simp [Complex.mul_im, Complex.normSq_eq_norm_sq, hpow_re]
  field_simp [hn] <;> ring
'''

PROOFS["hstar_real_sq"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    calc
      star w * w = (Complex.normSq w : ℂ) := by
        simpa [Complex.star_def] using
          (Complex.normSq_eq_conj_mul_self (z := w)).symm
      _ = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
        rw [Complex.normSq_eq_norm_sq]
''' + RW_PREFIX + r'''  simp [Complex.mul_im]
  field_simp [hn] <;> ring
'''

PROOFS["hstar_real_sq_only"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    calc
      star w * w = (Complex.normSq w : ℂ) := by
        simpa only [Complex.star_def] using
          (Complex.normSq_eq_conj_mul_self (z := w)).symm
      _ = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
        norm_num [Complex.normSq_eq_norm_sq]
''' + RW_PREFIX + r'''  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  field_simp [hn] <;> ring
'''

PROOFS["calc_normsq"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  calc
    (star w * hyperbolicRightNormal y w).im =
        -(y / ‖w‖) * Complex.normSq w := by
      rw [hyperbolicRightNormal,
        show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
            (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
              (star w * w) by ring,
        hstar]
      simp [Complex.mul_im]
    _ = -y * ‖w‖ := by
      rw [Complex.normSq_eq_norm_sq]
      field_simp [hn] <;> ring
'''

PROOFS["calc_real_sq"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    calc
      star w * w = (Complex.normSq w : ℂ) := by
        simpa [Complex.star_def] using
          (Complex.normSq_eq_conj_mul_self (z := w)).symm
      _ = (((‖w‖ ^ 2 : ℝ) : ℂ)) := by
        rw [Complex.normSq_eq_norm_sq]
  calc
    (star w * hyperbolicRightNormal y w).im =
        -(y / ‖w‖) * (‖w‖ ^ 2) := by
      rw [hyperbolicRightNormal,
        show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
            (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
              (star w * w) by ring,
        hstar]
      simp [Complex.mul_im]
    _ = -y * ‖w‖ := by
      field_simp [hn] <;> ring
'''

PROOFS["rw_ring_nf_ofReal"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
''' + COMMON_HSTAR + RW_PREFIX + r'''  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn]
  ring_nf
  rw [← Complex.ofReal_pow]
  simp
'''

PROOFS["rw_norm_num"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
''' + COMMON_HSTAR + RW_PREFIX + r'''  norm_num [Complex.mul_im, Complex.normSq_eq_norm_sq,
    pow_two, Complex.mul_re]
  field_simp [hn] <;> ring
'''

PROOFS["change_after_simp"] = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
''' + COMMON_HSTAR + RW_PREFIX + r'''  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  change -(y / ‖w‖) * Complex.normSq w = -y * ‖w‖
  rw [Complex.normSq_eq_norm_sq]
  field_simp [hn] <;> ring
'''

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


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in PROOFS:
        raise SystemExit("usage: qym_gb77_v13_signed_area_patch.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("unexpected exact GB77 input SHA256")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected exact GB77 input blob")
    text = before.decode("utf-8")
    before_audit = audit(text)
    matches = list(C9_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"C9 theorem: expected one match, found {len(matches)}")
    m = matches[0]
    text = text[:m.start()] + PROOFS[variant].rstrip() + "\n\n" + text[m.end():]
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden proof-escape delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    decoded = after.decode("utf-8")
    marker = "/-! ## 2. The actual geometric normal and its three unconditional laws -/"
    gate_line = decoded.count("\n", 0, decoded.index(marker)) + 1
    print(json.dumps({
        "schema": "qym-gb77-v13-signed-area-patch-v1",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": gate_line,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
