#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"

REAL_MULTIPLE_RE = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  rw [hyperbolicRightNormal,
    show star v *
        ((((y / ‖(((s : ℝ) : ℂ) * v)‖ : ℝ) : ℂ) * (-Complex.I)) *
          (((s : ℝ) : ℂ) * v)) =
      (((((y / ‖(((s : ℝ) : ℂ) * v)‖ : ℝ) : ℂ) *
          ((s : ℝ) : ℂ)) * (-Complex.I)) * (star v * v)) by ring,
    ← Complex.normSq_eq_conj_mul_self]
  simp [Complex.mul_re]
'''

SIGNED_AREA = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
      (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * (star w * w) by ring,
    ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im,
    neg_zero, zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub]
  rw [Complex.normSq_eq_norm_sq]
  field_simp [hn]
  <;> ring
'''

RE_REAL = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_realMultiple_re\b.*?"
    r"(?=^/-- Exact signed-area formula)"
)
RE_IM = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?"
    r"(?=^/-! ## 2\.)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode() + b"\0" + data
    ).hexdigest()


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
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_patch_gb85_c05_normal.py QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("GB85 SHA256 mismatch")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("GB85 Git blob mismatch")
    text = before.decode("utf-8")
    before_audit = audit(text)
    text, n_real = RE_REAL.subn(REAL_MULTIPLE_RE.rstrip() + "\n\n", text)
    text, n_im = RE_IM.subn(SIGNED_AREA.rstrip() + "\n\n", text)
    if n_real != 1 or n_im != 1:
        raise SystemExit(f"replacement counts: real={n_real}, im={n_im}")
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    print(json.dumps({
        "schema": "qym-gb85-c05-normal-v1",
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
