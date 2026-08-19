#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "1a45a5cad7243eab3ad276f6add587a3a890819ecee30ef689d2295364db41b4"
BASE_BLOB = "1d9a5b94f7f7a02a996fbeced521c915194d751d"

C8_DIRECT = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im]
  ring
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

C9_HSTAR = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
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
  field_simp [hn]
  ring
'''

VARIANTS = {
    "direct_hstar": C8_DIRECT,
    "structural_hstar": C8_STRUCTURAL,
    "structural_rw_hstar": C8_STRUCTURAL_RW,
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


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: qym_gb78_v12_normal_patch.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("unexpected GB78 input SHA256")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected GB78 input blob")
    text = before.decode("utf-8")
    before_audit = audit(text)
    text = replace_one(text, C8_RE, VARIANTS[variant], "real-multiple normal theorem")
    text = replace_one(text, C9_RE, C9_HSTAR, "signed-area theorem")
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    decoded = after.decode("utf-8")
    marker = "/-! ## 2. The actual geometric normal and its three unconditional laws -/"
    gate_line = decoded.count("\n", 0, decoded.index(marker)) + 1
    print(json.dumps({
        "schema": "qym-gb78-v12-normal-patch-v1",
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
