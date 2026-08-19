#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA = "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd"
BASE_BLOB = "c6e8883353b350f22b7f48d955fc5cfa4e61f88f"
TARGET_START = "theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}"
TARGET_END = "\n\n/-! ## 2. The actual geometric normal and its three unconditional laws -/"

THEOREM_HEAD = """theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
"""

REASSOC = """  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring]
"""

COORD_SIMP = """  simp only [Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub, pow_two]
"""

PROOFS: dict[str, str] = {
    "normsq_rw": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  field_simp [hn]
  <;> ring
""",
    "normsq_have": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsq : star w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hsq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  field_simp [hn]
  <;> ring
""",
    "normsq_simpa": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsq : star w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.star_def, Complex.normSq_eq_norm_sq] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hsq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  field_simp [hn]
  <;> ring
""",
    "reassoc_star_coords": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
""" + REASSOC + COORD_SIMP + """  field_simp [hn]
  <;> ring
""",
    "direct_star_coords": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal]
""" + COORD_SIMP + """  field_simp [hn]
  <;> ring
""",
    "reassoc_broad_simp": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
""" + REASSOC + """  simp [Complex.mul_im, Complex.mul_re, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  <;> field_simp [hn]
  <;> ring
""",
    "normsq_simp_only": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
""" + REASSOC + """  simp only [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  field_simp [hn]
  <;> ring
""",
    "normsq_change": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsq : star w * w = ((Complex.normSq w : ℝ) : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
""" + REASSOC + """  rw [hsq, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  field_simp [hn]
  <;> ring
""",
    "original_plus_star": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
""" + REASSOC + """  simp only [Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub, pow_two]
  field_simp [hn]
  <;> ring_nf
  <;> ring
""",
    "normsq_ring_nf": """  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
""" + REASSOC + """  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp [Complex.mul_im]
  <;> field_simp [hn]
  <;> ring_nf
  <;> ring
""",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def main() -> None:
    if len(sys.argv) != 4 or sys.argv[1] not in PROOFS:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} VARIANT QYM.lean EXPECTED_SHA256")
    variant = sys.argv[1]
    path = Path(sys.argv[2])
    expected = sys.argv[3]
    before = path.read_bytes()
    if expected != BASE_SHA or sha(before) != BASE_SHA or blob(before) != BASE_BLOB:
        raise SystemExit(
            f"GB77 authority mismatch expected={expected} sha={sha(before)} blob={blob(before)}"
        )
    source = before.decode("utf-8")
    start = source.find(TARGET_START)
    end = source.find(TARGET_END, start)
    if start < 0 or end < 0:
        raise SystemExit("target theorem block not found")
    old = source[start:end]
    if old.count("field_simp [hn]") != 1 or "ring_nf" not in old:
        raise SystemExit("unexpected GB77 target theorem body")
    before_audit = audit(source)
    replacement = THEOREM_HEAD + PROOFS[variant].rstrip("\n")
    text = source[:start] + replacement + source[end:]
    after_audit = audit(text)
    if after_audit != before_audit or any(after_audit.values()):
        raise SystemExit(f"forbidden-token audit changed {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    target_start_line = text.count("\n", 0, start) + 1
    target_end_index = start + len(replacement)
    target_end_line = text.count("\n", 0, target_end_index) + 1
    next_decl_index = text.find("def actualOutwardHyperbolicUnitNormal", target_end_index)
    next_decl_line = text.count("\n", 0, next_decl_index) + 1 if next_decl_index >= 0 else target_end_line + 1
    print(json.dumps({
        "schema": "qym-gb77-v14-right-normal-im-patch-v1",
        "variant": variant,
        "input_sha256": sha(before),
        "input_blob": blob(before),
        "candidate_sha256": sha(after),
        "candidate_blob": blob(after),
        "target_declaration": "conj_mul_hyperbolicRightNormal_im",
        "target_start_line": target_start_line,
        "target_end_line": target_end_line,
        "next_declaration_line": next_decl_line,
        "forbidden": after_audit,
        "bytes": len(after),
        "lf": after.count(b"\n"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
