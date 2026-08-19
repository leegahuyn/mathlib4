#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd"
BASE_BLOB = "c6e8883353b350f22b7f48d955fc5cfa4e61f88f"

THEOREM_RE = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?"
    r"(?=^/-! ## 2\. The actual geometric normal)"
)

COMMON_PREFIX = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
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
'''

VARIANTS = {
    "normsq_simp_then_rw": COMMON_PREFIX + r'''  simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.normSq_eq_norm_sq]
  field_simp [hn] <;> ring
''',
    "mulre_pow2": COMMON_PREFIX + r'''  simp [Complex.mul_re, Complex.mul_im,
    Complex.normSq_eq_norm_sq, pow_two] <;>
    field_simp [hn] <;> ring
''',
    "norm_sq_cast": r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
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
  simp [Complex.mul_re, Complex.mul_im, pow_two] <;>
    field_simp [hn] <;> ring
''',
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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
    if len(sys.argv) != 4 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            "usage: qym_patch_gb77_v15.py VARIANT INPUT_QYM OUTPUT_QYM"
        )
    variant = sys.argv[1]
    source_path = Path(sys.argv[2])
    output_path = Path(sys.argv[3])
    before = source_path.read_bytes()
    if sha256(before) != BASE_SHA256 or git_blob(before) != BASE_BLOB:
        raise SystemExit(
            f"GB77 authority mismatch: sha={sha256(before)} blob={git_blob(before)}"
        )
    text = before.decode("utf-8")
    matches = list(THEOREM_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected one blocker theorem, found {len(matches)}")
    before_audit = audit(text)
    m = matches[0]
    replacement = VARIANTS[variant].rstrip() + "\n\n"
    patched = text[: m.start()] + replacement + text[m.end() :]
    after_audit = audit(patched)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(patched, encoding="utf-8")
    after = output_path.read_bytes()
    marker = "theorem conj_mul_hyperbolicRightNormal_im"
    line = patched.count("\n", 0, patched.index(marker)) + 1
    print(json.dumps({
        "schema": "qym-gb77-v15-candidate-v1",
        "status": "PREPARED_UNVERIFIED",
        "variant": variant,
        "baseline_error_headers": 77,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "blocker": "conj_mul_hyperbolicRightNormal_im",
        "blocker_line": line,
        "forbidden": after_audit,
        "bytes": len(after),
        "lf": after.count(b"\n"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
