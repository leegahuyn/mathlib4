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
    Complex.inv_re, Complex.inv_im]
  ring
'''

C8_DIRECT_INV_NF = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im]
  ring_nf
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
  field_simp [hn]
  ring
'''

C9_NORMSQ_CALC = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
  simp [Complex.mul_im]
  field_simp [hn]
  ring
'''

C8_VARIANTS = {
    "direct_inv": C8_DIRECT_INV,
    "direct_inv_nf": C8_DIRECT_INV_NF,
    "structural_rw": C8_STRUCTURAL_RW,
}

VARIANTS: dict[str, tuple[str, str | None]] = {
    "c8_direct_inv": ("direct_inv", None),
    "c8_direct_inv_nf": ("direct_inv_nf", None),
    "c8_structural_rw": ("structural_rw", None),
    "c8_direct_inv_c9_normsq": ("direct_inv", C9_NORMSQ),
    "c8_direct_inv_nf_c9_normsq": ("direct_inv_nf", C9_NORMSQ),
    "c8_structural_rw_c9_normsq": ("structural_rw", C9_NORMSQ),
    "c8_direct_inv_c9_normsq_calc": ("direct_inv", C9_NORMSQ_CALC),
    "c8_structural_rw_c9_normsq_calc": ("structural_rw", C9_NORMSQ_CALC),
}

C8_RE = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_realMultiple_re\b.*?"
    r"(?=^/-- Exact signed-area formula)"
)
C9_RE = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?"
    r"(?=^/-! ## 2\. The actual geometric normal)"
)
C9_START_RE = re.compile(r"(?m)^theorem conj_mul_hyperbolicRightNormal_im\b")
NEXT_SECTION_RE = re.compile(
    r"(?m)^/-! ## 2\. The actual geometric normal and its three unconditional laws -/"
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
    match = matches[0]
    return text[: match.start()] + replacement.rstrip() + "\n\n" + text[match.end() :]


def line_of(text: str, match: re.Match[str]) -> int:
    return text.count("\n", 0, match.start()) + 1


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            "usage: qym_gb78_authority_v12_patch.py VARIANT PrimalitySheafVerification/QYM.lean\n"
            f"variants: {', '.join(sorted(VARIANTS))}"
        )

    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    before = path.read_bytes()
    before_sha = hashlib.sha256(before).hexdigest()
    before_blob = git_blob(before)
    if before_sha != BASE_SHA256:
        raise SystemExit(f"unexpected exact-GB78 input SHA256: {before_sha}")
    if before_blob != BASE_BLOB:
        raise SystemExit(f"unexpected exact-GB78 input blob: {before_blob}")

    c8_name, c9_proof = VARIANTS[variant]
    text = before.decode("utf-8")
    before_audit = audit(text)
    text = replace_one(text, C8_RE, C8_VARIANTS[c8_name], "real-multiple theorem")
    if c9_proof is not None:
        text = replace_one(text, C9_RE, c9_proof, "signed-area theorem")

    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden proof-escape delta: {before_audit} -> {after_audit}")

    if c9_proof is None:
        gate_match = C9_START_RE.search(text)
        gate_label = "C9 theorem start"
    else:
        gate_match = NEXT_SECTION_RE.search(text)
        gate_label = "post-C9 section start"
    if gate_match is None:
        raise SystemExit(f"missing local-gate marker: {gate_label}")

    path.write_text(text, encoding="utf-8", newline="\n")
    after = path.read_bytes()
    decoded = after.decode("utf-8")
    if decoded != text:
        raise SystemExit("candidate write/read mismatch")

    result = {
        "schema": "qym-exact-gb78-authority-v12-patch-v1",
        "variant": variant,
        "c8_strategy": c8_name,
        "c9_strategy": "unchanged" if c9_proof is None else (
            "normsq_calc" if c9_proof == C9_NORMSQ_CALC else "normsq"
        ),
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": line_of(text, gate_match),
        "gate_label": gate_label,
        "forbidden_before": before_audit,
        "forbidden_after": after_audit,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
