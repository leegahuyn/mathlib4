from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    old = """              intro r v
              have hr : r • v = (r : ℂ) • v := rfl
              rw [hr, map_smulₛₗ]
              simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
                smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
                Complex.ofReal_im, zero_mul, sub_zero] }
"""
    new = """              intro r v
              have hr : r • v = (r : ℂ) • v := rfl
              rw [hr, map_smulₛₗ]
              change r * (F v).re - 0 * (F v).im = r * (F v).re
              ring }
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis compute real scalar anti-linearity componentwise")
    changed |= did

    old = """            intro r u v
            have hr : r • v = (r : ℂ) • v := rfl
            rw [hr, map_smulₛₗ]
            simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
              smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, zero_mul, sub_zero])
"""
    new = """            intro r u v
            have hr : r • v = (r : ℂ) • v := rfl
            rw [hr, map_smulₛₗ]
            change r * (B u v).re - 0 * (B u v).im = r * (B u v).re
            ring)
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis compute form anti-linearity componentwise")
    changed |= did

    old = """      have hI := h (Complex.I • v)
      simpa only [map_smulₛₗ, starRingEnd_apply, Complex.star_def,
        Complex.conj_I, smul_eq_mul] using hI
"""
    new = """      have hI := h (Complex.I • v)
      rw [map_smulₛₗ, map_smulₛₗ] at hI
      have hstar : starRingEnd ℂ Complex.I = -Complex.I := by
        ext <;> norm_num [starRingEnd_apply, Complex.star_def]
      rw [hstar] at hI
      simpa only [smul_eq_mul] using hI
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis recover imaginary parts without recursive simp")
    changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
