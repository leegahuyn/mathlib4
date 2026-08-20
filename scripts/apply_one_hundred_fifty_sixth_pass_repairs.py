from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fifty_fifth_pass_repairs as pass155
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le (by exact le_top)
""",
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le
    (show (2 : WithTop ℕ) ≤ (⊤ : WithTop ℕ) from le_top)
""",
            1,
            "FunctionalAnalysis type the finite-to-infinite differentiability comparison",
        ),
        (
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by exact le_top)).iteratedFDeriv_cons
""",
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (show (max 2 2 : WithTop ℕ) ≤ (⊤ : WithTop ℕ) from le_top)).iteratedFDeriv_cons
""",
            1,
            "FunctionalAnalysis type the second-order symmetry comparison",
        ),
        (
            """theorem normalizedGreenBulk_expansion
    (a : ℤ) (u v : ℍ → ℂ) (z : ℍ) :
    star (raiseRaw a u z) * v z +
        star (u z) *
          (lowerRaw (a + 4) v z / heightC z ^ 2) =
      -Complex.I *
          (star (dx u z) * v z +
            star (u z) * dx v z) +
        (star (dy u z) * v z +
          star (u z) * dy v z) +
        physicalExponent a / heightC z *
          star (u z) * v z := by
  have hh : heightC z ≠ 0 := by
    simpa [heightC] using
      (Complex.ofReal_ne_zero.mpr (ne_of_gt z.im_pos))
  unfold raiseRaw lowerRaw
  simp only [star_add, star_mul', star_div, star_neg,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  field_simp [hh]
  ring_nf
  simp [Complex.I_sq]
  <;> ring
""",
            """theorem normalizedGreenBulk_expansion
    (a : ℤ) (u v : ℍ → ℂ) (z : ℍ) :
    star (raiseRaw a u z) * v z +
        star (u z) *
          (lowerRaw (a + 4) v z / heightC z ^ 2) =
      -Complex.I *
          (star (dx u z) * v z +
            star (u z) * dx v z) +
        (star (dy u z) * v z +
          star (u z) * dy v z) +
        physicalExponent a / heightC z *
          star (u z) * v z := by
  have hh : heightC z ≠ 0 := by
    simpa [heightC] using
      (Complex.ofReal_ne_zero.mpr (ne_of_gt z.im_pos))
  unfold raiseRaw lowerRaw
  simp only [star_add, star_mul', star_div, star_neg,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  have hreduce :
      heightC z * v z * physicalExponent a * (heightC z)⁻¹ * star (u z) =
        v z * physicalExponent a * star (u z) := by
    field_simp [hh]
    ring
  rw [hreduce]
  ring
""",
            1,
            "FunctionalAnalysis cancel the nonzero height only in normalizedGreenBulk_expansion",
        ),
        (
            """  simpa [weightCoefficient, div_eq_mul_inv] using
    RealSmooth.const_complex_smul q hInv
""",
            """  change RealSmooth (fun z => q * (heightC z)⁻¹)
  simpa only [Pi.smul_apply, smul_eq_mul] using
    RealSmooth.const_complex_smul q hInv
""",
            1,
            "FunctionalAnalysis expose the reciprocal weight coefficient pointwise",
        ),
        (
            """    d1 (weightCoefficient q) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ := by
      simpa [weightCoefficient, div_eq_mul_inv] using
        d1_smul q hInv z ξ
""",
            """    d1 (weightCoefficient q) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ := by
      change d1 (fun w => q * (heightC w)⁻¹) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ
      simpa only [Pi.smul_apply, smul_eq_mul] using
        d1_smul q hInv z ξ
""",
            1,
            "FunctionalAnalysis expose the weighted reciprocal derivative pointwise",
        ),
        (
            """theorem realSmooth_heightSq : RealSmooth heightSq := by
  simpa [heightSq] using realSmooth_heightC.pow 2
""",
            """theorem realSmooth_heightSq : RealSmooth heightSq := by
  change RealSmooth (fun z => heightC z ^ 2)
  exact realSmooth_heightC.pow 2
""",
            1,
            "FunctionalAnalysis expose square-height smoothness definitionally",
        ),
        ("hf.dx", "RealSmooth.dx hf", 11,
          "FunctionalAnalysis call x-derivative smoothness explicitly"),
        ("hf.dy", "RealSmooth.dy hf", 11,
          "FunctionalAnalysis call y-derivative smoothness explicitly"),
    ])


def main() -> int:
    pass155.repair_mock2()
    pass155.repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
