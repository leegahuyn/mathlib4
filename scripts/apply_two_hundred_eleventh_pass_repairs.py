from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  simpa [modularLeftVerticalCurve] using
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      (-(1 : ℝ) / 2 : ℂ))
""",
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  convert
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      (-(1 : ℝ) / 2 : ℂ)) using 1 <;>
    simp [add_comm]
""",
        "Mock2 Advanced identify the left affine vertical derivative",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  simpa [modularRightVerticalCurve] using
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      ((1 : ℝ) / 2 : ℂ))
""",
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  convert
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      ((1 : ℝ) / 2 : ℂ)) using 1 <;>
    simp [add_comm]
""",
        "Mock2 Advanced identify the right affine vertical derivative",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hBw : Bw = star j ^ 2 * F * Bz := by
    calc
      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [← hConjPow]
        field_simp [hjc]
        ring
      _ = star j ^ 2 * (F * Bz) := by rw [hDerivative]
      _ = star j ^ 2 * F * Bz := by ring
""",
        """  have hBw : Bw = star j ^ 2 * F * Bz := by
    calc
      Bw = star (j ^ 2) *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [map_inv₀]
        field_simp [hjc]
      _ = star (j ^ 2) * (F * Bz) := by rw [hDerivative]
      _ = star j ^ 2 * F * Bz := by rw [hConjPow]; ring
""",
        "FunctionalAnalysis cancel a conjugated inverse before lowering algebra",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
