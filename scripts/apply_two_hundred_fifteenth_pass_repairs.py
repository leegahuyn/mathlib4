from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(
            f"{label}: expected exactly {expected} match(es), found {count}"
        )
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  convert
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      (-(1 : ℝ) / 2 : ℂ)) using 1 <;>
    simp [add_comm]
""",
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  change HasDerivAt
    (fun x : ℝ => (-(1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
    Complex.I t
  simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
    ((Complex.I • Complex.ofRealCLM).hasDerivAt (x := t)).const_add
      (-(1 : ℝ) / 2 : ℂ)
""",
        "Mock2 Advanced differentiate the left affine curve through ofRealCLM",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  convert
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      ((1 : ℝ) / 2 : ℂ)) using 1 <;>
    simp [add_comm]
""",
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  change HasDerivAt
    (fun x : ℝ => ((1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
    Complex.I t
  simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
    ((Complex.I • Complex.ofRealCLM).hasDerivAt (x := t)).const_add
      ((1 : ℝ) / 2 : ℂ)
""",
        "Mock2 Advanced differentiate the right affine curve through ofRealCLM",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """      Bw = star (j ^ 2) *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [map_inv₀]
        field_simp [hjc]
""",
        """      Bw = star (j ^ 2) *
          (star ((j ^ 2)⁻¹) * Bw) := by
        field_simp [hjc]
""",
        "FunctionalAnalysis cancel the normalized conjugate inverse directly",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
