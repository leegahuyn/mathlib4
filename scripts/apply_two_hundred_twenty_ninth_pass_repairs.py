from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


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
        """/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        """/- Restore the canonical real normed-space structure on `ℂ` before using
the reciprocal and smooth-calculus APIs below. -/
attribute [-instance] NormedSpace.complexToReal
attribute [instance] instInnerProductSpaceRealComplex

/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        "Mock2 Advanced restore canonical complex real calculus instances",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_cuspOneAmbientCurve {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) :
    HasDerivAt (cuspOneAmbientCurve Y)
      (cuspFiniteAmbientTangent Y x) x := by
  simpa [cuspOneAmbientCurve, cuspZeroAmbientCurve] using
    (hasDerivAt_cuspZeroAmbientCurve hY x).const_add (1 : ℂ)
""",
        """theorem hasDerivAt_cuspOneAmbientCurve {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) :
    HasDerivAt (cuspOneAmbientCurve Y)
      (cuspFiniteAmbientTangent Y x) x := by
  change HasDerivAt
    ((fun _ : ℝ => (1 : ℂ)) + cuspZeroAmbientCurve Y)
      (cuspFiniteAmbientTangent Y x) x
  simpa only [zero_add] using
    (hasDerivAt_const x (1 : ℂ)).add
      (hasDerivAt_cuspZeroAmbientCurve hY x)
""",
        "Mock2 Advanced differentiate the translated cusp curve explicitly",
    )
    m2a = replace_exact(
        m2a,
        """theorem contDiff_cuspOneAmbientCurve {Y : ℝ} (hY : 0 < Y) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cuspOneAmbientCurve Y) := by
  simpa [cuspOneAmbientCurve, cuspZeroAmbientCurve] using
    (contDiff_cuspZeroAmbientCurve hY).const_add (1 : ℂ)
""",
        """theorem contDiff_cuspOneAmbientCurve {Y : ℝ} (hY : 0 < Y) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cuspOneAmbientCurve Y) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    ((fun _ : ℝ => (1 : ℂ)) + cuspZeroAmbientCurve Y)
  exact contDiff_const.add (contDiff_cuspZeroAmbientCurve hY)
""",
        "Mock2 Advanced prove translated cusp smoothness explicitly",
    )
    m2a = replace_exact(
        m2a,
        """  simp [cuspLevelCurve, Gamma2Cusp.scalingMatrix]
""",
        """  simp [cuspLevelCurve, Gamma2Cusp.scalingMatrix,
    cuspHorizontalAmbientCurve]
""",
        "Mock2 Advanced unfold the infinity cusp ambient curve",
    )
    m2a = replace_exact(
        m2a,
        """        exact coe_cuspLevelCurve_infinity Y hY x
""",
        """        exact (coe_cuspLevelCurve_infinity Y hY x).symm
""",
        "Mock2 Advanced orient the infinity carrier equality",
    )
    m2a = replace_exact(
        m2a,
        """        exact coe_cuspLevelCurve_zero Y hY x
""",
        """        exact (coe_cuspLevelCurve_zero Y hY x).symm
""",
        "Mock2 Advanced orient the zero carrier equality",
    )
    m2a = replace_exact(
        m2a,
        """        exact coe_cuspLevelCurve_one Y hY x
""",
        """        exact (coe_cuspLevelCurve_one Y hY x).symm
""",
        "Mock2 Advanced orient the one carrier equality",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
