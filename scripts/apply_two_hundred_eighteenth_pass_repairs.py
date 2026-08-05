from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """theorem etaResidual_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (etaResidual γ) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
    (fun τ : H => etaRatio γ τ ^ 2 * denominator γ τ)
  exact ((etaRatio_contMDiff γ).pow 2).mul
    (by simpa [denominator] using
      (UpperHalfPlane.contMDiff_denom (gammaGL γ)))
""",
        """theorem etaResidual_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (etaResidual γ) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
    (fun τ : H => etaRatio γ τ ^ 2 * denominator γ τ)
  apply ((etaRatio_contMDiff γ).pow 2).mul
  unfold denominator UpperHalfPlane.denom
  exact (contMDiff_const.mul UpperHalfPlane.contMDiff_coe).add
    contMDiff_const
""",
        "Mock2 prove denominator smoothness with local affine combinators",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """/-- Global affine parametrization of the left vertical line. -/
def modularLeftVerticalCurve (t : ℝ) : ℂ :=
""",
        """section StandardComplexRealNormedSpace

local attribute [-instance] instInnerProductSpaceRealComplex
local attribute [instance 2000] NormedSpace.complexToReal

/-- Global affine parametrization of the left vertical line. -/
def modularLeftVerticalCurve (t : ℝ) : ℂ :=
""",
        "Mock2 Advanced use the standard real NormedSpace on complex boundary curves",
    )
    m2a = replace_exact(
        m2a,
        """end CorrectedLemmas.Gamma2SixCellPolygon

/-! ### Unconditional generation of `Gamma(2)`
""",
        """end StandardComplexRealNormedSpace

end CorrectedLemmas.Gamma2SixCellPolygon

/-! ### Unconditional generation of `Gamma(2)`
""",
        "Mock2 Advanced close the standard complex-real NormedSpace section",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        change Bw = star (j ^ 2) * star (j ^ 2)⁻¹ * Bw
        rw [mul_inv_cancel₀ hs, one_mul]
""",
        """        calc
          Bw = 1 * Bw := by rw [one_mul]
          _ = (star (j ^ 2) * star (j ^ 2)⁻¹) * Bw := by
            rw [mul_inv_cancel₀ hs]
          _ = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw) := by
            rw [mul_assoc]
""",
        "FunctionalAnalysis cancel the conjugate inverse by an explicit calc chain",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
