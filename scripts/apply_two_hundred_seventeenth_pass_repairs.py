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
  fun_prop
""",
        "Mock2 prove denominator smoothness in the ambient NormedSpace instance",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  simpa only [zero_add, mul_one] using
    (hasDerivAt_const t (-(1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  change HasDerivAt
    (fun x : ℝ => (-(1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
    Complex.I t
  have hlin :
      HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ)) Complex.I t := by
    simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
      (Complex.I • Complex.ofRealCLM).hasFDerivAt.hasDerivAt
  simpa using
    (hasDerivAt_const t (-(1 : ℝ) / 2 : ℂ)).add hlin
""",
        "Mock2 Advanced differentiate the left affine curve with ofRealCLM",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  simpa only [zero_add, mul_one] using
    (hasDerivAt_const t ((1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  change HasDerivAt
    (fun x : ℝ => ((1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
    Complex.I t
  have hlin :
      HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ)) Complex.I t := by
    simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
      (Complex.I • Complex.ofRealCLM).hasFDerivAt.hasDerivAt
  simpa using
    (hasDerivAt_const t ((1 : ℝ) / 2 : ℂ)).add hlin
""",
        "Mock2 Advanced differentiate the right affine curve with ofRealCLM",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        change Bw = star (j ^ 2) * star (j ^ 2)⁻¹ * Bw
        rw [mul_inv_cancel₀ hs, one_mul]
""",
        """        symm
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
""",
        "FunctionalAnalysis orient the conjugate inverse cancellation",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
