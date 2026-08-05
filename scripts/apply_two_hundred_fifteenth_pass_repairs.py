from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
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
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  have hDelta :=
    SlashInvariantForm.slash_action_eqn''
      CuspForm.discriminant hmem τ
  simpa [etaValue, ModularForm.discriminant, denominator, gammaGL] using hDelta
""",
        """  have hDelta :=
    SlashInvariantForm.slash_action_eqn''
      CuspForm.discriminant hmem τ
  have hact : gammaGL γ • τ = γ • τ := gammaGL_smul γ τ
  rw [hact] at hDelta
  simpa [etaValue, ModularForm.discriminant, denominator] using hDelta
""",
        "Mock2 identify the GL and subgroup actions in the discriminant law",
    )
    m2 = replace_exact(
        m2,
        """theorem etaResidual_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (etaResidual γ) := by
  simpa [etaResidual, denominator] using
    ((etaRatio_contMDiff γ).pow 2).mul
      (UpperHalfPlane.contMDiff_denom (gammaGL γ))
""",
        """theorem etaResidual_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (etaResidual γ) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
    (fun τ : H => etaRatio γ τ ^ 2 * denominator γ τ)
  exact ((etaRatio_contMDiff γ).pow 2).mul
    (by simpa [denominator] using
      (UpperHalfPlane.contMDiff_denom (gammaGL γ)))
""",
        "Mock2 expose the eta residual product before smoothness",
    )
    m2 = replace_exact(
        m2,
        """theorem etaResidualRoot_continuous (γ : Gamma2) :
    Continuous (etaResidualRoot γ) := by
  simpa [etaResidualRoot] using
    (etaResidualUnit_continuous γ).subtype_mk
      (fun τ => etaResidualUnit_pow_twelve γ τ)
""",
        """theorem etaResidualRoot_continuous (γ : Gamma2) :
    Continuous (etaResidualRoot γ) := by
  change Continuous (fun τ : H =>
    (⟨etaResidualUnit γ τ, etaResidualUnit_pow_twelve γ τ⟩ :
      rootsOfUnity 12 ℂ))
  exact (etaResidualUnit_continuous γ).subtype_mk
    (fun τ => etaResidualUnit_pow_twelve γ τ)
""",
        "Mock2 expose the residual-root subtype map before continuity",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  convert
    (hasDerivAt_const t (-(1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal) using 1 <;>
    simp
""",
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  simpa only [zero_add, mul_one] using
    (hasDerivAt_const t (-(1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        "Mock2 Advanced close the left affine derivative without convert residue",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  convert
    (hasDerivAt_const t ((1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal) using 1 <;>
    simp
""",
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  simpa only [zero_add, mul_one] using
    (hasDerivAt_const t ((1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        "Mock2 Advanced close the right affine derivative without convert residue",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        change Bw = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw)
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
""",
        """        change Bw = star (j ^ 2) * star (j ^ 2)⁻¹ * Bw
        rw [mul_inv_cancel₀ hs, one_mul]
""",
        "FunctionalAnalysis cancel the left-associated conjugate inverse",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
