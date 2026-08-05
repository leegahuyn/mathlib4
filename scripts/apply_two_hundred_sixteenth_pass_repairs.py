from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


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
  rw [← gammaGL_smul γ τ]
  simpa [etaValue, ModularForm.discriminant, denominator, gammaGL] using hDelta
""",
        "Mock2 align the eta discriminant action with gammaGL",
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
    (fun τ : H => etaRatio γ τ ^ 2 *
      UpperHalfPlane.denom (gammaGL γ) (τ : ℂ))
  exact ((etaRatio_contMDiff γ).pow 2).mul
    (UpperHalfPlane.contMDiff_denom (gammaGL γ))
""",
        "Mock2 state eta residual smoothness pointwise",
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
  change Continuous
    (fun τ : H =>
      (⟨etaResidualUnit γ τ,
        etaResidualUnit_pow_twelve γ τ⟩ : rootsOfUnity 12 ℂ))
  exact (etaResidualUnit_continuous γ).subtype_mk
    (fun τ => etaResidualUnit_pow_twelve γ τ)
""",
        "Mock2 expose the roots-of-unity subtype function",
    )
    m2 = replace_exact(
        m2,
        """    _ = (denominatorUnit γ τ)⁻¹ *
        (etaRatioUnit γ τ ^ 2 * (etaRatioUnit γ τ ^ 2)⁻¹) := by
      rw [mul_inv_rev]
      ac_rfl
""",
        """    _ = (denominatorUnit γ τ)⁻¹ *
        (etaRatioUnit γ τ ^ 2 * (etaRatioUnit γ τ ^ 2)⁻¹) := by
      rw [_root_.mul_inv_rev]
      ac_rfl
""",
        "Mock2 disambiguate the group inverse multiplication lemma",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
