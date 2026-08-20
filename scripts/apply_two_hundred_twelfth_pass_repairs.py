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
        """local instance (priority := 2000) : NormedSpace ℂ ℂ :=
  (RCLike.innerProductSpace : InnerProductSpace ℂ ℂ).toNormedSpace
""",
        """section DeckCalculusCanonicalNormedSpace

local instance (priority := 100000) canonicalNormedSpaceComplex :
    NormedSpace ℂ ℂ :=
  (RCLike.innerProductSpace : InnerProductSpace ℂ ℂ).toNormedSpace
""",
        "Mock2 isolate the canonical complex NormedSpace for deck calculus",
    )
    m2 = replace_exact(
        m2,
        """theorem deckDerivative_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (deckDerivative γ) := by
  simpa [deckDerivative, denominator] using
    (UpperHalfPlane.contMDiff_denom_zpow (gammaGL γ) (-2))
""",
        """theorem deckDerivative_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (deckDerivative γ) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
    (fun τ : H => (denominator γ τ ^ 2)⁻¹)
  simpa [denominator] using
    (UpperHalfPlane.contMDiff_denom_zpow (gammaGL γ) (-2))
""",
        "Mock2 expose the negative-two denominator power in standard form",
    )
    m2 = replace_exact(
        m2,
        """theorem deckTangent_mul (γ δ : Gamma2) (τ : H) :
    deckTangent (γ * δ) τ =
      (deckTangent γ (δ • τ)).comp (deckTangent δ τ) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [deckDerivative_mul, mul_assoc]

/-- A globally smooth choice of `(cτ+d)⁻¹ᐟ²`.  The square law records the
""",
        """theorem deckTangent_mul (γ δ : Gamma2) (τ : H) :
    deckTangent (γ * δ) τ =
      (deckTangent γ (δ • τ)).comp (deckTangent δ τ) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [deckDerivative_mul, mul_assoc]

end DeckCalculusCanonicalNormedSpace

/-- A globally smooth choice of `(cτ+d)⁻¹ᐟ²`.  The square law records the
""",
        "Mock2 close the canonical deck-calculus instance scope",
    )
    M2.write_text(m2, encoding="utf-8")

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
  unfold modularLeftVerticalCurve
  convert
    (hasDerivAt_const t (-(1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal) using 1 <;>
    simp
""",
        "Mock2 Advanced differentiate the left affine vertical curve",
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
  unfold modularRightVerticalCurve
  convert
    (hasDerivAt_const t ((1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal) using 1 <;>
    simp
""",
        "Mock2 Advanced differentiate the right affine vertical curve",
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
        have hs : star (j ^ 2) ≠ 0 := by
          simpa [map_pow] using pow_ne_zero 2 hjc
        change Bw = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw)
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
""",
        "FunctionalAnalysis cancel the normalized conjugate inverse directly",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
