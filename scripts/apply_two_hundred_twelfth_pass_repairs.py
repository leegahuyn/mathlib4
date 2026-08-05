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
        """local instance (priority := 2000) : NormedSpace ℂ ℂ :=
  (RCLike.innerProductSpace : InnerProductSpace ℂ ℂ).toNormedSpace
""",
        """attribute [-instance] NonUnitalCStarAlgebra.toNormedSpace
attribute [-instance] NormedAlgebra.toNormedSpace
attribute [instance 2000] InnerProductSpace.toNormedSpace
""",
        "Mock2 select the canonical inner-product NormedSpace without an opaque wrapper",
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
        "Mock2 expose the negative-two denominator power in current normal form",
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

attribute [-instance] InnerProductSpace.toNormedSpace
attribute [instance] NonUnitalCStarAlgebra.toNormedSpace
attribute [instance] NormedAlgebra.toNormedSpace
attribute [instance] InnerProductSpace.toNormedSpace

/-- A globally smooth choice of `(cτ+d)⁻¹ᐟ²`.  The square law records the
""",
        "Mock2 restore ambient NormedSpace priorities after deck calculus",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
