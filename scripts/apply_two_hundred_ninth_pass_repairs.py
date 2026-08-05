from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


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

attribute [-instance] RCLike.innerProductSpace.toNormedSpace
attribute [instance] NonUnitalCStarAlgebra.toNormedSpace
attribute [instance] RCLike.innerProductSpace.toNormedSpace

/-- A globally smooth choice of `(cτ+d)⁻¹ᐟ²`.  The square law records the
""",
        "Mock2 restore the ambient NormedSpace priorities after deck calculus",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
