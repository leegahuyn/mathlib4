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
        """  exact ((etaRatio_contMDiff γ).continuous.pow 2).mul
    (UpperHalfPlane.contMDiff_denom (gammaGL γ)).continuous
""",
        """  exact ((etaRatio_contMDiff γ).continuous.pow 2).mul
    (UpperHalfPlane.contMDiff_denom (n := ∞) (gammaGL γ)).continuous
""",
        "Mock2 specify infinite smoothness in residual continuity",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """local attribute [-instance] instInnerProductSpaceRealComplex
local attribute [instance 2000] NormedSpace.complexToReal
""",
        """attribute [local -instance] instInnerProductSpaceRealComplex
attribute [local instance 2000] NormedSpace.complexToReal
""",
        "Mock2 Advanced use valid local attribute syntax for the standard complex-real NormedSpace",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """          _ = (star (j ^ 2) * star (j ^ 2)⁻¹) * Bw := by
            rw [mul_inv_cancel₀ hs]
          _ = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw) := by
            rw [mul_assoc]
""",
        """          _ = (star (j ^ 2) * star (j ^ 2)⁻¹) * Bw :=
            congrArg (fun z : ℂ => z * Bw) (mul_inv_cancel₀ hs).symm
          _ = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw) :=
            mul_assoc _ _ _
""",
        "FunctionalAnalysis cancel the conjugate inverse without rewrite matching",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
