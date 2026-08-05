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
        """theorem lineSmul_contMDiff {B : HalfWeightBranch}
    (M : MultiplierSystem B) (γ : Gamma2) :
    CMDiff ∞ (lineSmul M γ) := by
""",
        """theorem lineSmul_contMDiff {B : HalfWeightBranch}
    (M : MultiplierSystem B) (γ : Gamma2) :
    ContMDiff ((𝓘(ℂ)).prod (𝓘(ℂ))) ((𝓘(ℂ)).prod (𝓘(ℂ))) ∞
      (lineSmul M γ) := by
""",
        "Mock2 specify both product manifold models for the line action",
    )
    m2 = replace_exact(
        m2,
        """def lineBundleMk {B : HalfWeightBranch} (M : MultiplierSystem B)
    (p : H × ℂ) : AutomorphicLineBundleTotal M :=
  Quotient.mk' p
""",
        """def lineBundleMk {B : HalfWeightBranch} (M : MultiplierSystem B)
    (p : H × ℂ) : AutomorphicLineBundleTotal M :=
  Quotient.mk (lineOrbitRel M) p
""",
        "Mock2 pass the orbit setoid explicitly to the quotient constructor",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """attribute [local -instance] instInnerProductSpaceRealComplex
attribute [local instance 2000] NormedSpace.complexToReal
""",
        """attribute [-instance] instInnerProductSpaceRealComplex
attribute [instance 2000] NormedSpace.complexToReal
""",
        "Mock2 Advanced disable the competing real inner-product instance",
    )
    m2a = replace_exact(
        m2a,
        """end StandardComplexRealNormedSpace

end CorrectedLemmas.Gamma2SixCellPolygon
""",
        """attribute [-instance] NormedSpace.complexToReal
attribute [instance] instInnerProductSpaceRealComplex
attribute [instance 900] NormedSpace.complexToReal

end StandardComplexRealNormedSpace

end CorrectedLemmas.Gamma2SixCellPolygon
""",
        "Mock2 Advanced restore the original complex-real instance priorities",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """/-- The elementary algebra at the end of the lowering covariance proof. -/
private theorem lower_covariance_algebra
""",
        """/-- The elementary algebra at the end of the lowering covariance proof. -/
set_option maxHeartbeats 800000 in
private theorem lower_covariance_algebra
""",
        "FunctionalAnalysis localize extra heartbeats to lowering covariance algebra",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
