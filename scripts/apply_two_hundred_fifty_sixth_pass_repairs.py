from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        "noncomputable local instance gaugeGroupChartedSpace :",
        "noncomputable instance gaugeGroupChartedSpace :",
        "Mock2 keep the concrete gauge chart available to exported certificate types",
    )
    m2 = replace_exact(
        m2,
        """    (curvatureAlgebra.curvature A) x =
""",
        """    (curvatureAlgebra.curvature A).toFun x =
""",
        "Mock2 evaluate bundled curvature through the locally constant projection",
    )
    m2 = replace_exact(
        m2,
        """  inverse_forward := by
    have h := congrArg (fun A : Form 0 U => A x) g.inverse_forward
    simpa [identityForm] using h
  forward_inverse := by
    have h := congrArg (fun A : Form 0 U => A x) g.forward_inverse
    simpa [identityForm] using h
""",
        """  inverse_forward := by
    change (wedge g.inverse g.forward) x = identityForm U x
    exact congrArg (fun A : Form 0 U => A x) g.inverse_forward
  forward_inverse := by
    change (wedge g.forward g.inverse) x = identityForm U x
    exact congrArg (fun A : Form 0 U => A x) g.forward_inverse
""",
        "Mock2 compare pointwise frame inverses in the original form carrier",
    )
    m2 = replace_exact(
        m2,
        """  inverse_forward := by
    apply LocallyConstant.ext
    intro x
    have h := congrArg (fun A : Form 0 V => A ⟨x.1, hUV x.2⟩)
      g.inverse_forward
    simpa [restrictForm, wedge, identityForm] using h
  forward_inverse := by
    apply LocallyConstant.ext
    intro x
    have h := congrArg (fun A : Form 0 V => A ⟨x.1, hUV x.2⟩)
      g.forward_inverse
    simpa [restrictForm, wedge, identityForm] using h
""",
        """  inverse_forward := by
    apply LocallyConstant.ext
    intro x
    change
      (wedge g.inverse g.forward) ⟨x.1, hUV x.2⟩ =
        identityForm V ⟨x.1, hUV x.2⟩
    exact congrArg (fun A : Form 0 V => A ⟨x.1, hUV x.2⟩)
      g.inverse_forward
  forward_inverse := by
    apply LocallyConstant.ext
    intro x
    change
      (wedge g.forward g.inverse) ⟨x.1, hUV x.2⟩ =
        identityForm V ⟨x.1, hUV x.2⟩
    exact congrArg (fun A : Form 0 V => A ⟨x.1, hUV x.2⟩)
      g.forward_inverse
""",
        "Mock2 prove restricted inverse laws before transporting the point",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem generated_le_projectedMatrices :
    Gamma2Generation.generated ≤ thetaCovariantProjectedMatrices := by
  rw [Subgroup.closure_le]
""",
        """theorem generated_le_projectedMatrices :
    Gamma2Generation.generated ≤ thetaCovariantProjectedMatrices := by
  unfold Gamma2Generation.generated
  rw [Subgroup.closure_le]
""",
        "Mock2 Advanced expose the generated subgroup before closure elimination",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  unfold quotientTSupport
""",
        """  unfold SmoothCompactCoreGeometry.quotientTSupport
""",
        "FunctionalAnalysis qualify the quotient support definition",
        expected=2,
    )
    fa = replace_exact(
        fa,
        """    simpa only [CompactlySupportedContinuousMap.coe_smul] using
      (MemLp.toLp_const_smul c (memLpTwo mu f))
""",
        """    simpa only [CompactlySupportedContinuousMap.coe_smul, RingHom.id_apply] using
      (MemLp.toLp_const_smul c (memLpTwo mu f))
""",
        "FunctionalAnalysis reduce the identity scalar hom in the L2 map",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
