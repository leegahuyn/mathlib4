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
        """noncomputable local instance gaugeGroupChartedSpace :
    ChartedSpace ModelSpace GaugeGroup := by
  change ChartedSpace ModelSpace ModelSpace
  infer_instance

instance gaugeGroupLieGroup : LieGroup GaugeModel ∞ GaugeGroup where
  contMDiff_mul := by
""",
        """noncomputable local instance gaugeGroupChartedSpace :
    ChartedSpace ModelSpace GaugeGroup := by
  change ChartedSpace ModelSpace ModelSpace
  infer_instance

noncomputable local instance gaugeGroupIsManifold :
    IsManifold GaugeModel ∞ GaugeGroup := by
  change IsManifold GaugeModel ∞ ModelSpace
  infer_instance

instance gaugeGroupLieGroup : LieGroup GaugeModel ∞ GaugeGroup where
  compatible := IsManifold.compatible
  contMDiff_mul := by
""",
        "Mock2 transport the standard manifold compatibility to the gauge synonym",
    )
    m2 = replace_exact(
        m2,
        """  maurerCartan_formula := by
    intro U g τ
    rw [smoothGaugeMap_eq_constant U g]
    simpa using
      (leftLogarithmicDerivativeValue_constant GaugeModel GaugeGroup
        U (1 : GaugeGroup) τ).symm
""",
        """  maurerCartan_formula := by
    intro U g τ
    exact Subsingleton.elim _ _
""",
        "Mock2 close the zero-dimensional Maurer-Cartan value by subsingletonity",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  · simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve,
      one_div, inv_neg, pow_two]
""",
        """  · rw [show -((Y : ℂ) * Complex.I) + -(x : ℂ) =
        -((x : ℂ) + (Y : ℂ) * Complex.I) by ring, inv_neg]
    ring
""",
        "Mock2 Advanced normalize the negated reciprocal square explicitly",
    )
    m2a = replace_exact(
        m2a,
        """  field_simp [hτ]
  ring_nf

theorem factor_sq""",
        """  field_simp [hτ]
  ring

theorem factor_sq""",
        "Mock2 Advanced close the first-base product by commutative ring normalization",
    )
    m2a = replace_exact(
        m2a,
        """    ModularGroup.S_inv, ModularGroup.coe_S, ModularGroup.coe_T_zpow,
    Matrix.mul_fin_two]
  ring_nf
""",
        """    ModularGroup.S_inv, ModularGroup.coe_S, ModularGroup.coe_T_zpow,
    Matrix.mul_fin_two]
  norm_num [Matrix.mul_fin_two] <;> ring
""",
        "Mock2 Advanced evaluate the zero-translation denominator matrix",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  unfold fluxOneFormValue fixedPhaseGreenFluxX fixedPhaseGreenFluxY
  rw [← Complex.re_add_im ξ]
  ring
""",
        """  unfold fluxOneFormValue fixedPhaseGreenFluxX fixedPhaseGreenFluxY
  rw [← Complex.re_add_im ξ]
  simp <;> ring
""",
        "FunctionalAnalysis reduce real and imaginary parts after complex reassembly",
    )
    fa = replace_exact(
        fa,
        """  push_cast at hSignC
  rw [mul_assoc, hSignC]
  ring
""",
        """  push_cast at hSignC
  rw [← mul_assoc, hSignC]
  ring
""",
        "FunctionalAnalysis reassociate orientation signs before rewriting",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
