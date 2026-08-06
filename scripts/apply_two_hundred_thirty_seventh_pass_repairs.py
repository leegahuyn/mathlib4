from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """attribute [-instance] NormedSpace.complexToReal

/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        """/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        "Mock2 Advanced keep complexToReal for the horizontal cusp line",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  simpa [cuspHorizontalAmbientCurve] using
    (((hasDerivAt_id (x : ℂ)).comp_ofReal).add_const
      ((Y : ℂ) * Complex.I))
""",
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  have hreal : HasDerivAt (⇑Complex.ofRealCLM) 1 x :=
    (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
  have hfun : (⇑Complex.ofRealCLM : ℝ → ℂ) =
      (fun t : ℝ => (t : ℂ)) := by
    funext t
    rfl
  rw [hfun] at hreal
  change HasDerivAt
    (fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I) 1 x
  exact hreal.add_const ((Y : ℂ) * Complex.I)
""",
        "Mock2 Advanced reuse the proved complex real embedding derivative",
    )
    m2a = replace_exact(
        m2a,
        """theorem contDiff_cuspHorizontalAmbientCurve (Y : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cuspHorizontalAmbientCurve Y) := by
  unfold cuspHorizontalAmbientCurve
  fun_prop
""",
        """theorem contDiff_cuspHorizontalAmbientCurve (Y : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cuspHorizontalAmbientCurve Y) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun x : ℝ => (x : ℂ) + (Y : ℂ) * Complex.I)
  simpa [Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.add contDiff_const
""",
        "Mock2 Advanced reuse the smooth complex real embedding",
    )
    m2a = replace_exact(
        m2a,
        """/-- Exact tangent formula for the cusp at zero. -/
theorem hasDerivAt_cuspZeroAmbientCurve {Y : ℝ} (hY : 0 < Y)
""",
        """attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.toInnerProductSpaceReal

/-- Exact tangent formula for the cusp at zero. -/
theorem hasDerivAt_cuspZeroAmbientCurve {Y : ℝ} (hY : 0 < Y)
""",
        "Mock2 Advanced isolate reciprocal calculus on the normed-algebra instance",
    )
    m2a = replace_exact(
        m2a,
        """attribute [instance 2000] NormedSpace.complexToReal

/-! ##### Finite assembly of the complete truncated boundary -/
""",
        """attribute [instance] RCLike.toInnerProductSpaceReal
attribute [instance 2000] NormedSpace.complexToReal

/-! ##### Finite assembly of the complete truncated boundary -/
""",
        "Mock2 Advanced restore real complex instances after reciprocal calculus",
    )
    m2a = replace_exact(
        m2a,
        """theorem generated_le_gamma2 : generated ≤ Gamma2 := by
  apply Subgroup.closure_le.2
""",
        """theorem generated_le_gamma2 : generated ≤ Gamma2 := by
  apply (Subgroup.closure_le Gamma2).2
""",
        "Mock2 Advanced apply the closure theorem to its target subgroup",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  simp [exponentC_eq_physicalExponent, rpowScale,
    Real.rpow_neg_one, heightC, restrictToUpper, div_eq_mul_inv]
  ring
""",
        """  simp [exponentC_eq_physicalExponent, rpowScale,
    Real.rpow_neg_one, heightC, restrictToUpper, div_eq_mul_inv]
""",
        "FunctionalAnalysis remove the tactic after raising restriction closes",
    )
    fa = replace_exact(
        fa,
        """  field_simp [hy]
  ring
""",
        """  field_simp [hy]
""",
        "FunctionalAnalysis remove the tactic after normalized lowering closes",
    )
    fa = replace_exact(
        fa,
        """  have hBase : ContDiffOn ℝ ∞
      (HalfWeightCompactCoordinateGreen.rpowScale p)
""",
        """  have hBase : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (HalfWeightCompactCoordinateGreen.rpowScale p)
""",
        "FunctionalAnalysis type the infinite smoothness order explicitly",
    )
    fa = replace_exact(
        fa,
        """def gammaTwoActionCoordinate (γ : GammaTwo) : ℍ → ℂ :=
""",
        """noncomputable def gammaTwoActionCoordinate (γ : GammaTwo) : ℍ → ℂ :=
""",
        "FunctionalAnalysis mark the modular action coordinate noncomputable",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
