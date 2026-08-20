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
        """noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        """noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

noncomputable local instance oneFormValueChartedSpace :
    ChartedSpace (OneFormValue I_G G) (OneFormValue I_G G) := by
  change ChartedSpace (ℂ →L[ℂ] E_G) (ℂ →L[ℂ] E_G)
  infer_instance

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        "Mock2 transport the self chart to one-form values",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """/- Restore the canonical real normed-space structure on `ℂ` before using
the reciprocal and smooth-calculus APIs below. -/
attribute [-instance] NormedSpace.complexToReal
attribute [instance] instInnerProductSpaceRealComplex

/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        """/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        "Mock2 Advanced retain the standard complex-to-real calculus instance",
    )
    m2a = replace_exact(
        m2a,
        """  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent] using hneg.inv hne
""",
        """  have hinv := hneg.inv hne
  convert hinv using 1 <;>
    simp [cuspZeroAmbientCurve, cuspFiniteAmbientTangent]
""",
        "Mock2 Advanced transport inverse differentiation across proof-irrelevant instances",
    )
    m2a = replace_exact(
        m2a,
        """  simpa [cuspZeroAmbientCurve] using
    hneg.inv (fun x => neg_ne_zero.mpr
      (cuspHorizontalAmbientCurve_ne_zero hY x))
""",
        """  have hinv := hneg.inv (fun x => neg_ne_zero.mpr
    (cuspHorizontalAmbientCurve_ne_zero hY x))
  convert hinv using 1 <;> simp [cuspZeroAmbientCurve]
""",
        "Mock2 Advanced transport inverse smoothness across proof-irrelevant instances",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        (Filter.Eventually.of_forall fun x =>
          directionalDerivative_apply ξ u x))
""",
        """        (Filter.Eventually.of_forall fun x => by
          simpa only [one_mul] using directionalDerivative_apply ξ u x))
""",
        "FunctionalAnalysis normalize the unit factor in derivative integrability",
    )
    fa = replace_exact(
        fa,
        """  simpa only [one_mul, fderiv_const, zero_apply, zero_mul,
    integral_zero, neg_zero, directionalDerivative_apply] using h
""",
        """  have hconst :
      (fun x : ℂ =>
        (fderiv ℝ (fun _w : ℂ => (1 : ℂ)) x) ξ * u x) = 0 := by
    funext x
    simp
  rw [hconst, integral_zero, neg_zero] at h
  simpa only [one_mul, directionalDerivative_apply] using h
""",
        "FunctionalAnalysis remove the constant derivative before simplifying the integral",
    )
    fa = replace_exact(
        fa,
        """  simpa only [HalfWeightDifferentialOperators.dx, dx] using
    integral_d1_mul_test_eq_neg f hf v 1
""",
        """  change (∫ w : ℂ,
      localizeLeft (fun z => d1 f z 1)
        (RealSmooth.d1_constDirection hf 1) v w) =
      -(∫ w : ℂ, localizeLeft f hf (directionalDerivative 1 v) w)
  exact integral_d1_mul_test_eq_neg f hf v 1
""",
        "FunctionalAnalysis expose dx as the real directional derivative",
    )
    fa = replace_exact(
        fa,
        """  simpa only [HalfWeightDifferentialOperators.dy, dy] using
    integral_d1_mul_test_eq_neg f hf v Complex.I
""",
        """  change (∫ w : ℂ,
      localizeLeft (fun z => d1 f z Complex.I)
        (RealSmooth.d1_constDirection hf Complex.I) v w) =
      -(∫ w : ℂ,
        localizeLeft f hf (directionalDerivative Complex.I v) w)
  exact integral_d1_mul_test_eq_neg f hf v Complex.I
""",
        "FunctionalAnalysis expose dy as the imaginary directional derivative",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
