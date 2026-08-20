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
        "SmoothGaugeMap.DeckInvariant g",
        "SmoothGaugeMap.DeckInvariant I_G G g",
        "Mock2 qualify namespaced deck invariance",
        expected=3,
    )
    m2 = replace_exact(
        m2,
        "SmoothGaugeMap.RhoCompatible ρ g",
        "SmoothGaugeMap.RhoCompatible I_G G ρ g",
        "Mock2 qualify namespaced rho compatibility",
        expected=2,
    )
    m2 = replace_exact(
        m2,
        "SmoothGaugeMap.Central g",
        "SmoothGaugeMap.Central I_G G g",
        "Mock2 qualify namespaced centrality for g",
        expected=6,
    )
    m2 = replace_exact(
        m2,
        "SmoothGaugeMap.Central h",
        "SmoothGaugeMap.Central I_G G h",
        "Mock2 qualify namespaced centrality for h",
    )
    m2 = replace_exact(
        m2,
        "DeckInvariant (",
        "DeckInvariant I_G G (",
        "Mock2 qualify deck invariance applications",
        expected=5,
    )
    m2 = replace_exact(
        m2,
        "DeckInvariant g",
        "DeckInvariant I_G G g",
        "Mock2 qualify deck invariance hypotheses on g",
        expected=4,
    )
    m2 = replace_exact(
        m2,
        "DeckInvariant h",
        "DeckInvariant I_G G h",
        "Mock2 qualify deck invariance hypotheses on h",
    )
    m2 = replace_exact(
        m2,
        "RhoCompatible ρ (",
        "RhoCompatible I_G G ρ (",
        "Mock2 qualify rho compatibility applications",
        expected=4,
    )
    m2 = replace_exact(
        m2,
        "RhoCompatible ρ g",
        "RhoCompatible I_G G ρ g",
        "Mock2 qualify rho compatibility hypotheses on g",
        expected=4,
    )
    m2 = replace_exact(
        m2,
        "RhoCompatible ρ h",
        "RhoCompatible I_G G ρ h",
        "Mock2 qualify rho compatibility hypotheses on h",
    )
    m2 = replace_exact(
        m2,
        "Central (",
        "Central I_G G (",
        "Mock2 qualify centrality applications",
        expected=4,
    )
    m2 = replace_exact(
        m2,
        "Central g",
        "Central I_G G g",
        "Mock2 qualify centrality hypotheses on g",
        expected=4,
    )
    m2 = replace_exact(
        m2,
        "Central h",
        "Central I_G G h",
        "Mock2 qualify centrality hypotheses on h",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  letI : NormedField ℂ := Complex.instNormedField
  have hneg :
      HasDerivAt (fun t : ℝ => -cuspHorizontalAmbientCurve Y t) (-1) x :=
    (hasDerivAt_cuspHorizontalAmbientCurve Y x).neg
  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        """  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
  have hneg :
      HasDerivAt (fun t : ℝ => -cuspHorizontalAmbientCurve Y t) (-1) x := by
    change HasDerivAt
      (fun t : ℝ => -((t : ℂ) + (Y : ℂ) * Complex.I)) (-1) x
    exact (hreal.add_const ((Y : ℂ) * Complex.I)).neg
  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        "Mock2 Advanced rebuild the cusp derivative under one normed-space structure",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hInt := quotientInnerDensity_integrable M u u D
  rw [peterssonForm, ← integral_re hInt]
  exact MeasureTheory.integral_nonneg
    (quotientInnerDensity_self_re_nonneg M u)
""",
        """  have hInt := quotientInnerDensity_integrable M u u D
  rw [peterssonForm]
  calc
    0 ≤ ∫ q, (quotientInnerDensity M u u q).re ∂D.quotientMeasure :=
      MeasureTheory.integral_nonneg
        (quotientInnerDensity_self_re_nonneg M u)
    _ = (∫ q, quotientInnerDensity M u u q ∂D.quotientMeasure).re := by
      simpa using integral_re hInt
""",
        "FunctionalAnalysis compare the real-part integral by an explicit calc",
    )
    fa = replace_exact(
        fa,
        """    have hRealIntegral :
        ∫ q, (quotientInnerDensity M u u q).re ∂D.quotientMeasure = 0 := by
      rw [integral_re hInt]
      simpa only [peterssonForm, Complex.zero_re] using
        congrArg Complex.re hIntegral
""",
        """    have hRealIntegral :
        ∫ q, (quotientInnerDensity M u u q).re ∂D.quotientMeasure = 0 := by
      calc
        ∫ q, (quotientInnerDensity M u u q).re ∂D.quotientMeasure =
            (∫ q, quotientInnerDensity M u u q ∂D.quotientMeasure).re := by
          simpa using integral_re hInt
        _ = 0 := by
          simpa only [peterssonForm, Complex.zero_re] using
            congrArg Complex.re hIntegral
""",
        "FunctionalAnalysis identify the zero real-part integral explicitly",
    )
    fa = replace_exact(
        fa,
        """  smul_left := fun u v c => by
    simpa only [toSmoothCore_smul] using
      peterssonForm_smul_left M chosenGammaTwoFundamentalDomain c
        u.toSmoothCore v.toSmoothCore
  definite := fun u hu => by
    apply PeterssonCoreSpace.ext
    have hu' : u.toSmoothCore = 0 :=
      (peterssonForm_self_eq_zero_iff M
        chosenGammaTwoFundamentalDomain u.toSmoothCore).mp hu
    simpa only [toSmoothCore_zero] using hu'
""",
        """  smul_left := fun u v c => by
    change peterssonForm M chosenGammaTwoFundamentalDomain
        (c • u.toSmoothCore) v.toSmoothCore =
      star c * peterssonForm M chosenGammaTwoFundamentalDomain
        u.toSmoothCore v.toSmoothCore
    exact peterssonForm_smul_left M chosenGammaTwoFundamentalDomain c
      u.toSmoothCore v.toSmoothCore
  definite := fun u hu => by
    apply (coreEquiv M).injective
    change u.toSmoothCore = 0
    exact (peterssonForm_self_eq_zero_iff M
      chosenGammaTwoFundamentalDomain u.toSmoothCore).mp hu
""",
        "FunctionalAnalysis align the wrapped core star and extensionality",
    )
    fa = replace_exact(
        fa,
        """    ‖u‖ ^ 2 = (inner ℂ u u).re := norm_sq_eq_re_inner u
""",
        """    ‖u‖ ^ 2 = (inner ℂ u u).re := norm_sq_eq_re_inner (𝕜 := ℂ) u
""",
        "FunctionalAnalysis specify the inner-product scalar field",
    )
    fa = replace_exact(
        fa,
        """noncomputable def hilbertSpaceWitness :
    HilbertSpace ℂ (PeterssonHilbertCompletion M) :=
  by infer_instance
""",
        """noncomputable def hilbertSpaceWitness :
    HilbertSpace ℂ (PeterssonHilbertCompletion M) :=
  ⟨⟩
""",
        "FunctionalAnalysis construct the fieldless Hilbert witness",
    )
    fa = replace_exact(
        fa,
        """abbrev OrbitMultiplier (n : ℤ) :=
""",
        """noncomputable abbrev OrbitMultiplier (n : ℤ) :=
""",
        "FunctionalAnalysis mark the orbit multiplier abbreviation noncomputable",
    )
    fa = replace_exact(
        fa,
        """      Complex.conj
        ((u : SmoothQuotientCompactFunction) z) *
""",
        """      star
        ((u : SmoothQuotientCompactFunction) z) *
""",
        "FunctionalAnalysis use star in the fixed-phase density",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
