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
        """noncomputable local instance oneFormValueChartedSpace :
    ChartedSpace (OneFormValue I_G G) (OneFormValue I_G G) := by
  change ChartedSpace (ℂ →L[ℂ] E_G) (ℂ →L[ℂ] E_G)
  infer_instance

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        """/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        "Mock2 remove the ineffective transported self chart",
    )
    m2 = replace_exact(
        m2,
        """  smooth_toFun :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞ toFun
""",
        """  smooth_toFun :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] E_G) ∞ toFun
""",
        "Mock2 expose the concrete one-form target model",
    )
    m2 = replace_exact(
        m2,
        """    exact (contMDiff_const :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞
        (fun _ : coverOpen U => (0 : OneFormValue I_G G)))
""",
        """    exact (contMDiff_const :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] E_G) ∞
        (fun _ : coverOpen U => (0 : OneFormValue I_G G)))
""",
        "Mock2 type the zero form in the concrete one-form model",
    )
    m2 = replace_exact(
        m2,
        """def liftedFormPresheaf : PresheafLike X where
""",
        """abbrev liftedFormPresheaf : PresheafLike X where
""",
        "Mock2 make the lifted form section carrier reducible",
    )
    m2 = replace_exact(
        m2,
        """  (contDiffWithinAt_localInvariantProp
    (I := 𝒤(ℂ))
    (I' := 𝒤(ℂ, OneFormValue I_G G)) ∞).localPredicate
""",
        """  (contDiffWithinAt_localInvariantProp
    (I := 𝓘(ℂ))
    (I' := 𝓘(ℂ, OneFormValue I_G G)) ∞).localPredicate
""",
        "Mock2 repair the manifold model notation in the local predicate",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  simpa [cuspHorizontalAmbientCurve] using
    hreal.add_const ((Y : ℂ) * Complex.I)
""",
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  have hreal := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hfun : (⇑Complex.ofRealCLM : ℝ → ℂ) =
      (fun t : ℝ => (t : ℂ)) := by
    funext t
    rfl
  rw [hfun] at hreal
  change HasDerivAt
    (fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I) 1 x
  exact hreal.add_const ((Y : ℂ) * Complex.I)
""",
        "Mock2 Advanced identify the real embedding extensionally",
    )
    m2a = replace_exact(
        m2a,
        """  have hinv := hneg.inv hne
  convert hinv using 1 <;>
    simp [cuspZeroAmbientCurve, cuspFiniteAmbientTangent]
""",
        """  change HasDerivAt
    (fun t : ℝ => (-cuspHorizontalAmbientCurve Y t)⁻¹)
      (1 / cuspHorizontalAmbientCurve Y x ^ 2) x
  convert hneg.inv hne using 1
  ring
""",
        "Mock2 Advanced normalize the finite-cusp derivative coefficient algebraically",
    )
    m2a = replace_exact(
        m2a,
        """  have hinv := hneg.inv (fun x => neg_ne_zero.mpr
    (cuspHorizontalAmbientCurve_ne_zero hY x))
  convert hinv using 1 <;> simp [cuspZeroAmbientCurve]
""",
        """  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun x : ℝ => (-cuspHorizontalAmbientCurve Y x)⁻¹)
  exact hneg.inv (fun x => neg_ne_zero.mpr
    (cuspHorizontalAmbientCurve_ne_zero hY x))
""",
        "Mock2 Advanced expose the reciprocal curve before smoothness",
    )
    m2a = replace_exact(
        m2a,
        """    Pairwise (Disjoint on strictCuspHoroball)
""",
        """    Pairwise fun κ₁ κ₂ =>
      Disjoint (strictCuspHoroball κ₁) (strictCuspHoroball κ₂)
""",
        "Mock2 Advanced replace the removed on combinator for cusp horoballs",
    )
    m2a = replace_exact(
        m2a,
        """  open_cells_pairwise_disjoint : Pairwise (Disjoint on openCell)
""",
        """  open_cells_pairwise_disjoint : Pairwise fun r₁ r₂ =>
    Disjoint (openCell r₁) (openCell r₂)
""",
        "Mock2 Advanced replace the removed on combinator for open cells",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  rw [hconst, integral_zero, neg_zero] at h
  simpa only [one_mul, directionalDerivative_apply] using h
""",
        """  rw [hconst] at h
  simp at h
  simpa only [one_mul, directionalDerivative_apply] using h
""",
        "FunctionalAnalysis simplify the zero integral after function replacement",
    )
    fa = replace_exact(
        fa,
        """  simpa only [directionalDerivative_apply] using
    (tsupport_fderiv_apply_subset ℝ ξ :
      tsupport (fun w : ℂ => fderiv ℝ (v : ℂ → ℂ) w ξ) ⊆
        tsupport (v : ℂ → ℂ))
""",
        """  have hfun : (directionalDerivative ξ v : ℂ → ℂ) =
      fun w : ℂ => fderiv ℝ (v : ℂ → ℂ) w ξ := by
    funext w
    exact directionalDerivative_apply ξ v w
  rw [hfun]
  exact (tsupport_fderiv_apply_subset ℝ ξ :
    tsupport (fun w : ℂ => fderiv ℝ (v : ℂ → ℂ) w ξ) ⊆
      tsupport (v : ℂ → ℂ))
""",
        "FunctionalAnalysis identify bundled derivative support extensionally",
    )
    fa = replace_exact(
        fa,
        """  · rw [dy_rpowMul_apply_of_im_pos p v hw]
    simp only [TestFunction.add_apply, TestFunction.smul_apply,
      rpowMul_apply, rpowScale, smul_eq_mul, Complex.ofReal_mul]
    ring
""",
        """  · rw [dy_rpowMul_apply_of_im_pos p v hw]
    change _ = (p : ℂ) * rpowMul (p - 1) v w +
      rpowMul p (dy v) w
    simp only [rpowMul_apply, rpowScale, smul_eq_mul,
      Complex.ofReal_mul]
    ring
""",
        "FunctionalAnalysis expose bundled addition and scalar evaluation",
    )
    fa = replace_exact(
        fa,
        """        localizeLeft (HalfWeightDifferentialOperators.dx f) RealSmooth.dx hf
          (rpowMul p v) w) =
""",
        """        localizeLeft (HalfWeightDifferentialOperators.dx f)
          (RealSmooth.dx hf) (rpowMul p v) w) =
""",
        "FunctionalAnalysis apply horizontal smoothness in weighted integration",
    )
    fa = replace_exact(
        fa,
        """        localizeLeft (HalfWeightDifferentialOperators.dy f) RealSmooth.dy hf
          (rpowMul p v) w) =
""",
        """        localizeLeft (HalfWeightDifferentialOperators.dy f)
          (RealSmooth.dy hf) (rpowMul p v) w) =
""",
        "FunctionalAnalysis apply vertical smoothness in weighted integration",
    )
    fa = replace_exact(
        fa,
        """  · rw [dy_rpowMul_apply_of_im_pos (1 : ℝ) v hw]
    simp only [rpowScale, Real.rpow_one, one_mul, sub_self,
      Real.rpow_zero, Complex.ofReal_one]
    ring
""",
        """  · rw [dy_rpowMul_apply_of_im_pos (1 : ℝ) v hw]
    change _ = v w + rpowMul 1 (dy v) w
    simp only [rpowMul_apply, rpowScale, Real.rpow_one, one_mul,
      sub_self, Real.rpow_zero, Complex.ofReal_one]
    ring
""",
        "FunctionalAnalysis expose the height-one bundled addition",
    )
    fa = replace_exact(
        fa,
        """        localizeLeft (HalfWeightDifferentialOperators.dx f) RealSmooth.dx hf
          (rpowMul 1 v) w) =
""",
        """        localizeLeft (HalfWeightDifferentialOperators.dx f)
          (RealSmooth.dx hf) (rpowMul 1 v) w) =
""",
        "FunctionalAnalysis apply horizontal smoothness at height one",
    )
    fa = replace_exact(
        fa,
        """        localizeLeft (HalfWeightDifferentialOperators.dy f) RealSmooth.dy hf
          (rpowMul 1 v) w) =
""",
        """        localizeLeft (HalfWeightDifferentialOperators.dy f)
          (RealSmooth.dy hf) (rpowMul 1 v) w) =
""",
        "FunctionalAnalysis apply vertical smoothness at height one",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
