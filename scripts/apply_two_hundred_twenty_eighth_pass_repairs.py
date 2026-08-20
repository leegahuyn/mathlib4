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
        """/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        """/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G

noncomputable local instance oneFormValueNormedAddCommGroup :
    NormedAddCommGroup (OneFormValue I_G G) := by
  change NormedAddCommGroup (ℂ →L[ℂ] E_G)
  infer_instance

noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        "Mock2 transport the normed structures to one-form values",
    )
    m2 = replace_exact(
        m2,
        """noncomputable def zero (U : Opens) : SmoothOneForm I_G G U where
  toFun := fun _ => 0
  smooth_toFun := contMDiff_const

@[simp] theorem zero_apply (U : Opens) (τ : coverOpen U) :
    zero I_G G U τ = 0 :=
  rfl
""",
        """noncomputable def zero (U : Opens) : SmoothOneForm I_G G U where
  toFun := fun _ => 0
  smooth_toFun := by
    exact (contMDiff_const :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞
        (fun _ : coverOpen U => (0 : OneFormValue I_G G)))

@[simp] theorem zero_apply (U : Opens) (τ : coverOpen U) :
    zero I_G G U τ = 0 := by
  simp [zero]
""",
        "Mock2 make the zero one-form model and coercion explicit",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem cuspOneAmbientCurve_eq_one_sub_inv (Y x : ℝ) :
    cuspOneAmbientCurve Y x =
      1 - (cuspHorizontalAmbientCurve Y x)⁻¹ := by
  simp [cuspOneAmbientCurve]
""",
        """theorem cuspOneAmbientCurve_eq_one_sub_inv (Y x : ℝ) :
    cuspOneAmbientCurve Y x =
      1 - (cuspHorizontalAmbientCurve Y x)⁻¹ := by
  simp [cuspOneAmbientCurve, sub_eq_add_neg]
""",
        "Mock2 Advanced normalize subtraction on the cusp-one curve",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  simpa [cuspHorizontalAmbientCurve] using
    (((hasDerivAt_id (x : ℂ)).comp_ofReal).add_const
      ((Y : ℂ) * Complex.I))

 theorem contDiff_cuspHorizontalAmbientCurve (Y : ℝ) :
""".replace("\n theorem", "\ntheorem"),
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  simpa [cuspHorizontalAmbientCurve] using
    hreal.add_const ((Y : ℂ) * Complex.I)

theorem contDiff_cuspHorizontalAmbientCurve (Y : ℝ) :
""",
        "Mock2 Advanced differentiate the horizontal cusp line through ofRealCLM",
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
        "Mock2 Advanced prove horizontal cusp smoothness compositionally",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    directionalDerivative_apply, upperLift_apply, d1]
""",
        """  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    directionalDerivative_apply, upperLift_apply, d1]
  ring
""",
        "FunctionalAnalysis close the localized product rule by commutativity",
    )
    fa = replace_exact(
        fa,
        """  rw [directionalDerivative_localizeLeft f hf v ξ,
    integral_add
      (core_integrable
        (localizeLeft (fun z => d1 f z ξ)
          (RealSmooth.d1_constDirection hf ξ) v))
      (core_integrable
        (localizeLeft f hf (directionalDerivative ξ v)))] at hzero
""",
        """  rw [directionalDerivative_localizeLeft f hf v ξ] at hzero
  change (∫ w : ℂ,
      localizeLeft (fun z => d1 f z ξ)
          (RealSmooth.d1_constDirection hf ξ) v w +
        localizeLeft f hf (directionalDerivative ξ v) w) = 0 at hzero
  rw [integral_add
      (core_integrable
        (localizeLeft (fun z => d1 f z ξ)
          (RealSmooth.d1_constDirection hf ξ) v))
      (core_integrable
        (localizeLeft f hf (directionalDerivative ξ v)))] at hzero
""",
        "FunctionalAnalysis expose pointwise addition before integral_add",
    )
    fa = replace_exact(
        fa,
        """        localizeLeft (HalfWeightDifferentialOperators.dx f) RealSmooth.dx hf v w) =
""",
        """        localizeLeft (HalfWeightDifferentialOperators.dx f)
          (RealSmooth.dx hf) v w) =
""",
        "FunctionalAnalysis apply the horizontal smoothness proof to f",
    )
    fa = replace_exact(
        fa,
        """        localizeLeft (HalfWeightDifferentialOperators.dy f) RealSmooth.dy hf v w) =
""",
        """        localizeLeft (HalfWeightDifferentialOperators.dy f)
          (RealSmooth.dy hf) v w) =
""",
        "FunctionalAnalysis apply the vertical smoothness proof to f",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
