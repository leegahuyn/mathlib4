from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(
            f"{label}: expected exactly {expected} match(es), found {count}"
        )
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """theorem etaResidual_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (etaResidual γ) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
    (fun τ : H => etaRatio γ τ ^ 2 * denominator γ τ)
  exact ((etaRatio_contMDiff γ).pow 2).mul
    (by simpa [denominator] using
      (UpperHalfPlane.contMDiff_denom (gammaGL γ)))
""",
        """theorem etaResidual_continuous (γ : Gamma2) :
    Continuous (etaResidual γ) := by
  change Continuous (fun τ : H =>
    etaRatio γ τ ^ 2 *
      UpperHalfPlane.denom (gammaGL γ) (τ : ℂ))
  exact ((etaRatio_contMDiff γ).continuous.pow 2).mul
    (UpperHalfPlane.contMDiff_denom (gammaGL γ)).continuous
""",
        "Mock2 prove residual continuity before residual smoothness",
    )
    m2 = replace_exact(
        m2,
        """theorem etaResidualUnit_continuous (γ : Gamma2) :
    Continuous (etaResidualUnit γ) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (etaResidual γ)
    exact (etaResidual_contMDiff γ).continuous
  · change Continuous (fun τ => (etaResidual γ τ)⁻¹)
    exact (etaResidual_contMDiff γ).continuous.inv₀
      (etaResidual_ne_zero γ)
""",
        """theorem etaResidualUnit_continuous (γ : Gamma2) :
    Continuous (etaResidualUnit γ) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (etaResidual γ)
    exact etaResidual_continuous γ
  · change Continuous (fun τ => (etaResidual γ τ)⁻¹)
    exact (etaResidual_continuous γ).inv₀
      (etaResidual_ne_zero γ)
""",
        "Mock2 use direct residual continuity for the unit-valued residual",
    )
    m2 = replace_exact(
        m2,
        """  have hCoe := congrArg
    (fun z : rootsOfUnity 12 ℂ => (((z : ℂˣ) : ℂ))) hRoot
  simpa [etaResidualRoot, etaResidualUnit] using hCoe

theorem etaResidualUnit_eq_base (γ : Gamma2) (τ : H) :
""",
        """  have hCoe := congrArg
    (fun z : rootsOfUnity 12 ℂ => (((z : ℂˣ) : ℂ))) hRoot
  simpa [etaResidualRoot, etaResidualUnit] using hCoe

/-- The residual is smooth because connectedness makes it constant. -/
theorem etaResidual_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (etaResidual γ) := by
  have hfun : etaResidual γ =
      fun _ : H => etaResidual γ UpperHalfPlane.I := by
    funext τ
    exact etaResidual_eq_base γ τ
  rw [hfun]
  exact contMDiff_const

theorem etaResidualUnit_eq_base (γ : Gamma2) (τ : H) :
""",
        "Mock2 derive residual smoothness from its proved constancy",
    )
    m2 = replace_exact(
        m2,
        """    _ = (denominatorUnit γ τ)⁻¹ *
        (etaRatioUnit γ τ ^ 2 * (etaRatioUnit γ τ ^ 2)⁻¹) := by
      rw [mul_inv_rev]
      ac_rfl
""",
        """    _ = (denominatorUnit γ τ)⁻¹ *
        (etaRatioUnit γ τ ^ 2 * (etaRatioUnit γ τ ^ 2)⁻¹) := by
      rw [_root_.mul_inv_rev]
      ac_rfl
""",
        "Mock2 disambiguate the group inverse multiplication lemma",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  simpa only [zero_add, mul_one] using
    (hasDerivAt_const t (-(1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  change HasDerivAt
    ((fun _ : ℝ => (-(1 : ℝ) / 2 : ℂ)) +
      fun y : ℝ => Complex.I * (y : ℂ)) Complex.I t
  simpa only [id_eq, zero_add, mul_one] using
    (hasDerivAt_const t (-(1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        "Mock2 Advanced state the left derivative in pointwise-addition form",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  simpa only [zero_add, mul_one] using
    (hasDerivAt_const t ((1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  change HasDerivAt
    ((fun _ : ℝ => ((1 : ℝ) / 2 : ℂ)) +
      fun y : ℝ => Complex.I * (y : ℂ)) Complex.I t
  simpa only [id_eq, zero_add, mul_one] using
    (hasDerivAt_const t ((1 : ℝ) / 2 : ℂ)).add
      (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal)
""",
        "Mock2 Advanced state the right derivative in pointwise-addition form",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        change Bw = star (j ^ 2) * star (j ^ 2)⁻¹ * Bw
        rw [mul_inv_cancel₀ hs, one_mul]
""",
        """        calc
          Bw = 1 * Bw := by rw [one_mul]
          _ = (star (j ^ 2) * star (j ^ 2)⁻¹) * Bw := by
            rw [mul_inv_cancel₀ hs]
          _ = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw) := by
            rw [mul_assoc]
""",
        "FunctionalAnalysis cancel the conjugate inverse through an explicit calc",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
