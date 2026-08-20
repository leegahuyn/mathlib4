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
        """attribute [local instance 2000]
  RCLike.innerProductSpace.toNormedSpace
""",
        """local attribute [-instance]
  instNormedSpaceComplex_primalitySheafVerification
""",
        "Mock2 disable the project-specific complex NormedSpace locally",
    )
    m2 = replace_exact(
        m2,
        """theorem automorphyFactor_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
      (fun τ : H => (M.automorphyFactor γ τ : ℂ)) := by
  simpa [automorphyFactor, Pi.mul_apply] using
    (contMDiff_const.mul (B.smooth γ))
""",
        """theorem automorphyFactor_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
      (fun τ : H => (M.automorphyFactor γ τ : ℂ)) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
    (fun τ : H => (M.nu γ : ℂ) * (B.value γ τ : ℂ))
  exact contMDiff_const.mul (B.smooth γ)
""",
        "Mock2 state automorphy-factor smoothness pointwise",
    )
    m2 = replace_exact(
        m2,
        """    fun z hz =>
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).
        differentiableWithinAt
""",
        """    fun z hz =>
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
""",
        "Mock2 keep eta differentiability field notation on one line",
    )
    m2 = replace_exact(
        m2,
        """  filter_upwards
      [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simp [etaValue, Function.comp_def, hz]
""",
        """  filter_upwards
      [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  change ModularForm.eta ((UpperHalfPlane.ofComplex z : H) : ℂ) =
    ModularForm.eta z
  simpa only [Function.comp_apply, id_eq] using
    congrArg ModularForm.eta hz
""",
        "Mock2 transport eta equality through the chart identity",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  have hcoeff :
      (-(1 : ℝ) / 2) * (-(1 : ℝ) / 2) = (1 : ℝ) / 4 := by
    norm_num
  simpa [firstDerivative, secondDerivative, mul_assoc, hcoeff] using
    (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2)
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  let c : ℝ := -(1 : ℝ) / 2
  have hcoeff : c * firstDerivative x = secondDerivative x := by
    dsimp [c, firstDerivative, secondDerivative]
    ring
  change HasDerivAt (fun y : ℝ => c * W y) (secondDerivative x) x
  have h := (hasDerivAt_W x).const_mul c
  rw [hcoeff] at h
  exact h
""",
        "Mock2 Advanced transport the exact Whittaker derivative coefficient",
    )
    m2a = replace_exact(
        m2a,
        """  have htransport :
      g • (repMatrix r • x) = repMatrix s • y := by
    simp [g, mul_smul, hγ]
""",
        """  have hγ' :
      (((γ.1 : IntegralSpecialLinear) : GL (Fin 2) ℝ) • x) = y := by
    simpa only [ModularGroup.sl_moeb] using hγ
  have htransport :
      g • (repMatrix r • x) = repMatrix s • y := by
    simp [g, mul_smul, hγ']
""",
        "Mock2 Advanced transport the Gamma2 action through its real GL matrix",
    )
    m2a = replace_exact(
        m2a,
        """  rw [htransport] at hfundamental
  subst s
  exact (Homeomorph.smul (repMatrix r)).injective hfundamental
""",
        """  rw [htransport] at hfundamental
  subst s
  have hcancel := congrArg
    (fun z : UpperHalfPlane => (repMatrix r)⁻¹ • z) hfundamental
  simpa only [← mul_smul, inv_mul, one_smul] using hcancel
""",
        "Mock2 Advanced cancel the cell action algebraically",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        field_simp [hjc]
""",
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [star_inv, hConjPow]
        field_simp [hjc]
""",
        "FunctionalAnalysis rewrite star of an inverse before cancellation",
    )
    fa = replace_exact(
        fa,
        """  rw [lowerRaw, heightC_gammaTwo_smul,
    inverseEtaPaperOrbitFactor_sub_one]
  dsimp [F, j, y, Bz, Bw] at hAlgebra ⊢
  ring_nf at hAlgebra ⊢
  exact hAlgebra
""",
        """  simp only [lowerRaw]
  rw [heightC_gammaTwo_smul,
    inverseEtaPaperOrbitFactor_sub_one]
  dsimp [F, j, y, Bz, Bw] at hAlgebra ⊢
  ring_nf at hAlgebra ⊢
  exact hAlgebra
""",
        "FunctionalAnalysis unfold both lowering operators before normalization",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
