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
        """attribute [local instance 2000]
  RCLike.innerProductSpace.toNormedSpace
""",
        """local instance : NormedSpace ℂ ℂ :=
  (RCLike.innerProductSpace ℂ).toNormedSpace
""",
        "Mock2 select the concrete RCLike complex NormedSpace instance",
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
        "Mock2 expose the pointwise automorphy factor before smoothness",
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
        "Mock2 repair the eta differentiability field-notation boundary",
    )
    m2 = replace_exact(
        m2,
        """  filter_upwards
      [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simp [etaValue, Function.comp_def, hz]
""",
        """  filter_upwards
      [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simpa [Function.comp_def] using congrArg ModularForm.eta hz
""",
        "Mock2 transport eta across the local inverse chart explicitly",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1 <;>
    ring
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  · rfl
  · rw [firstDerivative]
    ring
""",
        "Mock2 Advanced prove the exact second Whittaker coefficient",
    )
    m2a = replace_exact(
        m2a,
        """  let g : IntegralSpecialLinear :=
    repMatrix s * γ.1 * (repMatrix r)⁻¹
  have htransport :
      g • (repMatrix r • x) = repMatrix s • y := by
    simp [g, mul_smul, hγ]
""",
        """  let g : IntegralSpecialLinear :=
    repMatrix s * γ.1 * (repMatrix r)⁻¹
  have hγReal :
      ((Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ)
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) • x = y := by
    simpa [gamma2Act] using hγ
  have htransport :
      g • (repMatrix r • x) = repMatrix s • y := by
    simp [g, mul_smul, hγReal]
""",
        "Mock2 Advanced expose the real Gamma2 action in cell transport",
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
    (fun w : UpperHalfPlane => (repMatrix r)⁻¹ • w) hfundamental
  simpa [mul_smul] using hcancel
""",
        "Mock2 Advanced cancel the cell representative by the inverse action",
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
        rw [Complex.conj_inv, hConjPow]
        field_simp [hjc]
""",
        "FunctionalAnalysis normalize the conjugate inverse before cancellation",
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
        "FunctionalAnalysis unfold every lowerRaw occurrence before normalization",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
