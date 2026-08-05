from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
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
        """theorem denominator_mul (γ δ : Gamma2) (τ : H) :
    denominator (γ * δ) τ =
      denominator γ (δ • τ) * denominator δ τ := by
  unfold denominator
  rw [gammaGL_mul, ← gammaGL_smul δ τ]
  simpa [UpperHalfPlane.σ, gammaGL_det_pos] using
    (UpperHalfPlane.denom_cocycle'
      (gammaGL γ) (gammaGL δ) τ)
""",
        """theorem denominator_mul (γ δ : Gamma2) (τ : H) :
    denominator (γ * δ) τ =
      denominator γ (δ • τ) * denominator δ τ := by
  unfold denominator
  rw [gammaGL_mul]
  have h := UpperHalfPlane.denom_cocycle'
    (gammaGL γ) (gammaGL δ) τ
  have hsmul :
      UpperHalfPlane.smulAux (gammaGL δ) τ = δ • τ := by
    rfl
  rw [hsmul] at h
  simpa [UpperHalfPlane.σ, gammaGL_det_pos] using h
""",
        "Mock2 identify the raw GL action inside the denominator cocycle",
    )
    m2 = replace_exact(
        m2,
        """local instance : NormedSpace ℂ ℂ :=
  RCLike.innerProductSpace.toNormedSpace
""",
        """attribute [local instance 2000]
  RCLike.innerProductSpace.toNormedSpace
""",
        "Mock2 prioritize Mathlib's existing complex NormedSpace instance",
    )
    m2 = replace_exact(
        m2,
        """  simpa [automorphyFactor] using
    (contMDiff_const.mul (B.smooth γ))
""",
        """  simpa [automorphyFactor, Pi.mul_apply] using
    (contMDiff_const.mul (B.smooth γ))
""",
        "Mock2 normalize pointwise multiplication in automorphy smoothness",
    )
    m2 = replace_exact(
        m2,
        """  have hDifferentiable :
      DifferentiableOn ℂ ModularForm.eta upperHalfPlaneSet :=
    fun z hz =>
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).
        differentiableWithinAt
  have hContDiffOn :
      ContDiffOn ℂ ∞ ModularForm.eta upperHalfPlaneSet :=
    hDifferentiable.contDiffOn isOpen_upperHalfPlaneSet
  have hContDiffAt :
      ContDiffAt ℂ ∞ ModularForm.eta (τ : ℂ) :=
    (hContDiffOn (τ : ℂ) τ.2).contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
""",
        """  have hDifferentiable :
      DifferentiableOn ℂ ModularForm.eta
        UpperHalfPlane.upperHalfPlaneSet :=
    fun z hz =>
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).
        differentiableWithinAt
  have hContDiffOn :
      ContDiffOn ℂ ∞ ModularForm.eta
        UpperHalfPlane.upperHalfPlaneSet :=
    hDifferentiable.contDiffOn
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hContDiffAt :
      ContDiffAt ℂ ∞ ModularForm.eta (τ : ℂ) :=
    (hContDiffOn (τ : ℂ) τ.2).contDiffAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.2)
""",
        "Mock2 qualify the upper-half-plane domain in eta smoothness",
    )
    M2.write_text(m2, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [hConjPow]
        field_simp [hjc]
""",
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        field_simp [hjc]
""",
        "FunctionalAnalysis cancel the conjugate square directly",
    )
    fa = replace_exact(
        fa,
        """      _ = 2 * Complex.I * q * c / j * F * u + F * Az := by
        rw [fixedPhaseFactor_holomorphic_direction n γ z]
        simp only [q, c, j, F, Az]
""",
        """      _ = 2 * Complex.I * q * c / j * F * u + F * Az := by
        rw [fixedPhaseFactor_holomorphic_direction n γ z]
""",
        "FunctionalAnalysis stop after the holomorphic rewrite closes",
    )
    fa = replace_exact(
        fa,
        """  rw [lowerRaw, heightC_gammaTwo_smul,
    hf γ z, inverseEtaPaperOrbitFactor_sub_one]
""",
        """  rw [lowerRaw, heightC_gammaTwo_smul,
    inverseEtaPaperOrbitFactor_sub_one]
""",
        "FunctionalAnalysis omit the absent zeroth-order factor from lowering",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
