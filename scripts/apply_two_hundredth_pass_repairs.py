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
  calc
    denominator (γ * δ) τ =
        denominator γ (gammaGL δ • τ) * denominator δ τ := by
      simpa [denominator, gammaGL_mul, UpperHalfPlane.σ,
        gammaGL_det_pos] using
        (UpperHalfPlane.denom_cocycle'
          (gammaGL γ) (gammaGL δ) τ)
    _ = denominator γ (δ • τ) * denominator δ τ := by
      rw [gammaGL_smul]
""",
        "Mock2 separate the GL denominator cocycle from the subgroup action",
    )
    m2 = replace_exact(
        m2,
        """local instance : NormedSpace ℂ ℂ :=
  RCLike.innerProductSpace.toNormedSpace
""",
        """attribute [local instance 2000]
  RCLike.innerProductSpace.toNormedSpace
""",
        "Mock2 prioritize the exact Mathlib complex NormedSpace instance",
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

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  change HasDerivAt (fun y : ℝ => (-(1 : ℝ) / 2) * W y)
    ((1 : ℝ) / 4 * W x) x
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  simp [firstDerivative]
  <;> ring
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  have hcoeff :
      (-(1 : ℝ) / 2) * firstDerivative x = secondDerivative x := by
    unfold firstDerivative secondDerivative
    ring
  rw [← hcoeff]
  simpa only [firstDerivative] using
    (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2)
""",
        "Mock2 Advanced isolate the exact second-derivative coefficient",
    )
    m2a = replace_exact(
        m2a,
        """theorem isClosed_closedCell (r : Gamma2Rep) : IsClosed (closedCell r) := by
  exact ModularGroup.isClosed_fd.preimage (continuous_const_smul _)
""",
        """theorem isClosed_closedCell (r : Gamma2Rep) : IsClosed (closedCell r) := by
  apply ModularGroup.isClosed_fd.preimage
  change Continuous (fun τ : UpperHalfPlane =>
    ((repMatrix r : IntegralSpecialLinear) : GL (Fin 2) ℝ) • τ)
  exact continuous_const_smul _
""",
        "Mock2 Advanced express closed-cell continuity through the real GL action",
    )
    m2a = replace_exact(
        m2a,
        """theorem isOpen_openCell (r : Gamma2Rep) : IsOpen (openCell r) := by
  exact ModularGroup.isOpen_fdo.preimage (continuous_const_smul _)
""",
        """theorem isOpen_openCell (r : Gamma2Rep) : IsOpen (openCell r) := by
  apply ModularGroup.isOpen_fdo.preimage
  change Continuous (fun τ : UpperHalfPlane =>
    ((repMatrix r : IntegralSpecialLinear) : GL (Fin 2) ℝ) • τ)
  exact continuous_const_smul _
""",
        "Mock2 Advanced express open-cell continuity through the real GL action",
    )
    m2a = replace_exact(
        m2a,
        """theorem pairwise_disjoint_openCell :
    Pairwise (Disjoint on openCell) := by
""",
        """theorem pairwise_disjoint_openCell :
    Pairwise (fun r s => Disjoint (openCell r) (openCell s)) := by
""",
        "Mock2 Advanced replace the removed on-combinator syntax",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hBw : Bw = star j ^ 2 * F * Bz := by
    calc
      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [hConjPow]
        field_simp [hjc]
      _ = star j ^ 2 * (F * Bz) := by rw [hDerivative]
      _ = star j ^ 2 * F * Bz := by ring
""",
        """  have hBw : Bw = star j ^ 2 * F * Bz := by
    calc
      Bw = star (j ^ 2) *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [Complex.conj_inv]
        field_simp [hjc]
      _ = star (j ^ 2) * (F * Bz) := by rw [hDerivative]
      _ = star j ^ 2 * F * Bz := by
        rw [hConjPow]
        ring
""",
        "FunctionalAnalysis cancel the conjugate square before rewriting its power",
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
        "FunctionalAnalysis stop after the fixed-phase rewrite closes raising calculus",
    )
    fa = replace_exact(
        fa,
        """  dsimp [F, j, q, y, r, u, Az, Aw] at hAlgebra ⊢
  ring_nf at hAlgebra ⊢
  exact hAlgebra
""",
        """  dsimp [F, j, q, y, r, u, Az, Aw] at hAlgebra ⊢
  simpa [inverseEtaPaperOrbitFactor, raiseRaw, mul_assoc,
    mul_left_comm, mul_comm] using hAlgebra
""",
        "FunctionalAnalysis normalize the final raising identity definitionally",
    )
    fa = replace_exact(
        fa,
        """  rw [lowerRaw, heightC_gammaTwo_smul,
    hf γ z, inverseEtaPaperOrbitFactor_sub_one]
  dsimp [F, j, y, Bz, Bw] at hAlgebra ⊢
  ring_nf at hAlgebra ⊢
  exact hAlgebra
""",
        """  rw [lowerRaw, heightC_gammaTwo_smul,
    inverseEtaPaperOrbitFactor_sub_one]
  dsimp [F, j, y, Bz, Bw] at hAlgebra ⊢
  simpa [inverseEtaPaperOrbitFactor, lowerRaw, mul_assoc,
    mul_left_comm, mul_comm] using hAlgebra
""",
        "FunctionalAnalysis remove the absent function-value rewrite and normalize lowering",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
