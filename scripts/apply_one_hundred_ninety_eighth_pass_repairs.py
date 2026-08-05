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
  simpa [denominator, UpperHalfPlane.σ, gammaGL_det_pos,
    gammaGL_smul] using
    (UpperHalfPlane.denom_cocycle'
      (gammaGL γ) (gammaGL δ) τ)
""",
        """theorem denominator_mul (γ δ : Gamma2) (τ : H) :
    denominator (γ * δ) τ =
      denominator γ (δ • τ) * denominator δ τ := by
  unfold denominator
  rw [gammaGL_mul, ← gammaGL_smul δ τ]
  exact UpperHalfPlane.denom_cocycle'
    (gammaGL γ) (gammaGL δ) τ
""",
        "Mock2 identify the subgroup action before applying the denominator cocycle",
    )
    m2 = replace_exact(
        m2,
        """theorem denominatorUnit_mul (γ δ : Gamma2) (τ : H) :
    denominatorUnit (γ * δ) τ =
      denominatorUnit γ (δ • τ) * denominatorUnit δ τ := by
  apply Units.ext
  simp [denominator_mul]

/-- The complex derivative of the deck map, in the standard upper-half-plane
""",
        """theorem denominatorUnit_mul (γ δ : Gamma2) (τ : H) :
    denominatorUnit (γ * δ) τ =
      denominatorUnit γ (δ • τ) * denominatorUnit δ τ := by
  apply Units.ext
  simp [denominator_mul]

local instance : NormedSpace ℂ ℂ :=
  RCLike.innerProductSpace.toNormedSpace ℂ

/-- The complex derivative of the deck map, in the standard upper-half-plane
""",
        "Mock2 use the standard complex NormedSpace instance for deck calculus",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  unfold W firstDerivative
  convert ((hasDerivAt_id x).neg.div_const 2).exp using 1 <;> ring
""",
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  unfold firstDerivative
  convert ((hasDerivAt_id x).neg.div_const 2).exp using 1
  · funext y
    simp [W, div_eq_mul_inv]
  · simp [W, div_eq_mul_inv, mul_comm]
""",
        "Mock2 Advanced prove the Whittaker first derivative extensionally",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  norm_num [div_eq_mul_inv] <;> ring
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  change HasDerivAt (fun y : ℝ => (-(1 : ℝ) / 2) * W y)
    ((1 : ℝ) / 4 * W x) x
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  ring
""",
        "Mock2 Advanced prove the Whittaker second derivative by constant multiplication",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hdetGL : g.det.val = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet
  have hfun : gammaTwoMoebiusChart γ =
      fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ) := by
    funext w
    rfl
  have hdenom : inverseEtaPaperOrbitDenom γ z =
      UpperHalfPlane.denom g z := by
    rfl
  rw [hfun, hdenom]
  simpa [one_div, hdetGL] using
    (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z)
""",
        """  have hdetC : (g.val.det : ℂ) = 1 := by
    exact_mod_cast hdet
  have hfun : gammaTwoMoebiusChart γ =
      fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ) := by
    funext w
    rfl
  have hdenom : inverseEtaPaperOrbitDenom γ z =
      UpperHalfPlane.denom g z := by
    rfl
  rw [hfun, hdenom]
  simpa [one_div, hdetC] using
    (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z)
""",
        "FunctionalAnalysis cast the determinant-one identity into the derivative field",
    )
    fa = replace_exact(
        fa,
        """  apply Complex.ext <;>
    simp [inverseEtaPaperOrbitDenom, inverseEtaPaperOrbitLowerLeft,
      UpperHalfPlane.denom, heightC, Complex.normSq_apply] <;>
    ring
""",
        """  apply Complex.ext <;>
    simp [inverseEtaPaperOrbitDenom, inverseEtaPaperOrbitLowerLeft,
      UpperHalfPlane.denom, heightC, Complex.normSq_apply, pow_two,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
    ring
""",
        "FunctionalAnalysis expand real and imaginary parts of the denominator square",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
