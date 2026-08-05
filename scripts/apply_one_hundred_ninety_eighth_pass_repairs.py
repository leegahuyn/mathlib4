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
    m2a = replace_exact(
        m2a,
        """inductive Gamma2Rep
  | id
  | t
  | s
  | ts
  | stInv
  | tstInv
  deriving DecidableEq, Fintype, Repr
""",
        """inductive Gamma2Rep
  | id
  | t
  | s
  | ts
  | stInv
  | tstInv
  deriving DecidableEq, Repr

instance : Fintype Gamma2Rep where
  elems := { .id, .t, .s, .ts, .stInv, .tstInv }
  complete x := by cases x <;> simp
""",
        "Mock2 Advanced provide the six-element Fintype explicitly",
    )
    m2a = replace_exact(
        m2a,
        """theorem reducedRep_injective : Function.Injective reducedRep := by
  intro r s hrs
  have h00 := congrArg (fun A : ModTwoSpecialLinear => A 0 0) hrs
  have h01 := congrArg (fun A : ModTwoSpecialLinear => A 0 1) hrs
  have h10 := congrArg (fun A : ModTwoSpecialLinear => A 1 0) hrs
  have h11 := congrArg (fun A : ModTwoSpecialLinear => A 1 1) hrs
  cases r <;> cases s <;>
    simp_all [reducedRep, repMatrix,
      Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
      ModularGroup.coe_T, ModularGroup.coe_T_inv, Matrix.mul_fin_two]
""",
        """theorem reducedRep_injective : Function.Injective reducedRep := by
  decide
""",
        "Mock2 Advanced verify reduced representative injectivity finitely",
    )
    m2a = replace_exact(
        m2a,
        """  rw [map_mul, map_inv]
  change (reducedRep r)⁻¹ * modTwoReduction g = 1
  rw [hr, inv_mul]
""",
        """  rw [map_mul, map_inv]
  change (reducedRep r)⁻¹ * modTwoReduction g = 1
  simpa [hr]
""",
        "Mock2 Advanced replace the removed inv_mul rewrite",
    )
    m2a = replace_exact(
        m2a,
        """  rw [map_mul, map_inv]
  change modTwoReduction g * (reducedRep r)⁻¹ = 1
  rw [← hr, mul_inv]
""",
        """  rw [map_mul, map_inv]
  change modTwoReduction g * (reducedRep r)⁻¹ = 1
  simpa [← hr]
""",
        "Mock2 Advanced replace the removed mul_inv rewrite",
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
  have hraw := UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z
  rw [hdetC] at hraw
  simpa [hfun, hdenom, one_div] using hraw
""",
        "FunctionalAnalysis cast determinant one before normalizing the derivative",
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
    fa = replace_exact(
        fa,
        """  rw [dx_inverseEtaPaperOrbitFactor, dy_inverseEtaPaperOrbitFactor]
  ring_nf
  simp [Complex.I_sq]
  <;> ring
""",
        """  rw [dx_inverseEtaPaperOrbitFactor, dy_inverseEtaPaperOrbitFactor]
  ring_nf
""",
        "FunctionalAnalysis remove tactics after the antiholomorphic goal closes",
    )
    fa = replace_exact(
        fa,
        """      _ = 2 * Complex.I * q * c * j * F * u +
          F * j ^ 2 * Az := by
        field_simp [hj]
        ring
""",
        """      _ = 2 * Complex.I * q * c * j * F * u +
          F * j ^ 2 * Az := by
        field_simp [hj]
""",
        "FunctionalAnalysis remove the tactic after field_simp closes the goal",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
