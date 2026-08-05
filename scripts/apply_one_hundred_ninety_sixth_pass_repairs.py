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
        """  abstract_prime_index_map_is_input :
    ∀ (X : BalancedQGaugeSheafCategory.{u, v} Open) (U : Open),
      X.balancedSheaf.Field U → ∀ p : PrimeIndex, X.PrimeProfile p
""",
        """  abstract_prime_index_map_is_input :
    ∀ (X : BalancedQGaugeSheafCategory.{u, v} Open) (U : Open),
      ∃ primeIndexMap :
          X.balancedSheaf.Field U → ∀ p : PrimeIndex, X.PrimeProfile p,
        primeIndexMap = X.primeIndexMap U
""",
        "Mock2 turn the Prop certificate data projection into an exact input witness",
    )
    m2 = replace_exact(
        m2,
        """    { abstract_prime_index_map_is_input := fun X U => X.primeIndexMap U
""",
        """    { abstract_prime_index_map_is_input := fun X U =>
        ⟨X.primeIndexMap U, rfl⟩
""",
        "Mock2 construct the exact prime-index input witness",
    )
    m2 = replace_exact(
        m2,
        """/-- The canonical projection `π : ℍ → Γ(2) \\ ℍ`. -/
def quotientMap (τ : H) : X :=
  Quotient.mk' τ

@[simp] theorem quotientMap_smul (γ : Gamma2) (τ : H) :
    quotientMap (γ • τ) = quotientMap τ := by
  change Definition11.quotientMk (γ • τ) = Definition11.quotientMk τ
  exact Definition11.quotientMk_smul γ τ

/-- The quotient projection as a bundled continuous map. -/
def quotientMapContinuous : C(H, X) where
  toFun := quotientMap
  continuous_toFun := continuous_quotient_mk'
""",
        """/-- The canonical projection `π : ℍ → Γ(2) \\ ℍ`. -/
def quotientMap : H → X :=
  Definition11.quotientMk

@[simp] theorem quotientMap_smul (γ : Gamma2) (τ : H) :
    quotientMap (γ • τ) = quotientMap τ := by
  exact Definition11.quotientMk_smul γ τ

/-- The quotient projection as a bundled continuous map. -/
def quotientMapContinuous : C(H, X) where
  toFun := quotientMap
  continuous_toFun := by
    change Continuous (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))
    exact continuous_quotient_mk'
""",
        "Mock2 reuse the canonical orbit projection and its quotient topology",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem sinh_le_half_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x / 2 := by
  have hsinh :
      2 * Real.sinh x = Real.exp x - Real.exp (-x) := by
    have h := congrArg Complex.re (Complex.two_sinh (x : ℂ))
    simpa [Real.sinh, ← Complex.ofReal_neg] using h
  linarith [Real.exp_pos (-x)]
""",
        """theorem sinh_le_half_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x / 2 := by
  rw [Real.sinh_eq]
  linarith [Real.exp_pos (-x)]
""",
        "Mock2 Advanced use the public real sinh exponential formula",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  simpa [W, firstDerivative, div_eq_mul_inv, mul_comm] using
    ((hasDerivAt_id x).neg.div_const 2).exp
""",
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  change HasDerivAt (fun y : ℝ => Real.exp (-y / 2))
    (-(1 / 2) * Real.exp (-x / 2)) x
  convert ((hasDerivAt_id x).neg.div_const 2).exp using 1 <;> ring
""",
        "Mock2 Advanced expose the Gaussian weight before differentiating",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  ring
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1 <;>
    simp [firstDerivative, secondDerivative] <;> ring
""",
        "Mock2 Advanced normalize the second Gaussian derivative",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem gammaTwoMoebiusChart_hasStrictDerivAt
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    HasStrictDerivAt (gammaTwoMoebiusChart γ)
      (1 / inverseEtaPaperOrbitDenom γ z ^ 2) (z : ℂ) := by
  let g : GL (Fin 2) ℝ :=
    (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) :
      GL (Fin 2) ℝ)
  have hdet : g.val.det = 1 := by
    simpa [g] using inverseEtaPaperOrbit_det_eq_one γ
  have hg : 0 < g.det.val := by
    simpa [g] using inverseEtaPaperOrbit_det_pos γ
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, g, hdet, one_div] using
    (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z)
""",
        """theorem gammaTwoMoebiusChart_hasStrictDerivAt
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    HasStrictDerivAt (gammaTwoMoebiusChart γ)
      (1 / inverseEtaPaperOrbitDenom γ z ^ 2) (z : ℂ) := by
  let g : GL (Fin 2) ℝ :=
    (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) :
      GL (Fin 2) ℝ)
  have hdet : g.val.det = 1 := by
    simpa [g] using inverseEtaPaperOrbit_det_eq_one γ
  have hg : 0 < g.det.val := by
    simpa [g] using inverseEtaPaperOrbit_det_pos γ
  have hfun : gammaTwoMoebiusChart γ =
      fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ) := by
    funext w
    rfl
  rw [hfun]
  convert (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z) using 1 <;>
    simp [inverseEtaPaperOrbitDenom, g, hdet, one_div]
""",
        "FunctionalAnalysis identify the Mobius chart with the GL action",
    )
    fa = replace_exact(
        fa,
        """  section : ∀ a : ℤ, core a →ₗ[ℂ] WeightSection (multiplier a)
  section_apply : ∀ a (u : core a) z,
    section a u z = (u : ℍ → ℂ) z
""",
        """  «section» : ∀ a : ℤ, core a →ₗ[ℂ] WeightSection (multiplier a)
  section_apply : ∀ a (u : core a) z,
    «section» a u z = (u : ℍ → ℂ) z
""",
        "FunctionalAnalysis escape the reserved section projection name",
    )
    fa = replace_exact(
        fa,
        """  exact (D.section a u).covariance γ z
""",
        """  exact (D.«section» a u).covariance γ z
""",
        "FunctionalAnalysis use the escaped section projection",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
