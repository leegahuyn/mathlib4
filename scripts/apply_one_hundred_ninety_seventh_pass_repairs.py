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
        """@[simp] theorem gammaGL_matrix_det (γ : Gamma2) :
    (gammaGL γ).val.det = 1 := by
  simp [gammaGL]
""",
        """@[simp] theorem gammaGL_matrix_det (γ : Gamma2) :
    (gammaGL γ).val.det = 1 := by
  unfold gammaGL
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  norm_num
""",
        "Mock2 prove the real determinant-one identity through val_det_apply",
    )
    m2 = replace_exact(
        m2,
        """@[simp] theorem gammaGL_mul (γ δ : Gamma2) :
    gammaGL (γ * δ) = gammaGL γ * gammaGL δ := by
  change (((γ.1 * δ.1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
    (γ.1 : GL (Fin 2) ℝ) * (δ.1 : GL (Fin 2) ℝ)
  simp

/-- Every real representative of an element of `Γ(2)` has determinant one. -/
""",
        """@[simp] theorem gammaGL_mul (γ δ : Gamma2) :
    gammaGL (γ * δ) = gammaGL γ * gammaGL δ := by
  change (((γ.1 * δ.1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
    (γ.1 : GL (Fin 2) ℝ) * (δ.1 : GL (Fin 2) ℝ)
  simp

@[simp] theorem gammaGL_smul (γ : Gamma2) (τ : H) :
    gammaGL γ • τ = γ • τ := by
  rfl

/-- Every real representative of an element of `Γ(2)` has determinant one. -/
""",
        "Mock2 expose the definitional equality between subgroup and GL actions",
    )
    m2 = replace_exact(
        m2,
        """theorem gammaGL_det_pos (γ : Gamma2) :
    0 < (gammaGL γ).det.val := by
  simp [gammaGL]
""",
        """theorem gammaGL_det_pos (γ : Gamma2) :
    0 < (gammaGL γ).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, gammaGL_matrix_det]
  norm_num
""",
        "Mock2 derive positive determinant from determinant one",
    )
    m2 = replace_exact(
        m2,
        """theorem denominator_mul (γ δ : Gamma2) (τ : H) :
    denominator (γ * δ) τ =
      denominator γ (δ • τ) * denominator δ τ := by
  simpa [denominator, UpperHalfPlane.σ, gammaGL_det_pos] using
    (UpperHalfPlane.denom_cocycle'
      (gammaGL γ) (gammaGL δ) τ)
""",
        """theorem denominator_mul (γ δ : Gamma2) (τ : H) :
    denominator (γ * δ) τ =
      denominator γ (δ • τ) * denominator δ τ := by
  simpa [denominator, UpperHalfPlane.σ, gammaGL_det_pos,
    gammaGL_smul] using
    (UpperHalfPlane.denom_cocycle'
      (gammaGL γ) (gammaGL δ) τ)
""",
        "Mock2 normalize the denominator cocycle through the subgroup action",
    )
    m2 = replace_exact(
        m2,
        """  symm
  simpa [deckDerivative, denominator, one_div] using
    (UpperHalfPlane.deriv_smul
      (by simpa using gammaGL_det_pos γ) τ)
""",
        """  symm
  simpa [deckDerivative, denominator, one_div] using
    (UpperHalfPlane.deriv_smul (g := gammaGL γ)
      (gammaGL_det_pos γ) τ)
""",
        "Mock2 pass determinant positivity directly to the deck derivative",
    )
    m2 = replace_exact(
        m2,
        """theorem deckDerivative_mul (γ δ : Gamma2) (τ : H) :
    deckDerivative (γ * δ) τ =
      deckDerivative γ (δ • τ) * deckDerivative δ τ := by
  simp [deckDerivative, denominator_mul, mul_zpow]
""",
        """theorem deckDerivative_mul (γ δ : Gamma2) (τ : H) :
    deckDerivative (γ * δ) τ =
      deckDerivative γ (δ • τ) * deckDerivative δ τ := by
  unfold deckDerivative
  rw [denominator_mul, mul_zpow]
""",
        "Mock2 preserve the zpow product before simplification",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  change HasDerivAt (fun y : ℝ => Real.exp (-y / 2))
    (-(1 / 2) * Real.exp (-x / 2)) x
  convert ((hasDerivAt_id x).neg.div_const 2).exp using 1 <;> ring
""",
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  unfold W firstDerivative
  convert ((hasDerivAt_id x).neg.div_const 2).exp using 1 <;> ring
""",
        "Mock2 Advanced unfold the Whittaker kernel before the chain rule",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1 <;>
    simp [firstDerivative, secondDerivative] <;> ring
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  norm_num [div_eq_mul_inv] <;> ring
""",
        "Mock2 Advanced normalize the exact rational second derivative coefficient",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hfun : gammaTwoMoebiusChart γ =
      fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ) := by
    funext w
    rfl
  rw [hfun]
  convert (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z) using 1 <;>
    simp [inverseEtaPaperOrbitDenom, g, hdet, one_div]
""",
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
        "FunctionalAnalysis normalize the determinant-one Mobius derivative",
    )
    fa = replace_exact(
        fa,
        """/-- Canonical fixed-phase core at orbit index `n`. -/
abbrev InverseEtaFixedPhaseCore (n : ℤ) :=
  inverseEtaFixedPhaseStableCoreSubmodule n
""",
        """/-- Canonical fixed-phase core at orbit index `n`. -/
noncomputable abbrev InverseEtaFixedPhaseCore (n : ℤ) :=
  inverseEtaFixedPhaseStableCoreSubmodule n
""",
        "FunctionalAnalysis mark the stable-core abbreviation noncomputable",
    )
    fa = replace_exact(
        fa,
        """  rw [hCutoffInvariant γ z, orbitSection.covariance γ z]
""",
        """  rw [hCutoffInvariant γ z,
    WeightSection.covariance orbitSection γ z]
""",
        "FunctionalAnalysis call the weight-section covariance theorem explicitly",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
