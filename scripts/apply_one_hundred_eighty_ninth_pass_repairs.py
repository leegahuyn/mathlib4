from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """@[ext] theorem ext {T₁ T₂ : FlatTransport D}
    (h : ∀ {r s : RadiusBase} (γ : RadiusPathClass r s)
      (u : Fibre D r), T₁.map γ u = T₂.map γ u) :
    T₁ = T₂ := by
  cases T₁ with
  | mk map₁ refl₁ trans₁ =>
      cases T₂ with
      | mk map₂ refl₂ trans₂ =>
          have hmap :
              (fun {r s : RadiusBase} (γ : RadiusPathClass r s) => map₁ γ) =
              (fun {r s : RadiusBase} (γ : RadiusPathClass r s) => map₂ γ) := by
            funext r s γ
            apply LinearEquiv.ext
            intro u
            exact h (r := r) (s := s) γ u
          cases hmap
          rfl
""",
        """@[ext] theorem ext {T₁ T₂ : FlatTransport D}
    (h : ∀ {r s : RadiusBase} (γ : RadiusPathClass r s)
      (u : Fibre D r), T₁.map γ u = T₂.map γ u) :
    T₁ = T₂ := by
  cases T₁ with
  | mk map₁ refl₁ trans₁ =>
      cases T₂ with
      | mk map₂ refl₂ trans₂ =>
          congr 1
          funext r s γ
          apply LinearEquiv.ext
          intro u
          exact h (r := r) (s := s) γ u
""",
        "Mock2 prove FlatTransport extensionality by constructor congruence",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """      rw [Complex.normSq_eq_conj_mul_self]
      change star (a n) * a n * 2 = a n * star (a n) * 2
      rw [mul_comm (star (a n)) (a n)]
""",
        """      rw [Complex.normSq_eq_conj_mul_self]
      ac_rfl
""",
        "Mock2 Advanced normalize the diagonal product associatively and commutatively",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        "/-- The genuine complex coordinate of the `Gamma(2)` Möbius action. -/\ndef gammaTwoMoebiusCoordinate",
        "/-- The genuine complex coordinate of the `Gamma(2)` Möbius action. -/\nnoncomputable def gammaTwoMoebiusCoordinate",
        "FunctionalAnalysis mark the GammaTwo coordinate noncomputable",
    )
    fa = replace_exact(
        fa,
        "/-- The same coordinate in the ambient open upper-half-plane chart. -/\ndef gammaTwoMoebiusChart",
        "/-- The same coordinate in the ambient open upper-half-plane chart. -/\nnoncomputable def gammaTwoMoebiusChart",
        "FunctionalAnalysis mark the GammaTwo chart noncomputable",
    )
    det_pos = """theorem inverseEtaPaperOrbit_det_pos
    (γ : GammaTwoQuotientGeometry.GammaTwo) :
    0 < (((((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) :
      GL (Fin 2) ℝ)).val.det) := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  norm_num
"""
    fa = replace_exact(
        fa,
        det_pos,
        det_pos + """

/-- The real determinant of an integral special-linear element is one. -/
@[simp] theorem inverseEtaPaperOrbit_det_eq_one
    (γ : GammaTwoQuotientGeometry.GammaTwo) :
    (((((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) :
      GL (Fin 2) ℝ)).val.det) = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  norm_num
""",
        "FunctionalAnalysis add the determinant-one normalization",
    )
    fa = replace_exact(
        fa,
        """  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, one_div] using
""",
        """  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, inverseEtaPaperOrbit_det_eq_one,
    one_div] using
""",
        "FunctionalAnalysis normalize the strict derivative determinant",
    )
    fa = replace_exact(
        fa,
        """    simpa using
      (gammaTwoMoebiusChart_hasStrictDerivAt γ (⟨w, hw⟩ : ℍ)).
        differentiableAt.differentiableWithinAt
""",
        """    have hDeriv :=
      (gammaTwoMoebiusChart_hasStrictDerivAt γ (⟨w, hw⟩ : ℍ)).differentiableAt
    exact hDeriv.differentiableWithinAt
""",
        "FunctionalAnalysis split the chart differentiability field chain",
    )
    fa = replace_exact(
        fa,
        """  simpa [RealSmooth, upperLift, gammaTwoMoebiusChart,
    Function.comp_def] using hSmooth
""",
        """  change ContDiffOn ℝ ∞ (gammaTwoMoebiusChart γ)
    UpperHalfPlane.upperHalfPlaneSet
  exact hSmooth
""",
        "FunctionalAnalysis expose the smooth chart goal",
    )
    fa = replace_exact(
        fa,
        """  have hFderiv :=
    (gammaTwoMoebiusChart_hasStrictDerivAt γ z).hasDerivAt.
      complexToReal_fderiv.fderiv
""",
        """  have hDeriv :=
    (gammaTwoMoebiusChart_hasStrictDerivAt γ z).hasDerivAt
  have hFderiv := hDeriv.complexToReal_fderiv.fderiv
""",
        "FunctionalAnalysis split the real derivative field chain",
    )
    fa = replace_exact(
        fa,
        """    simpa [G, g, inverseEtaPaperOrbitDenom, div_eq_mul_inv] using
      hComplex.complexToReal_fderiv
""",
        """    simpa [G, g, inverseEtaPaperOrbitDenom,
      inverseEtaPaperOrbit_det_eq_one, div_eq_mul_inv] using
      hComplex.complexToReal_fderiv
""",
        "FunctionalAnalysis normalize the Frechet derivative determinant",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
