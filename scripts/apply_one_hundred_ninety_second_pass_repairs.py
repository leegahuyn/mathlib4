from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """    · simp [closureDomainToGraphCompletion,
        graphCompletionToClosureDomain]
""",
        """    · simp [closureDomainToGraphCompletion,
        graphCompletionToClosureDomain, graphCoordinateEquiv]
""",
        "Mock2 Advanced expose the WithLp coordinate equivalence in left inverse",
    )
    m2a = replace_exact(
        m2a,
        """  simp [hz0, hsnd]
""",
        """  simp [graphCoordinateEquiv, hz0, hsnd]
""",
        "Mock2 Advanced expose the WithLp coordinate equivalence vertically",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem gammaTwoMoebiusChart_hasStrictDerivAt
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    HasStrictDerivAt (gammaTwoMoebiusChart γ)
      (1 / inverseEtaPaperOrbitDenom γ z ^ 2) (z : ℂ) := by
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, inverseEtaPaperOrbit_det_eq_one,
    Matrix.SpecialLinearGroup.det_coe, one_div] using
    (UpperHalfPlane.hasStrictDerivAt_smul
      (inverseEtaPaperOrbit_det_pos γ) z)
""",
        """theorem gammaTwoMoebiusChart_hasStrictDerivAt
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    HasStrictDerivAt (gammaTwoMoebiusChart γ)
      (1 / inverseEtaPaperOrbitDenom γ z ^ 2) (z : ℂ) := by
  let gℝ : SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
      (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)))
  have hdet : ((gℝ.val.det : ℝ) : ℂ) = 1 := by
    rw [gℝ.det_coe]
    norm_num
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, gℝ, hdet, one_div] using
    (UpperHalfPlane.hasStrictDerivAt_smul
      (inverseEtaPaperOrbit_det_pos γ) z)
""",
        "FunctionalAnalysis isolate the mapped special-linear determinant",
    )
    fa = replace_exact(
        fa,
        """    have hComplex :=
      (UpperHalfPlane.hasStrictDerivAt_smul
        (inverseEtaPaperOrbit_det_pos γ) z).hasDerivAt
    simpa [G, g, inverseEtaPaperOrbitDenom,
      inverseEtaPaperOrbit_det_eq_one,
      Matrix.SpecialLinearGroup.det_coe, div_eq_mul_inv] using
      hComplex.complexToReal_fderiv
""",
        """    have hComplex :=
      (gammaTwoMoebiusChart_hasStrictDerivAt γ z).hasDerivAt
    simpa [G, g, gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
      div_eq_mul_inv] using hComplex.complexToReal_fderiv
""",
        "FunctionalAnalysis reuse the normalized Möbius strict derivative",
    )
    fa = replace_exact(
        fa,
        """    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      (RealSmooth.contDiffAt_upperLift hf
        ((((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp))
""",
        """    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      (RealSmooth.contDiffAt_upperLift hf
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp)
""",
        "FunctionalAnalysis repair the outer differentiability field chain",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
