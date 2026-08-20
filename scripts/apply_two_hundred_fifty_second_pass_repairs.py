from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        "abbrev GaugeModel : ModelWithCorners ℂ ModelSpace ModelSpace := 𝓘(ℂ)",
        "abbrev GaugeModel : ModelWithCorners ℂ ModelSpace ModelSpace := 𝓘(ℂ, ModelSpace)",
        "Mock2 use the self model on the zero-dimensional function space",
    )
    m2 = replace_exact(
        m2,
        """namespace Proposition17And18FinalSpecialization

noncomputable section

open PolynomialMatrixDifferentialForms
""",
        """namespace Proposition17And18FinalSpecialization

noncomputable section

open scoped Manifold ContDiff
open PolynomialMatrixDifferentialForms
""",
        "Mock2 reopen manifold notation in the final specialization namespace",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  convert (haff.inv hne).comp_ofReal using 1
  · funext y
    unfold cuspZeroAmbientCurve cuspHorizontalAmbientCurve
    congr 1
    ring
  · rw [show -((x : ℂ)) - (Y : ℂ) * Complex.I =
        -((x : ℂ) + (Y : ℂ) * Complex.I) by ring]
    simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve,
      one_div, pow_two]
""",
        """  convert (haff.inv hne).comp_ofReal using 1
  · funext y
    unfold cuspZeroAmbientCurve cuspHorizontalAmbientCurve
    congr 1
  · simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve,
      one_div, pow_two] <;> ring
""",
        "Mock2 Advanced remove closed-goal residue from the cusp derivative",
    )
    m2a = replace_exact(
        m2a,
        """theorem continuous_transformedPoint : Continuous transformedPoint := by
  exact (continuous_const_smul _).comp (continuous_const_smul _)
""",
        """theorem continuous_transformedPoint : Continuous transformedPoint := by
  change Continuous (fun τ : UpperHalfPlane =>
    (((ModularGroup.T ^ (2 : ℤ) : IntegralSpecialLinear) : GL (Fin 2) ℝ) •
      (((ModularGroup.S⁻¹ : IntegralSpecialLinear) : GL (Fin 2) ℝ) • τ)))
  exact (continuous_const_smul _).comp (continuous_const_smul _)
""",
        "Mock2 Advanced express transformed-point continuity through real GL actions",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  rw [physicalExponent_eq_intCast_div_two]
  norm_cast
  dsimp [p]
  field_simp [ne_of_gt z.im_pos]
  ring
""",
        """  rw [physicalExponent_eq_intCast_div_two]
  push_cast
  ring
""",
        "FunctionalAnalysis preserve real division while pushing complex casts",
    )
    fa = replace_exact(
        fa,
        "(fixedPhaseGreenScale_realSmooth n).mul (RealSmooth.conj hu)",
        "RealSmooth.mul (fixedPhaseGreenScale_realSmooth n) (RealSmooth.conj hu)",
        "FunctionalAnalysis select the bundled RealSmooth product theorem",
        expected=2,
    )
    fa = replace_exact(
        fa,
        "(hScale.mul (RealSmooth.conj hu)).mul hv",
        "RealSmooth.mul (RealSmooth.mul hScale (RealSmooth.conj hu)) hv",
        "FunctionalAnalysis build scalar-density smoothness with explicit products",
    )
    fa = replace_exact(
        fa,
        """  unfold fixedPhaseGreenScalarDensity fixedPhaseGreenScale
  simp only [smul_eq_mul]
  ring
""",
        """  unfold fixedPhaseGreenScalarDensity fixedPhaseGreenScale
  ring
""",
        "FunctionalAnalysis remove the no-progress scalar-multiplication simplifier",
    )
    fa = replace_exact(
        fa,
        """    InverseEtaFixedPhaseCore.lowerFromSucc_apply,
    paperOrbitExponent_add_one]
  rw [fixedPhaseGreenScale_succ]
""",
        """    InverseEtaFixedPhaseCore.lowerFromSucc_apply]
  rw [fixedPhaseGreenScale_succ, paperOrbitExponent_add_one]
""",
        "FunctionalAnalysis rewrite the successor scale before normalizing its exponent",
    )
    fa = replace_exact(
        fa,
        """  simpa only [heightSq_mul_fixedPhaseGreenFlux_divergence] using
    hRaise.add hLower
""",
        """  refine (hRaise.add hLower).congr ?_
  filter_upwards with z
  exact (heightSq_mul_fixedPhaseGreenFlux_divergence n u v z).symm
""",
        "FunctionalAnalysis transport integrability by pointwise divergence equality",
    )
    fa = replace_exact(
        fa,
        """  unfold fluxOneFormValue fixedPhaseGreenFluxX fixedPhaseGreenFluxY
  rw [← Complex.re_add_im ξ]
  ring
""",
        """  simp [fluxOneFormValue, fixedPhaseGreenFluxX, fixedPhaseGreenFluxY,
    Complex.mul_re, Complex.mul_im] <;> ring
""",
        "FunctionalAnalysis normalize the complex flux pairing by coordinates",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
