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


def replace_in_block(
    text: str,
    start_marker: str,
    end_marker: str,
    old: str,
    new: str,
    expected: int,
    label: str,
) -> str:
    start = text.index(start_marker)
    end = text.index(end_marker, start)
    block = text[start:end]
    count = block.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    block = block.replace(old, new)
    print(f"{label}: applied {count}")
    return text[:start] + block + text[end:]


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        "curvatureAlgebra.curvature A x =",
        "(curvatureAlgebra.curvature A) x =",
        "Mock2 apply the bundled curvature form at the point",
    )
    m2 = replace_exact(
        m2,
        """def at {U : TopologicalSpace.Opens Base} (g : FrameChange U) (x : U) :
""",
        """def «at» {U : TopologicalSpace.Opens Base} (g : FrameChange U) (x : U) :
""",
        "Mock2 escape the reserved frame-change evaluator name",
    )
    m2 = replace_exact(
        m2,
        "g.at x",
        "g.«at» x",
        "Mock2 use the escaped frame-change evaluator",
        expected=16,
    )
    m2 = replace_exact(
        m2,
        "FrameChange.at",
        "FrameChange.«at»",
        "Mock2 audit the escaped frame-change evaluator",
    )
    m2 = replace_in_block(
        m2,
        "noncomputable def restrict {U V : TopologicalSpace.Opens Base}",
        "/-- Pointwise matrix conjugation of a one-form. -/",
        "simpa [identityForm] using h",
        "simpa [restrictForm, wedge, identityForm] using h",
        2,
        "Mock2 unfold restricted wedge identities",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  · simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve,
      one_div, pow_two] <;> ring
""",
        """  · simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve,
      one_div, inv_neg, pow_two]
""",
        "Mock2 Advanced close the even reciprocal square under negation",
    )
    m2a = replace_in_block(
        m2a,
        "theorem firstBase_mul_secondBase",
        "theorem factor_sq",
        "  ring\n",
        "  ring_nf\n",
        1,
        "Mock2 Advanced normalize the first-base product",
    )
    m2a = replace_in_block(
        m2a,
        "theorem denom_zeroTranslation",
        "/-- The zero-cusp parabolic action",
        "  ring\n",
        "  ring_nf\n",
        1,
        "Mock2 Advanced normalize the zero-translation denominator",
    )
    m2a = replace_exact(
        m2a,
        """  have hSinv : ModularGroup.S⁻¹ • τ = ModularGroup.S • τ := by
    rw [ModularGroup.S_inv, ModularGroup.SL_neg_smul]
  rw [zeroCuspLift_matrix, zeroTranslation_act,
    ConcreteUnaryTheta.theta_S, hT, hSinv,
""",
        """  have hT' :
      ConcreteUnaryTheta.theta (transformedPoint τ) =
        ConcreteUnaryTheta.theta (ModularGroup.S⁻¹ • τ) := by
    simpa [transformedPoint] using hT
  have hSinv : ModularGroup.S⁻¹ • τ = ModularGroup.S • τ := by
    rw [ModularGroup.S_inv, ModularGroup.SL_neg_smul]
  rw [zeroCuspLift_matrix, zeroTranslation_act,
    ConcreteUnaryTheta.theta_S, hT', hSinv,
""",
        "Mock2 Advanced expose transformedPoint in theta covariance",
    )
    m2a = replace_exact(
        m2a,
        """  apply Subgroup.closure_le.2
""",
        """  rw [Subgroup.closure_le]
""",
        "Mock2 Advanced use the current closure inclusion theorem",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  rw [physicalExponent_eq_intCast_div_two]
  push_cast
  ring
""",
        """  rw [physicalExponent_eq_intCast_div_two]
  dsimp [p]
  push_cast
  ring_nf
""",
        "FunctionalAnalysis unfold the half exponent before cast normalization",
    )
    fa = replace_in_block(
        fa,
        "theorem heightSq_mul_fixedPhaseGreenFlux_divergence",
        "/-- The concrete divergence is integrable",
        "  field_simp [heightC_ne_zero z]\n  <;> ring\n",
        "  unfold fixedPhaseGreenScale\n  field_simp [heightC_ne_zero z]\n  <;> ring_nf\n",
        1,
        "FunctionalAnalysis expose the source fiber scale in Green divergence",
    )
    fa = replace_exact(
        fa,
        """  simp [fluxOneFormValue, fixedPhaseGreenFluxX, fixedPhaseGreenFluxY,
    Complex.mul_re, Complex.mul_im] <;> ring
""",
        """  unfold fluxOneFormValue fixedPhaseGreenFluxX fixedPhaseGreenFluxY
  rw [← Complex.re_add_im ξ]
  ring
""",
        "FunctionalAnalysis reconstruct the complex flux vector explicitly",
    )
    fa = replace_in_block(
        fa,
        "theorem fixedPhaseGreenScalarDensity_quotientCompact",
        "/-- Both concrete flux components are real smooth. -/",
        "HasQuotientCompactSupport",
        "SmoothCompactCoreGeometry.HasQuotientCompactSupport",
        4,
        "FunctionalAnalysis qualify quotient compact support",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
