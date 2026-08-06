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
        """  unfold gaugeAdjointValue
  rw [mfderiv_congr hconj, mfderiv_id]
""",
        """  unfold gaugeAdjointValue
  change
    mfderiv I_G I_G (fun x : G => a⁻¹ * x * a) 1 =
      ContinuousLinearMap.id ℂ (GaugeLieAlgebra I_G G)
  rw [mfderiv_congr hconj, mfderiv_id]
""",
        "Mock2 compare the central adjoint identity in the tangent model",
    )
    m2 = replace_exact(
        m2,
        """  change A τ + D.maurerCartan U g τ = _
  rw [show A τ = (gaugeAdjointValue I_G G (g τ)).comp (A τ) by
      exact centralConjugate_pointwise_paper_formula I_G G U g A hg.1 τ,
    D.maurerCartan_formula U g τ]
""",
        """  change A τ + D.maurerCartan U g τ = _
  rw [D.maurerCartan_formula U g τ]
  congr 1
  simpa using
    centralConjugate_pointwise_paper_formula I_G G U g A hg.1 τ
""",
        "Mock2 avoid rewriting the adjoint term twice",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  have haff :
      HasDerivAt
        (fun z : ℂ => -(z + (Y : ℂ) * Complex.I))
        (-1) (x : ℂ) := by
    simpa using
      (((hasDerivAt_id (x : ℂ)).add_const
        ((Y : ℂ) * Complex.I)).neg)
  have hne : -((x : ℂ) + (Y : ℂ) * Complex.I) ≠ 0 := by
    exact neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    cuspHorizontalAmbientCurve, one_div] using
      (haff.inv hne).comp_ofReal
""",
        """  have haff :
      HasDerivAt
        (fun z : ℂ => -(z + (Y : ℂ) * Complex.I))
        (-1) (x : ℂ) :=
    (((hasDerivAt_id (x : ℂ)).add_const
      ((Y : ℂ) * Complex.I)).neg)
  have hne : -((x : ℂ) + (Y : ℂ) * Complex.I) ≠ 0 := by
    exact neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  convert (haff.inv hne).comp_ofReal using 1 <;>
    simp [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
      cuspHorizontalAmbientCurve, one_div, pow_two] <;> ring
""",
        "Mock2 Advanced normalize the complex reciprocal before real restriction",
    )
    m2a = replace_exact(
        m2a,
        "change G at g ih",
        "change G at g",
        "Mock2 Advanced retype only the fixed-determinant branch matrix",
        expected=2,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  rw [physicalExponent_eq_intCast_div_two]
  rw [Complex.ofReal_mul, Complex.ofReal_div]
  ring
""",
        """  rw [physicalExponent_eq_intCast_div_two]
  rw [Complex.ofReal_mul, Complex.ofReal_div]
  ring_nf
""",
        "FunctionalAnalysis normalize the fixed-phase scale derivative",
    )
    fa = replace_in_block(
        fa,
        "theorem dx_fixedPhaseGreenScalarDensity",
        "/-- `x`-component of the divergence field",
        "hu.conj",
        "(SmoothCompactCoreGeometry.RealSmooth.conj hu)",
        5,
        "FunctionalAnalysis qualify fixed-phase conjugation smoothness",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
