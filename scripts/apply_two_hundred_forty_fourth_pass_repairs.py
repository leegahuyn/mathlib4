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
        """theorem ext_pointwise {U : Opens} {g h : SmoothGaugeMap I_G G U}
    (hfun : ∀ τ, g τ = h τ) : g = h :=
  SmoothGaugeMap.ext (funext hfun)
""",
        """theorem ext_pointwise {U : Opens} {g h : SmoothGaugeMap I_G G U}
    (hfun : ∀ τ, g τ = h τ) : g = h :=
  SmoothGaugeMap.ext I_G G (funext hfun)
""",
        "Mock2 pass the model and group to smooth gauge extensionality",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """    HasDerivAt (cuspZeroAmbientCurve Y)
      (cuspFiniteAmbientTangent Y x) x := by
  have hneg :
""",
        """    HasDerivAt (cuspZeroAmbientCurve Y)
      (cuspFiniteAmbientTangent Y x) x := by
  letI : NormedField ℂ := Complex.instNormedField
  have hneg :
""",
        "Mock2 Advanced pin the canonical complex normed field locally",
    )
    m2a = replace_exact(
        m2a,
        """Matrix.mul_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]""",
        """pow_two, Matrix.mul_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]""",
        "Mock2 Advanced reduce squares in finite Gamma2 matrices",
        expected=8,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        "MeasureTheory.integral_complex_ofReal",
        "integral_complex_ofReal",
        "FunctionalAnalysis use the root complex-of-real integral theorem",
        expected=2,
    )
    fa = replace_exact(
        fa,
        "(mu := D.quotientMeasure)",
        "(μ := D.quotientMeasure)",
        "FunctionalAnalysis use the current integral measure argument",
        expected=4,
    )
    fa = replace_exact(
        fa,
        "MeasureTheory.integral_re",
        "integral_re",
        "FunctionalAnalysis use the root real-part integral theorem",
        expected=2,
    )
    fa = replace_exact(
        fa,
        "MeasureTheory.integral_conj",
        "integral_conj",
        "FunctionalAnalysis use the root conjugation integral theorem",
        expected=2,
    )
    fa = replace_exact(
        fa,
        """    Complex.conj
          (∫ q, quotientInnerDensity M v u q ∂D.quotientMeasure) =
""",
        """    star
          (∫ q, quotientInnerDensity M v u q ∂D.quotientMeasure) =
""",
        "FunctionalAnalysis state Petersson conjugation with star",
        expected=1,
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
