from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """    exact (ae_restrict_iff' measurableSet_fundamentalRegion).1 <| by
      simpa only [fundamentalMeasure] using hfund
""",
        """    exact (ae_restrict_iff' measurableSet_fundamentalRegion).1 <| by
      simpa only [fundamentalMeasure, Filter.EventuallyEq] using hfund
""",
        "Mock2 Advanced unfold EventuallyEq on the restricted fundamental measure",
    )
    m2a = replace_exact(
        m2a,
        """  have hall :
      ∀ᵐ τ ∂hyperbolicMeasure, ∀ γ : Gamma2Element,
        gamma2Act γ τ ∈ fundamentalRegion → u τ = v τ := by
    rw [ae_all_iff]
    exact hmatrix
""",
        """  letI : Countable Gamma2Element :=
    (show Function.Injective (fun γ : Gamma2Element => γ.1.1) by
      intro γ δ h
      apply Subtype.ext
      apply Subtype.ext
      exact h).countable
  have hall :
      ∀ᵐ τ ∂hyperbolicMeasure, ∀ γ : Gamma2Element,
        gamma2Act γ τ ∈ fundamentalRegion → u τ = v τ := by
    rw [ae_all_iff]
    exact hmatrix
""",
        "Mock2 Advanced derive countability from the integer matrix embedding",
    )
    m2a = replace_exact(
        m2a,
        "MeasureTheory.Lp ℂ (2 : ℝ≥0∞) fundamentalMeasure",
        "MeasureTheory.Lp ℂ 2 fundamentalMeasure",
        "Mock2 Advanced infer the Lp exponent type from the carrier",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """  rw [positivePeterssonQuarter, Complex.norm_real,
    abs_of_nonneg (Real.sqrt_nonneg _)]
""",
        """  simp [positivePeterssonQuarter, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
""",
        "Mock2 Advanced normalize the nested real-square-root norm",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  intro y
  rw [Q.graphExtension_coe y]
  rfl
""",
        """  intro y
  rw [Q.graphExtension_coe y]
  exact UniformSpace.Completion.norm_coe y
""",
        "FunctionalAnalysis use the completion norm-coercion theorem explicitly",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
