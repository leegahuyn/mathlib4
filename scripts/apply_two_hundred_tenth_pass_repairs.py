from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
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
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  exact (raise n u).2 FixedPhaseDifferentialWord.nil γ z
""",
        """  simpa only [FixedPhaseDifferentialWord.eval_nil_apply,
    FixedPhaseDifferentialWord.targetIndex_nil] using
      ((raise n u).2 FixedPhaseDifferentialWord.nil γ z)
""",
        "FunctionalAnalysis reduce the zeroth word in raising covariance",
    )
    fa = replace_exact(
        fa,
        """  exact (lower n u).2 FixedPhaseDifferentialWord.nil γ z
""",
        """  simpa only [FixedPhaseDifferentialWord.eval_nil_apply,
    FixedPhaseDifferentialWord.targetIndex_nil] using
      ((lower n u).2 FixedPhaseDifferentialWord.nil γ z)
""",
        "FunctionalAnalysis reduce the zeroth word in lowering covariance",
    )
    fa = replace_exact(
        fa,
        """  simpa using
    (HalfWeightDifferentialOperators.lower_raise_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        """  simpa only [lowerFromSucc_apply, raise_apply] using
    (HalfWeightDifferentialOperators.lower_raise_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        "FunctionalAnalysis expose the bundled lower-after-raise applications",
    )
    fa = replace_exact(
        fa,
        """  simpa using
    (HalfWeightDifferentialOperators.raise_lower_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        """  simpa only [raiseFromPred_apply, lower_apply] using
    (HalfWeightDifferentialOperators.raise_lower_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        "FunctionalAnalysis expose the bundled raise-after-lower applications",
    )
    fa = replace_exact(
        fa,
        """  simpa using
    (HalfWeightDifferentialOperators.averaged_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        """  simpa only [lowerFromSucc_apply, raise_apply,
    raiseFromPred_apply, lower_apply] using
    (HalfWeightDifferentialOperators.averaged_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        "FunctionalAnalysis expose both bundled averaged applications",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
