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
        """theorem raise_covariance (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    ((raise n u : InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) ((γ : SL(2, ℤ)) • z) =
      (inverseEtaPaperOrbitMultiplier
          GammaTwoQuotientGeometry.GammaTwo (n + 1)).factor γ z *
        ((raise n u : InverseEtaFixedPhaseCore (n + 1)) :
          SmoothQuotientCompactFunction) z := by
  simpa only [FixedPhaseDifferentialWord.eval_nil_apply,
    FixedPhaseDifferentialWord.targetIndex_nil] using
      ((raise n u).2 FixedPhaseDifferentialWord.nil γ z)
""",
        """theorem raise_covariance (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    ((raise n u : InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) ((γ : SL(2, ℤ)) • z) =
      (inverseEtaPaperOrbitMultiplier
          GammaTwoQuotientGeometry.GammaTwo (n + 1)).factor γ z *
        ((raise n u : InverseEtaFixedPhaseCore (n + 1)) :
          SmoothQuotientCompactFunction) z := by
  have hcov :=
    (mem_inverseEtaFixedPhaseStableCoreSubmodule_iff (n + 1)
      (toSmoothQuotientCompactFunction (raise n u))).1 (raise n u).2
  simpa [toSmoothQuotientCompactFunction] using hcov γ z
""",
        "FunctionalAnalysis extract raising covariance from stable-core membership",
    )
    fa = replace_exact(
        fa,
        """theorem lower_covariance (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    ((lower n u : InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) ((γ : SL(2, ℤ)) • z) =
      (inverseEtaPaperOrbitMultiplier
          GammaTwoQuotientGeometry.GammaTwo (n - 1)).factor γ z *
        ((lower n u : InverseEtaFixedPhaseCore (n - 1)) :
          SmoothQuotientCompactFunction) z := by
  simpa only [FixedPhaseDifferentialWord.eval_nil_apply,
    FixedPhaseDifferentialWord.targetIndex_nil] using
      ((lower n u).2 FixedPhaseDifferentialWord.nil γ z)
""",
        """theorem lower_covariance (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    ((lower n u : InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) ((γ : SL(2, ℤ)) • z) =
      (inverseEtaPaperOrbitMultiplier
          GammaTwoQuotientGeometry.GammaTwo (n - 1)).factor γ z *
        ((lower n u : InverseEtaFixedPhaseCore (n - 1)) :
          SmoothQuotientCompactFunction) z := by
  have hcov :=
    (mem_inverseEtaFixedPhaseStableCoreSubmodule_iff (n - 1)
      (toSmoothQuotientCompactFunction (lower n u))).1 (lower n u).2
  simpa [toSmoothQuotientCompactFunction] using hcov γ z
""",
        "FunctionalAnalysis extract lowering covariance from stable-core membership",
    )
    fa = replace_exact(
        fa,
        """theorem lower_raise_factorization (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    -laplaceRaw (paperOrbitExponent n)
        (u : SmoothQuotientCompactFunction) z =
      (((lowerFromSucc n (raise n u) :
          InverseEtaFixedPhaseCore n) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) z +
        physicalExponent (paperOrbitExponent n) *
          (u : SmoothQuotientCompactFunction) z := by
  simpa only [lowerFromSucc_apply, raise_apply] using
    (HalfWeightDifferentialOperators.lower_raise_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        """theorem lower_raise_factorization (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    -laplaceRaw (paperOrbitExponent n)
        (u : SmoothQuotientCompactFunction) z =
      (((lowerFromSucc n (raise n u) :
          InverseEtaFixedPhaseCore n) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) z +
        physicalExponent (paperOrbitExponent n) *
          (u : SmoothQuotientCompactFunction) z := by
  have hraise :
      (((raise n u : InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) =
      raiseRaw (paperOrbitExponent n)
        ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) := by
    funext w
    exact raise_apply n u w
  rw [lowerFromSucc_apply, paperOrbitExponent_add_one, hraise]
  exact HalfWeightDifferentialOperators.lower_raise_factorization
    (a := paperOrbitExponent n)
    (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
    (u : SmoothQuotientCompactFunction).1.2 z
""",
        "FunctionalAnalysis transport lower-after-raise to raw operators",
    )
    fa = replace_exact(
        fa,
        """theorem raise_lower_factorization (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    -laplaceRaw (paperOrbitExponent n)
        (u : SmoothQuotientCompactFunction) z =
      (((raiseFromPred n (lower n u) :
          InverseEtaFixedPhaseCore n) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) z := by
  simpa only [raiseFromPred_apply, lower_apply] using
    (HalfWeightDifferentialOperators.raise_lower_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        """theorem raise_lower_factorization (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    -laplaceRaw (paperOrbitExponent n)
        (u : SmoothQuotientCompactFunction) z =
      (((raiseFromPred n (lower n u) :
          InverseEtaFixedPhaseCore n) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) z := by
  have hlower :
      (((lower n u : InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) =
      lowerRaw (paperOrbitExponent n)
        ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) := by
    funext w
    exact lower_apply n u w
  rw [raiseFromPred_apply, paperOrbitExponent_sub_one, hlower]
  exact HalfWeightDifferentialOperators.raise_lower_factorization
    (a := paperOrbitExponent n)
    (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
    (u : SmoothQuotientCompactFunction).1.2 z
""",
        "FunctionalAnalysis transport raise-after-lower to raw operators",
    )
    fa = replace_exact(
        fa,
        """theorem averaged_factorization (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    -laplaceRaw (paperOrbitExponent n)
        (u : SmoothQuotientCompactFunction) z =
      (1 / 2 : ℂ) *
        ((((lowerFromSucc n (raise n u) :
            InverseEtaFixedPhaseCore n) :
          SmoothQuotientCompactFunction) : ℍ → ℂ) z +
          (((raiseFromPred n (lower n u) :
              InverseEtaFixedPhaseCore n) :
            SmoothQuotientCompactFunction) : ℍ → ℂ) z) +
        (physicalExponent (paperOrbitExponent n) / 2) *
          (u : SmoothQuotientCompactFunction) z := by
  simpa only [lowerFromSucc_apply, raise_apply,
    raiseFromPred_apply, lower_apply] using
    (HalfWeightDifferentialOperators.averaged_factorization
      (a := paperOrbitExponent n)
      (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (u : SmoothQuotientCompactFunction).1.2 z)
""",
        """theorem averaged_factorization (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    -laplaceRaw (paperOrbitExponent n)
        (u : SmoothQuotientCompactFunction) z =
      (1 / 2 : ℂ) *
        ((((lowerFromSucc n (raise n u) :
            InverseEtaFixedPhaseCore n) :
          SmoothQuotientCompactFunction) : ℍ → ℂ) z +
          (((raiseFromPred n (lower n u) :
              InverseEtaFixedPhaseCore n) :
            SmoothQuotientCompactFunction) : ℍ → ℂ) z) +
        (physicalExponent (paperOrbitExponent n) / 2) *
          (u : SmoothQuotientCompactFunction) z := by
  have hraise :
      (((raise n u : InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) =
      raiseRaw (paperOrbitExponent n)
        ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) := by
    funext w
    exact raise_apply n u w
  have hlower :
      (((lower n u : InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) : ℍ → ℂ) =
      lowerRaw (paperOrbitExponent n)
        ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) := by
    funext w
    exact lower_apply n u w
  rw [lowerFromSucc_apply, raiseFromPred_apply,
    paperOrbitExponent_add_one, paperOrbitExponent_sub_one,
    hraise, hlower]
  exact HalfWeightDifferentialOperators.averaged_factorization
    (a := paperOrbitExponent n)
    (f := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
    (u : SmoothQuotientCompactFunction).1.2 z
""",
        "FunctionalAnalysis transport the averaged factorization to raw operators",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
