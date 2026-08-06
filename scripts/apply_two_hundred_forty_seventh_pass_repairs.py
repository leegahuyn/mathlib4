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
        """abbrev OneFormValue
    (_I_G : ModelWithCorners ℂ E_G H_G) (_G : Type uGG) :=
  ℂ →L[ℂ] E_G
""",
        """abbrev OneFormValue
    (I_G : ModelWithCorners ℂ E_G H_G) (G : Type uGG) :=
  ℂ →L[ℂ] GaugeLieAlgebra I_G G
""",
        "Mock2 expose one-form values in the actual gauge Lie algebra",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        """  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  letI : NontriviallyNormedField ℂ :=
    Complex.instNormedField.toNontriviallyNormedField
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        "Mock2 Advanced pin the canonical nontrivially normed complex field",
    )
    m2a = replace_exact(
        m2a,
        """  | hS g ih =>
      obtain ⟨r, h, hh, hg⟩ := ih
""",
        """  | hS g ih =>
      change G at g ih
      obtain ⟨r, h, hh, hg⟩ := ih
""",
        "Mock2 Advanced identify the S-branch fixed determinant matrix with SL2",
    )
    m2a = replace_exact(
        m2a,
        """  | hT g ih =>
      obtain ⟨r, h, hh, hg⟩ := ih
""",
        """  | hT g ih =>
      change G at g ih
      obtain ⟨r, h, hh, hg⟩ := ih
""",
        "Mock2 Advanced identify the T-branch fixed determinant matrix with SL2",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hScaleC := congrArg (fun r : ℝ => (r : ℂ)) hScaleNormSq
  simpa [M, F, Complex.ofReal_mul, starRingEnd_apply,
    Complex.normSq_eq_conj_mul_self] using hScaleC
""",
        """  have hScaleC := congrArg (fun r : ℝ => (r : ℂ)) hScaleNormSq
  change
    ((weightFiberScale (-paperOrbitExponent n)
        (((γ : GammaTwo) : SL(2, ℤ)) • z) : ℝ) : ℂ) *
        (star F * F) =
      ((weightFiberScale (-paperOrbitExponent n) z : ℝ) : ℂ)
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self] at hScaleC
  simpa only [starRingEnd_apply] using hScaleC
""",
        "FunctionalAnalysis avoid unfolding the full source multiplier during cancellation",
    )
    fa = replace_exact(
        fa,
        """  have hu := u.2 FixedPhaseDifferentialWord.nil γ z
  have hv := v.2 FixedPhaseDifferentialWord.nil γ z
  have hu' :
      ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        F * (u : SmoothQuotientCompactFunction) z := by
    simpa [F, M, OrbitMultiplier] using hu
  have hv' :
      ((v : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (F * j ^ 2) * (v : SmoothQuotientCompactFunction) z := by
    have hFactor := inverseEtaPaperOrbitMultiplier_factor_add_one
      GammaTwo n γ z
    simpa [F, M, j, OrbitMultiplier] using hv.trans (by
      rw [hFactor]
      ring)
""",
        """  have hu := u.2 FixedPhaseDifferentialWord.nil γ z
  have hv := v.2 FixedPhaseDifferentialWord.nil γ z
  simp only [FixedPhaseDifferentialWord.targetIndex_nil,
    FixedPhaseDifferentialWord.eval_nil_apply] at hu hv
  have hu' :
      ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        F * (u : SmoothQuotientCompactFunction) z := by
    simpa [F, M, OrbitMultiplier,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using hu
  have hv' :
      ((v : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (F * j ^ 2) * (v : SmoothQuotientCompactFunction) z := by
    have hFactor := inverseEtaPaperOrbitMultiplier_factor_add_one
      GammaTwo n γ z
    rw [hFactor] at hv
    simpa [F, M, j, OrbitMultiplier, mul_assoc,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using hv
""",
        "FunctionalAnalysis normalize nil differential words before covariance rewrites",
    )
    fa = replace_exact(
        fa,
        """  rw [fixedPhaseGreenScalarDensity, hu', hv', star_mul]
  change
    ((weightFiberScale (-paperOrbitExponent n)
        (((γ : GammaTwo) : SL(2, ℤ)) • z) : ℝ) : ℂ) *
          (star F *
            star ((u : SmoothQuotientCompactFunction) z)) *
          ((F * j ^ 2) *
            (v : SmoothQuotientCompactFunction) z)) =
      j ^ 2 *
        (((weightFiberScale (-paperOrbitExponent n) z : ℝ) : ℂ) *
          star ((u : SmoothQuotientCompactFunction) z) *
          (v : SmoothQuotientCompactFunction) z)
  calc
    ((weightFiberScale (-paperOrbitExponent n)
        (((γ : GammaTwo) : SL(2, ℤ)) • z) : ℝ) : ℂ) *
          (star F *
            star ((u : SmoothQuotientCompactFunction) z)) *
          ((F * j ^ 2) *
            (v : SmoothQuotientCompactFunction) z)) =
        (((weightFiberScale (-paperOrbitExponent n)
            (((γ : GammaTwo) : SL(2, ℤ)) • z) : ℝ) : ℂ) *
            (star F * F)) * j ^ 2 *
          star ((u : SmoothQuotientCompactFunction) z) *
          (v : SmoothQuotientCompactFunction) z) := by ring
""",
        """  rw [fixedPhaseGreenScalarDensity, hu', hv', star_mul]
  change
    ((weightFiberScale (-paperOrbitExponent n)
        (((γ : GammaTwo) : SL(2, ℤ)) • z) : ℝ) : ℂ) *
          (star ((u : SmoothQuotientCompactFunction) z) * star F) *
          ((F * j ^ 2) *
            (v : SmoothQuotientCompactFunction) z) =
      j ^ 2 *
        (((weightFiberScale (-paperOrbitExponent n) z : ℝ) : ℂ) *
          star ((u : SmoothQuotientCompactFunction) z) *
          (v : SmoothQuotientCompactFunction) z)
  calc
    ((weightFiberScale (-paperOrbitExponent n)
        (((γ : GammaTwo) : SL(2, ℤ)) • z) : ℝ) : ℂ) *
          (star ((u : SmoothQuotientCompactFunction) z) * star F) *
          ((F * j ^ 2) *
            (v : SmoothQuotientCompactFunction) z) =
        (((weightFiberScale (-paperOrbitExponent n)
            (((γ : GammaTwo) : SL(2, ℤ)) • z) : ℝ) : ℂ) *
            (star F * F)) * j ^ 2 *
          star ((u : SmoothQuotientCompactFunction) z) *
          (v : SmoothQuotientCompactFunction) z := by ring
""",
        "FunctionalAnalysis match the actual star multiplication order",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
