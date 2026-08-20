from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twenty_sixth_pass_repairs as pass126
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """  advanced_readiness :
    AdvancedClaimsIIUnconditionalCertificationReadinessCertificate
  final_aggregation :
    AdvancedClaimsIIFinalTheoremAggregationCertificate
  rlf_enriched :
    AdvancedClaimsIIRlfEnrichedMathematicalContentCertificate
""",
            """  advanced_readiness :
    AdvancedClaimsIIUnconditionalCertificationReadinessCertificate
  final_aggregation :
    AdvancedClaimsIIFinalTheoremAggregationCertificate
      referenceAdvancedClaimsIICompletionCertificate
  rlf_enriched :
    AdvancedClaimsIIRlfEnrichedMathematicalContentCertificate
""",
            1,
            "Mock1Advanced supply the completion certificate in the abstract-concrete bridge",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """def toPresheafLike (F : LinearPresheaf X) : PresheafLike X where
""",
            """@[reducible] def toPresheafLike (F : LinearPresheaf X) : PresheafLike X where
""",
            1,
            "Mock2 make the forgetful presheaf carrier definitionally transparent",
        ),
        (
            """    change
      (inverseEvalLinear A q) (c • x.2.2) +
          (evalLinear A q) (c • x.2.1) =
        c • ((inverseEvalLinear A q) x.2.2 +
          (evalLinear A q) x.2.1)
    ring
""",
            """    change
      (inverseEvalLinear A q) (c • x.2.2) +
          (evalLinear A q) (c • x.2.1) =
        c • ((inverseEvalLinear A q) x.2.2 +
          (evalLinear A q) x.2.1)
    rw [map_smul, map_smul]
    ring
""",
            1,
            "Mock2 use the two linear-map scalar laws before distributivity",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  apply integrable_dirac
  positivity
""",
            """  apply integrable_dirac
  simp [kernel]
  exact pow_pos (by norm_num) i
""",
            1,
            "Mock2Advanced prove the positive geometric denominator left by simplification",
        ),
        (
            """  densityFloor : ℝ≥0
""",
            """  densityFloor : NNReal
""",
            1,
            "Mock2Advanced parse the stored spectral-density floor as a nonnegative real",
        ),
        (
            """    {densityFloor : ℝ≥0} (densityFloor_pos : 0 < densityFloor)
""",
            """    {densityFloor : NNReal} (densityFloor_pos : 0 < densityFloor)
""",
            4,
            "Mock2Advanced parse all spectral-density floor binders as nonnegative reals",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """theorem modular_normSq_denom_eq_lowerRowQuadratic
    (g : SL(2, ℤ)) (z : ℍ) :
    Complex.normSq (UpperHalfPlane.denom g z) =
      ((((g 1 0 : ℤ) : ℝ) * z.re + ((g 1 1 : ℤ) : ℝ)) ^ 2 +
        (((g 1 0 : ℤ) : ℝ) ^ 2 * z.im ^ 2)) := by
  rw [ModularGroup.denom_apply]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  ring
""",
            """theorem modular_normSq_denom_eq_lowerRowQuadratic
    (g : SL(2, ℤ)) (z : ℍ) :
    Complex.normSq (UpperHalfPlane.denom g z) =
      ((((g 1 0 : ℤ) : ℝ) * z.re + ((g 1 1 : ℤ) : ℝ)) ^ 2 +
        (((g 1 0 : ℤ) : ℝ) ^ 2 * z.im ^ 2)) := by
  rw [ModularGroup.denom_apply]
  norm_num [Complex.normSq_apply, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im] <;> ring
""",
            1,
            "FunctionalAnalysis normalize integer-to-complex lower-row casts before ring algebra",
        ),
    ])


def main() -> int:
    pass126.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
