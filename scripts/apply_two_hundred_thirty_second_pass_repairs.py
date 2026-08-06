from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """def strictSmoothOneFormLocalPredicate :
    TopCat.LocalPredicate
      (fun _ : TopCat.of H => OneFormValue I_G G) :=
""",
        """def strictSmoothOneFormLocalPredicate :
    TopCat.LocalPredicate.{0, 0}
      (fun _ : TopCat.of H => OneFormValue I_G G) :=
""",
        "Mock2 pin the strict local-predicate universes to the concrete upper half-plane",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  have hreal := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hfun : (⇑Complex.ofRealCLM : ℝ → ℂ) =
      (fun t : ℝ => (t : ℂ)) := by
    funext t
    rfl
  rw [hfun] at hreal
  change HasDerivAt
    (fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I) 1 x
  exact hreal.add_const ((Y : ℂ) * Complex.I)
""",
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
  change HasDerivAt
    (fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I) 1 x
  exact hreal.add_const ((Y : ℂ) * Complex.I)
""",
        "Mock2 Advanced pin the basepoint of the real embedding derivative",
    )
    m2a = replace_exact(
        m2a,
        """  convert hneg.inv hne using 1
  ring
""",
        """  convert hneg.inv hne using 1
""",
        "Mock2 Advanced remove the redundant reciprocal coefficient normalization",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    simp only [rpowMul_apply, rpowScale, Real.rpow_one, one_mul,
      sub_self, Real.rpow_zero, Complex.ofReal_one]
    ring
""",
        """    simp only [rpowMul_apply, rpowScale, Real.rpow_one, one_mul,
      sub_self, Real.rpow_zero, Complex.ofReal_one]
""",
        "FunctionalAnalysis remove the closed-goal ring after height-one simplification",
    )
    fa = replace_exact(
        fa,
        """    rw [← Real.rpow_add hw]
    congr 1
    ring
""",
        """    rw [← Real.rpow_add hw]
    congr 1
""",
        "FunctionalAnalysis remove the closed-goal ring in the inverse-height exponent",
    )
    fa = replace_exact(
        fa,
        """    simp only [map_add, map_mul, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        """    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        "FunctionalAnalysis remove the no-progress conjugation simp before linear combination",
    )
    fa = replace_exact(
        fa,
        """    simp only [map_add, map_mul, map_neg, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        """    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        "FunctionalAnalysis remove the no-progress lowering conjugation simp",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
