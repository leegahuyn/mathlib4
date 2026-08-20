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
        """section GaugeForms

variable {E_G H_G : Type*}
variable [NormedAddCommGroup E_G] [NormedSpace ℂ E_G] [CompleteSpace E_G]
variable [TopologicalSpace H_G]
variable (I_G : ModelWithCorners ℂ E_G H_G)
variable (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H_G G]
""",
        """section GaugeForms

universe uEG uHG uGG

variable {E_G : Type uEG} {H_G : Type uHG}
variable [NormedAddCommGroup E_G] [NormedSpace ℂ E_G] [CompleteSpace E_G]
variable [TopologicalSpace H_G]
variable (I_G : ModelWithCorners ℂ E_G H_G)
variable (G : Type uGG) [Group G] [TopologicalSpace G] [ChartedSpace H_G G]
""",
        "Mock2 expose the gauge model universes explicitly",
    )
    m2 = replace_exact(
        m2,
        """    TopCat.LocalPredicate.{0, 0}
      (fun _ : TopCat.of H => OneFormValue I_G G) :=
""",
        """    TopCat.LocalPredicate.{uEG, 0}
      (fun _ : TopCat.of H => OneFormValue I_G G) :=
""",
        "Mock2 align the local-predicate value universe with the gauge model",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
""",
        """  have hreal : HasDerivAt (⇑Complex.ofRealCLM) 1 x :=
    (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
  have hfun : (⇑Complex.ofRealCLM : ℝ → ℂ) =
      (fun t : ℝ => (t : ℂ)) := by
    funext t
    rfl
  rw [hfun] at hreal
""",
        "Mock2 Advanced transport the real embedding derivative extensionally",
    )
    m2a = replace_exact(
        m2a,
        """  change HasDerivAt
    (fun t : ℝ => (-cuspHorizontalAmbientCurve Y t)⁻¹)
      (1 / cuspHorizontalAmbientCurve Y x ^ 2) x
  convert hneg.inv hne using 1
""",
        """  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        "Mock2 Advanced use the reciprocal derivative theorem directly",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    rw [raise_apply,
      dx_weightedConjugate_apply_of_im_pos a u hw,
      dy_weightedConjugate_apply_of_im_pos a u hw]
    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        """    rw [raise_apply,
      dx_weightedConjugate_apply_of_im_pos a u hw,
      dy_weightedConjugate_apply_of_im_pos a u hw]
    simp only [map_add, map_mul, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        "FunctionalAnalysis expand conjugation before the raising flux algebra",
    )
    fa = replace_exact(
        fa,
        """  rw [weightedConjugate_raise_eq_flux,
    compactPair_add_left, compactPair_smul_left,
    compactPair_directionalDerivative_left,
""",
        """  rw [weightedConjugate_raise_eq_flux, dx, dy,
    compactPair_add_left, compactPair_smul_left,
    compactPair_directionalDerivative_left,
""",
        "FunctionalAnalysis expose coordinate derivatives in the raising Green identity",
    )
    fa = replace_exact(
        fa,
        """    rw [normalizedLower_apply,
      dx_weightedConjugate_apply_of_im_pos a u hw,
      dy_weightedConjugate_apply_of_im_pos a u hw,
      weightedConjugate_apply]
    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        """    rw [normalizedLower_apply,
      dx_weightedConjugate_apply_of_im_pos a u hw,
      dy_weightedConjugate_apply_of_im_pos a u hw,
      weightedConjugate_apply]
    simp only [map_add, map_mul, map_neg, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
    have hcoeff := weighted_inverse_height_coefficient a hw
""",
        "FunctionalAnalysis expand conjugation before the lowering flux algebra",
    )
    fa = replace_exact(
        fa,
        """  rw [weightedConjugate_normalizedLower_eq_flux,
    compactPair_add_left, compactPair_add_left,
""",
        """  rw [weightedConjugate_normalizedLower_eq_flux, dx, dy,
    compactPair_add_left, compactPair_add_left,
""",
        "FunctionalAnalysis expose coordinate derivatives in the lowering Green identity",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
