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
        """noncomputable local instance oneFormValueNormedAddCommGroup :
    NormedAddCommGroup (OneFormValue I_G G) := by
  change NormedAddCommGroup (ℂ →L[ℂ] E_G)
  infer_instance

noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

noncomputable local instance oneFormValueChartedSpace :
    ChartedSpace (OneFormValue I_G G) (OneFormValue I_G G) :=
  chartedSpaceSelf (OneFormValue I_G G)

""",
        """""",
        "Mock2 use canonical continuous-linear-map norm and chart structures",
    )
    m2 = replace_exact(
        m2,
        """  res {U V} i f hf := by
    intro x
    exact (hf (i x)).comp x ((contMDiff_inclusion i.le) x)
""",
        """  res {U V} i f hf :=
    hf.comp (contMDDiff_inclusion i.le)
""".replace("contMDDiff", "contMDiff"),
        "Mock2 compose global smoothness with open inclusion",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        """attribute [-instance] NormedSpace.complexToReal

/-! ##### Regular smooth parametrizations of all cusp-height levels -/
""",
        "Mock2 Advanced use the normed-algebra real structure on the cusp block",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_cuspHorizontalAmbientCurve (Y x : ℝ) :
    HasDerivAt (cuspHorizontalAmbientCurve Y) 1 x := by
  have hreal : HasDerivAt (⇑Complex.ofRealCLM) 1 x :=
    (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
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
  simpa [cuspHorizontalAmbientCurve] using
    (((hasDerivAt_id (x : ℂ)).comp_ofReal).add_const
      ((Y : ℂ) * Complex.I))
""",
        "Mock2 Advanced differentiate the horizontal cusp curve in the active real structure",
    )
    m2a = replace_exact(
        m2a,
        """theorem contDiff_cuspHorizontalAmbientCurve (Y : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cuspHorizontalAmbientCurve Y) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun x : ℝ => (x : ℂ) + (Y : ℂ) * Complex.I)
  simpa [Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.add contDiff_const
""",
        """theorem contDiff_cuspHorizontalAmbientCurve (Y : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cuspHorizontalAmbientCurve Y) := by
  unfold cuspHorizontalAmbientCurve
  fun_prop
""",
        "Mock2 Advanced prove horizontal cusp smoothness in the active real structure",
    )
    m2a = replace_exact(
        m2a,
        """  have hspace :
      (NormedAlgebra.toNormedSpace ℂ : NormedSpace ℝ ℂ) =
        NormedSpace.complexToReal := Subsingleton.elim _ _
  cases hspace
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        """  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        "Mock2 Advanced apply reciprocal differentiation under one normed-space instance",
    )
    m2a = replace_exact(
        m2a,
        """  have hspace :
      (NormedAlgebra.toNormedSpace ℂ : NormedSpace ℝ ℂ) =
        NormedSpace.complexToReal := Subsingleton.elim _ _
  cases hspace
  exact hneg.inv (fun x => neg_ne_zero.mpr
    (cuspHorizontalAmbientCurve_ne_zero hY x))
""",
        """  exact hneg.inv (fun x => neg_ne_zero.mpr
    (cuspHorizontalAmbientCurve_ne_zero hY x))
""",
        "Mock2 Advanced apply reciprocal smoothness under one normed-space instance",
    )
    m2a = replace_exact(
        m2a,
        """/-! ##### Finite assembly of the complete truncated boundary -/
""",
        """attribute [instance 2000] NormedSpace.complexToReal

/-! ##### Finite assembly of the complete truncated boundary -/
""",
        "Mock2 Advanced restore the standard complex-real instance after cusp calculus",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    have hcoeff := weighted_inverse_height_coefficient a hw
    linear_combination (star (u w)) * hcoeff
""",
        """    have hI : star Complex.I = -Complex.I := by
      exact Complex.conj_I
    rw [hI]
    have hcoeff := weighted_inverse_height_coefficient a hw
    linear_combination (star (u w)) * hcoeff
""",
        "FunctionalAnalysis normalize the conjugate of I in the raising flux",
    )
    fa = replace_exact(
        fa,
        """  ring

/-- The same theorem written as an exact zero-boundary Green sum. -/
""",
        """  simp only [dx, dy] <;> ring

/-- The same theorem written as an exact zero-boundary Green sum. -/
""",
        "FunctionalAnalysis identify directional derivatives in the raising Green identity",
    )
    fa = replace_exact(
        fa,
        """    have hcoeff := weighted_inverse_height_coefficient a hw
    linear_combination -(star (u w)) * hcoeff
""",
        """    have hI : star Complex.I = -Complex.I := by
      exact Complex.conj_I
    rw [hI]
    have hcoeff := weighted_inverse_height_coefficient a hw
    linear_combination -(star (u w)) * hcoeff
""",
        "FunctionalAnalysis normalize the conjugate of I in the lowering flux",
    )
    fa = replace_exact(
        fa,
        """  ring

/-- Zero-sum form of the lowering identity. -/
""",
        """  simp only [dx, dy] <;> ring

/-- Zero-sum form of the lowering identity. -/
""",
        "FunctionalAnalysis identify directional derivatives in the lowering Green identity",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
