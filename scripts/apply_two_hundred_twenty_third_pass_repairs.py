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
        """noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G :=
  LieGroup.of_le le_top
""",
        """noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G :=
  LieGroup.of_le (I := I_G) (G := G)
    (n := minSmoothness ℂ 3) (m := ∞) le_top
""",
        "Mock2 pin the source and target smoothness orders in LieGroup.of_le",
    )
    m2 = replace_exact(
        m2,
        """/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G
""",
        """/- `TangentSpace` hides the model-space norm from typeclass inference.
Transport the fixed chart-model structures locally without changing the API. -/
noncomputable local instance gaugeLieAlgebraNormedAddCommGroup :
    NormedAddCommGroup (GaugeLieAlgebra I_G G) := by
  change NormedAddCommGroup E_G
  infer_instance

noncomputable local instance gaugeLieAlgebraNormedSpace :
    NormedSpace ℂ (GaugeLieAlgebra I_G G) := by
  change NormedSpace ℂ E_G
  infer_instance

/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G
""",
        "Mock2 transport the chart-model norm to the gauge Lie algebra",
    )
    m2 = replace_exact(
        m2,
        """theorem ext_pointwise {U : Opens} {A B : SmoothOneForm I_G G U}
    (h : ∀ τ : coverOpen U, A τ = B τ) : A = B :=
  ext (funext h)
""",
        """theorem ext_pointwise {U : Opens} {A B : SmoothOneForm I_G G U}
    (h : ∀ τ : coverOpen U, A τ = B τ) : A = B :=
  SmoothOneForm.ext (I_G := I_G) (G := G) (funext h)
""",
        "Mock2 disambiguate smooth one-form extensionality",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  simpa [modularCurve, Function.comp_def] using
    houter.comp_contDiffWithinAt t
      ((hcurve t ht.1).mono Set.inter_subset_left)
""",
        """  simpa [trimmedCurveDomain, modularCurve, Function.comp_def] using
    houter.comp_contDiffWithinAt t
      ((hcurve t ht.1).mono Set.inter_subset_left)
""",
        "Mock2 Advanced unfold the trimmed curve domain in smoothness",
    )
    m2a = replace_exact(
        m2a,
        """  simpa [modularCurve, modularCurveTangent, Function.comp_def] using
    houter.comp_hasDerivWithinAt
      (hderiv.mono Set.inter_subset_left)
""",
        """  simpa [trimmedCurveDomain, modularCurve, modularCurveTangent,
      Function.comp_def] using
    houter.comp_hasDerivWithinAt t
      (hderiv.mono Set.inter_subset_left)
""",
        "Mock2 Advanced supply the chain-rule basepoint and unfold the trim",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  exact (D.«section» a u).covariance γ z
""",
        """  exact WeightSection.covariance (D.«section» a u) γ z
""",
        "FunctionalAnalysis call WeightSection covariance by namespace",
    )
    fa = replace_exact(
        fa,
        """  halfCoreEquiv_apply : ∀ u z,
    (halfCoreEquiv u).toSection z = (u : ℍ → ℂ) z
""",
        """  halfCoreEquiv_apply : ∀ u z,
    SmoothCompactCore.toSection (halfCoreEquiv u) z =
      (u : ℍ → ℂ) z
""",
        "FunctionalAnalysis project the smooth compact core explicitly",
    )
    fa = replace_exact(
        fa,
        """def upperPlaneOpen : Opens ℂ :=
""",
        """def upperPlaneOpen : TopologicalSpace.Opens ℂ :=
""",
        "FunctionalAnalysis qualify the open-set type",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
