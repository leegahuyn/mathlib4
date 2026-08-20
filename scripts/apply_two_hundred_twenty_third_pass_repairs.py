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
    (m := minSmoothness ℂ 3) (n := ∞) le_top
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
    m2a = replace_exact(
        m2a,
        """  have hbase : g • τ ∈ frontier s := by
    have hpre :
        τ ∈ (fun w : UpperHalfPlane => g • w) ⁻¹' frontier s := by
      rw [(Homeomorph.smul g).preimage_frontier s]
      exact hτfrontier
    exact hpre
""",
        """  have hbase : g • τ ∈ frontier s := by
    let gR : GL (Fin 2) ℝ := realGL g
    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹' frontier s := by
      rw [(Homeomorph.smul gR).preimage_frontier s]
      simpa [gR, realGL_smul] using hτfrontier
    simpa [gR, realGL_smul] using hpre
""",
        "Mock2 Advanced use the real GL homeomorphism for frontier transport",
    )
    m2a = replace_exact(
        m2a,
        """  have hbase : repMatrix r • τ ∈ frontier ModularGroup.fd := by
    have hpre :
        τ ∈ (fun w : UpperHalfPlane => repMatrix r • w) ⁻¹'
          frontier ModularGroup.fd := by
      rw [(Homeomorph.smul (repMatrix r)).preimage_frontier ModularGroup.fd]
      exact hτfrontier
    exact hpre
""",
        """  have hbase : repMatrix r • τ ∈ frontier ModularGroup.fd := by
    let gR : GL (Fin 2) ℝ := realGL (repMatrix r)
    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹'
          frontier ModularGroup.fd := by
      rw [(Homeomorph.smul gR).preimage_frontier ModularGroup.fd]
      simpa [gR, realGL_smul] using hτfrontier
    simpa [gR, realGL_smul] using hpre
""",
        "Mock2 Advanced use the real GL homeomorphism for closed-cell frontier transport",
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
    fa = replace_exact(
        fa,
        """  simpa [rpowScale, Function.comp_def] using
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hp
""",
        """  change ContDiffAt ℝ ∞
    (fun z : ℂ => ((z.im ^ p : ℝ) : ℂ)) w
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp w hp
""",
        "FunctionalAnalysis expose the real height power before smoothness composition",
    )
    fa = replace_exact(
        fa,
        """  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L ξ) hc.fderiv
  simpa [rpowScale, Function.comp_def,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.imCLM_apply, smul_eq_mul, mul_assoc] using h
""",
        """  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L ξ) hc.fderiv
  change fderiv ℝ (fun z : ℂ => ((z.im ^ p : ℝ) : ℂ)) w ξ = _
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Complex.imCLM_apply, smul_eq_mul,
    mul_assoc] using h
""",
        "FunctionalAnalysis expose the real height power in its derivative formula",
    )
    fa = replace_exact(
        fa,
        """  rw [fderiv_mul
    (rpowScale_contDiffAt_of_im_pos p hw).differentiableAt (by simp)
    ((u.contDiff.differentiable (by simp)) w)]
""",
        """  rw [fderiv_mul
    ((rpowScale_contDiffAt_of_im_pos p hw).differentiableAt (by simp))
    ((u.contDiff.differentiable (by simp)) w)]
""",
        "FunctionalAnalysis apply the nonzero smoothness order before fderiv_mul",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
