from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """def sectionGaugePresheaf (D : AnalyticData V) :
    QGaugePresheaf (TopologicalSpace.Opens RadiusBase) where
  Field U := (Definition11.Lq D).Fiber U
  res hUW s := (Definition11.Lq D).res hUW s
  res_id := (Definition11.Lq D).res_id
  res_comp := (Definition11.Lq D).res_comp
""",
        """abbrev sectionGaugePresheaf (D : AnalyticData V) :
    QGaugePresheaf (TopologicalSpace.Opens RadiusBase) where
  Field U := LocallyConstant U D.solutionSpace
  res hUW s := (Definition11.Lq D).res hUW s
  res_id := (Definition11.Lq D).res_id
  res_comp := (Definition11.Lq D).res_comp
""",
        "Mock2 expose the Definition 11 section type transparently",
    )
    m2 = replace_exact(
        m2,
        """    (s : (sectionGaugePresheaf D).Field W) (x : U) :
    (sectionGaugePresheaf D).res hUW s x = s ⟨x.1, hUW x.2⟩ :=
  rfl
""",
        """    (s : (sectionGaugePresheaf D).Field W) (x : U) :
    ((sectionGaugePresheaf D).res hUW s).toFun x =
      s.toFun ⟨x.1, hUW x.2⟩ :=
  rfl
""",
        "Mock2 use the locally constant section projection explicitly",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem denseRange_graphCoreToGraphSobolev
    (D : CoreOperators (V := V) (H0 := H0) (HR := HR) (HL := HL)) :
    DenseRange (graphCoreToGraphSobolev D) := by
  change DenseRange (Set.inclusion (graphCore_le_graphSobolev D))
  simpa [-SetLike.coe_sort_coe]
""",
        """theorem denseRange_graphCoreToGraphSobolev
    (D : CoreOperators (V := V) (H0 := H0) (HR := HR) (HL := HL)) :
    DenseRange (graphCoreToGraphSobolev D) := by
  change DenseRange (Set.inclusion (graphCore_le_graphSobolev D))
  rw [denseRange_inclusion_iff]
  · intro x hx
    exact hx
  · intro x hx
    exact graphCore_le_graphSobolev D hx
""",
        "Mock2 Advanced reuse the proved dense inclusion criterion",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, inverseEtaPaperOrbit_det_eq_one,
    one_div] using
""",
        """  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, inverseEtaPaperOrbit_det_eq_one,
    Matrix.SpecialLinearGroup.det_coe, one_div] using
""",
        "FunctionalAnalysis simplify the mapped special-linear determinant",
    )
    fa = replace_exact(
        fa,
        """    have hDeriv :=
      (gammaTwoMoebiusChart_hasStrictDerivAt γ (⟨w, hw⟩ : ℍ)).differentiableAt
    exact hDeriv.differentiableWithinAt
""",
        """    have hDeriv :=
      (gammaTwoMoebiusChart_hasStrictDerivAt γ
        (⟨w, hw⟩ : ℍ)).hasDerivAt.differentiableAt
    exact hDeriv.differentiableWithinAt
""",
        "FunctionalAnalysis project differentiability through HasDerivAt",
    )
    fa = replace_exact(
        fa,
        """theorem d1_comp_gammaTwo_smul
    (γ : GammaTwoQuotientGeometry.GammaTwo) {f : ℍ → ℂ}
    (hf : RealSmooth f) (z : ℍ) (ξ : ℂ) :
    d1 (fun w ↦ f (((γ : GammaTwoQuotientGeometry.GammaTwo) :
        SL(2, ℤ)) • w)) z ξ =
      d1 f ((((γ : GammaTwoQuotientGeometry.GammaTwo) :
        SL(2, ℤ)) • z))
        (ξ / inverseEtaPaperOrbitDenom γ z ^ 2) := by
  let g : GL (Fin 2) ℝ :=
    (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) :
      GL (Fin 2) ℝ)
  let G : ℂ → ℂ := fun w ↦
    ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)
  have hG : HasFDerivAt G
      (((inverseEtaPaperOrbitDenom γ z ^ 2)⁻¹) •
        (1 : ℂ →L[ℝ] ℂ)) (z : ℂ) := by
    have hComplex :=
      (UpperHalfPlane.hasStrictDerivAt_smul
        (inverseEtaPaperOrbit_det_pos γ) z).hasDerivAt
    simpa [G, g, inverseEtaPaperOrbitDenom,
      inverseEtaPaperOrbit_det_eq_one, div_eq_mul_inv] using
      hComplex.complexToReal_fderiv
  have hOuter : DifferentiableAt ℝ (upperLift f)
      ((((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z :
        ℍ) : ℂ) :=
    (RealSmooth.contDiffAt_upperLift hf
      ((((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z))).
        differentiableAt (by simp)
  have hComp := hOuter.hasFDerivAt.comp (z : ℂ) hG
  have hFunctions :
      upperLift (fun w ↦ f
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • w)) =
        upperLift f ∘ G := by
    funext w
    simp [upperLift, G, g, Function.comp_def]
  unfold d1
  rw [hFunctions]
  have hApply := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L ξ) hComp.fderiv
  simpa [G, ContinuousLinearMap.comp_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hApply
""",
        """theorem d1_comp_gammaTwo_smul
    (γ : GammaTwoQuotientGeometry.GammaTwo) {f : ℍ → ℂ}
    (hf : RealSmooth f) (z : ℍ) (ξ : ℂ) :
    d1 (fun w ↦ f (((γ : GammaTwoQuotientGeometry.GammaTwo) :
        SL(2, ℤ)) • w)) z ξ =
      d1 f ((((γ : GammaTwoQuotientGeometry.GammaTwo) :
        SL(2, ℤ)) • z))
        (ξ / inverseEtaPaperOrbitDenom γ z ^ 2) := by
  let g : GL (Fin 2) ℝ :=
    (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) :
      GL (Fin 2) ℝ)
  let G : ℂ → ℂ := fun w ↦
    ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)
  have hG : HasFDerivAt G
      (((inverseEtaPaperOrbitDenom γ z ^ 2)⁻¹) •
        (1 : ℂ →L[ℝ] ℂ)) (z : ℂ) := by
    have hComplex :=
      (UpperHalfPlane.hasStrictDerivAt_smul
        (inverseEtaPaperOrbit_det_pos γ) z).hasDerivAt
    simpa [G, g, inverseEtaPaperOrbitDenom,
      inverseEtaPaperOrbit_det_eq_one,
      Matrix.SpecialLinearGroup.det_coe, div_eq_mul_inv] using
      hComplex.complexToReal_fderiv
  have hOuter : DifferentiableAt ℝ (upperLift f) (G (z : ℂ)) := by
    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      (RealSmooth.contDiffAt_upperLift hf
        ((((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp))
  have hComp := hOuter.hasFDerivAt.comp (z : ℂ) hG
  have hLocal :
      upperLift (fun w ↦ f
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • w)) =ᶠ[
          nhds (z : ℂ)] upperLift f ∘ G := by
    filter_upwards [
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp [upperLift, Function.comp_def, G, g,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul]
  unfold d1
  rw [hLocal.fderiv_eq]
  have hApply := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L ξ) hComp.fderiv
  simpa [G, ContinuousLinearMap.comp_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hApply
""",
        "FunctionalAnalysis use the local chart chain rule at the correct basepoint",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
