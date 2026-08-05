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
        """  ambient : QGaugePresheaf Open
  boundary : QGaugePresheaf Open
""",
        """  ambient : QGaugePresheaf.{u, v} Open
  boundary : QGaugePresheaf.{u, v} Open
""",
        "Mock2 pin the balanced category presheaf value universe",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  apply (graphCoordinateEquiv
    (H0 := H0) (HR := HR) (HL := HL)).injective
  simp [graphCoordinateEquiv, hz0, hsnd]
""",
        """  apply (graphCoordinateEquiv
    (H0 := H0) (HR := HR) (HL := HL)).injective
  change (z.fst, z.snd) = (0, 0)
  exact Prod.ext hz0 hsnd
""",
        "Mock2 Advanced prove the completed graph vector zero in product coordinates",
    )
    m2a = replace_exact(
        m2a,
        """theorem norm_valueProjection_le
    (T : H0 →ₗ.[ℂ] DerivativeAmbient (HR := HR) (HL := HL))
    (u : graphCompletion T) :
    ‖valueProjection T u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [graphCompletion_norm_sq T u]
  positivity
""",
        """theorem norm_valueProjection_le
    (T : H0 →ₗ.[ℂ] DerivativeAmbient (HR := HR) (HL := HL))
    (u : graphCompletion T) :
    ‖valueProjection T u‖ ≤ ‖u‖ := by
  nlinarith [graphCompletion_norm_sq T u,
    sq_nonneg ‖raisingProjection T u‖,
    sq_nonneg ‖loweringProjection T u‖,
    norm_nonneg (valueProjection T u), norm_nonneg u]
""",
        "Mock2 Advanced derive graph-coordinate contractivity from the norm identity",
    )
    m2a = replace_exact(
        m2a,
        """theorem CommonCoreOperators.denseRange_valueProjection_jointPMap
    (D : CommonCoreOperators (H0 := H0) (HR := HR) (HL := HL)) :
    DenseRange (valueProjection D.jointPMap) := by
  apply D.dense_core.mono
  intro x hx
  let xd : D.jointPMap.domain :=
    ⟨x, by simpa only [CommonCoreOperators.jointPMap_domain] using hx⟩
  let z : GraphAmbient (H0 := H0) (HR := HR) (HL := HL) :=
    (x, D.jointPMap xd)
  have hz : z ∈ transportedGraph D.jointPMap := by
    change (x, D.jointPMap xd) ∈ D.jointPMap.graph
    exact D.jointPMap.mem_graph xd
  let uz : graphCompletion D.jointPMap :=
    ⟨z, (transportedGraph D.jointPMap).le_topologicalClosure hz⟩
  exact ⟨uz, rfl⟩
""",
        """theorem CommonCoreOperators.denseRange_valueProjection_jointPMap
    (D : CommonCoreOperators (H0 := H0) (HR := HR) (HL := HL)) :
    DenseRange (valueProjection D.jointPMap) := by
  apply D.dense_core.mono
  intro x hx
  let xd : D.jointPMap.domain :=
    ⟨x, by
      rw [CommonCoreOperators.jointPMap_domain]
      exact hx⟩
  let z : GraphAmbient (H0 := H0) (HR := HR) (HL := HL) :=
    (graphCoordinateEquiv
      (H0 := H0) (HR := HR) (HL := HL)).symm
        (x, D.jointPMap xd)
  have hz : z ∈ transportedGraph D.jointPMap := by
    apply (mem_transportedGraph_iff D.jointPMap z).2
    simpa [z, graphCoordinateEquiv] using D.jointPMap.mem_graph xd
  let uz : graphCompletion D.jointPMap :=
    ⟨z, (transportedGraph D.jointPMap).le_topologicalClosure hz⟩
  refine ⟨uz, ?_⟩
  change z.fst = x
  simp [z, graphCoordinateEquiv]
""",
        "Mock2 Advanced embed the dense core through the actual WithLp coordinate equivalence",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem gammaTwoMoebiusChart_hasStrictDerivAt
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    HasStrictDerivAt (gammaTwoMoebiusChart γ)
      (1 / inverseEtaPaperOrbitDenom γ z ^ 2) (z : ℂ) := by
  let gℝ : SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
      (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)))
  have hdet : ((gℝ.val.det : ℝ) : ℂ) = 1 := by
    rw [gℝ.det_coe]
    norm_num
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, gℝ, hdet, one_div] using
    (UpperHalfPlane.hasStrictDerivAt_smul
      (inverseEtaPaperOrbit_det_pos γ) z)
""",
        """theorem gammaTwoMoebiusChart_hasStrictDerivAt
    (γ : GammaTwoQuotientGeometry.GammaTwo) (z : ℍ) :
    HasStrictDerivAt (gammaTwoMoebiusChart γ)
      (1 / inverseEtaPaperOrbitDenom γ z ^ 2) (z : ℂ) := by
  let g : GL (Fin 2) ℝ :=
    (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) :
      GL (Fin 2) ℝ)
  have hdet : g.det = 1 := by
    simp [g]
  have hg : 0 < g.det.val := by
    simp [hdet]
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, g, hdet, one_div] using
    (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z)
""",
        "FunctionalAnalysis normalize the GammaTwo action through its actual GL matrix",
    )
    fa = replace_exact(
        fa,
        """  have hG : HasFDerivAt G
      (((inverseEtaPaperOrbitDenom γ z ^ 2)⁻¹) •
        (1 : ℂ →L[ℝ] ℂ)) (z : ℂ) := by
    have hComplex :=
      (gammaTwoMoebiusChart_hasStrictDerivAt γ z).hasDerivAt
    simpa [G, g, gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
      div_eq_mul_inv] using hComplex.complexToReal_fderiv
  have hOuter : DifferentiableAt ℝ (upperLift f) (G (z : ℂ)) := by
    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      (RealSmooth.contDiffAt_upperLift hf
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp)
""",
        """  have hG : HasFDerivAt G
      (UpperHalfPlane.smulFDeriv g (z : ℂ)) (z : ℂ) := by
    simpa [G] using
      (UpperHalfPlane.hasStrictFDerivAt_smul g z).hasFDerivAt
  have hG_apply (η : ℂ) :
      UpperHalfPlane.smulFDeriv g (z : ℂ) η =
        (1 / inverseEtaPaperOrbitDenom γ z ^ 2) * η := by
    have hg : 0 < g.det.val := by
      simpa [g] using inverseEtaPaperOrbit_det_pos γ
    simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, hg,
      inverseEtaPaperOrbitDenom, inverseEtaPaperOrbit_det_eq_one,
      g, smul_eq_mul]
  have hOuter : DifferentiableAt ℝ (upperLift f) (G (z : ℂ)) := by
    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      (RealSmooth.contDiffAt_upperLift hf
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp)
""",
        "FunctionalAnalysis use Mathlib's bundled real derivative for the GammaTwo action",
    )
    fa = replace_exact(
        fa,
        """  have hApply := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L ξ) hComp.fderiv
  simpa [G, ContinuousLinearMap.comp_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hApply
""",
        """  have hApply := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L ξ) hComp.fderiv
  simp only [ContinuousLinearMap.comp_apply] at hApply
  rw [hG_apply] at hApply
  simpa [G, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hApply
""",
        "FunctionalAnalysis evaluate the bundled Möbius derivative in the chain rule",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
