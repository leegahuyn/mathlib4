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
        """  · intro t ht
    apply huniq t
    intro i
    change (toMathlibPresheaf P).map (le_iSup U i).op t = sf i
    exact ht i
""",
        """  · intro t ht
    apply huniq t
    intro i
    change P.res (le_iSup U i) t = sf i
    exact ht i
""",
        "Mock2 express uniqueness through the lightweight restriction",
    )
    m2 = replace_exact(
        m2,
        """def Bq : QGaugePresheaf Opens :=
  locallyConstantQGaugePresheaf (BoundaryDatum A)
""",
        """def Bq : QGaugePresheaf.{0, v} Opens where
  Field U := LocallyConstant U (BoundaryDatum A)
  res hUV s := LocallyConstant.comap
    (LocallyConstantValueSheaf.openInclusion hUV) s
  res_id := by
    intro U s
    apply LocallyConstant.ext
    intro x
    rfl
  res_comp := by
    intro U W Z hUW hWZ s
    apply LocallyConstant.ext
    intro x
    rfl
""",
        "Mock2 construct the boundary presheaf directly in the ambient fibre universe",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  simpa [productKernel, unitIntervalDensity, hx, stageTest, ht] using
    KuznetsovInterface.fourierPositiveSmoothTentFunction_pos_zero T hT
""",
        """  simpa [productKernel, unitIntervalDensity, hx, stageTest, ht, smoothTest] using
    KuznetsovInterface.fourierPositiveSmoothTentFunction_pos_zero T hT
""",
        "Mock2 Advanced unfold the smooth test in the central positivity proof",
    )
    m2a = replace_exact(
        m2a,
        """    x = (a + b) / 2 := by
  linarith
""",
        """    x = (a + b) / 2 := by
  subst a
  subst b
  ring
""",
        "Mock2 Advanced prove scalar averaging algebraically",
    )
    m2a = replace_exact(
        m2a,
        """    energy + boundary = rhs ↔ energy = rhs - boundary := by
  constructor <;> intro h <;> linarith
""",
        """    energy + boundary = rhs ↔ energy = rhs - boundary := by
  constructor <;> intro h <;> linear_combination h
""",
        "Mock2 Advanced move the boundary term by ring algebra",
    )
    m2a = replace_exact(
        m2a,
        """    have hlinear : coercivity * solutionNorm ≤ rhsNorm := by
      exact (mul_le_mul_right hsolutionPos).mp (by
        simpa [mul_assoc] using hbound)
""",
        """    have hlinear : coercivity * solutionNorm ≤ rhsNorm := by
      nlinarith [hbound]
""",
        "Mock2 Advanced cancel the positive solution norm",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  unfold d1 inverseEtaPaperOrbitPhaseFunction upperLift
  simp
""",
        """  unfold d1 inverseEtaPaperOrbitPhaseFunction upperLift
  change
    (fderiv ℝ
      (fun _ : ℂ =>
        (inverseEtaMultiplier
          GammaTwoQuotientGeometry.GammaTwo).nu γ)
      (z : ℂ)) ξ = 0
  simp only [fderiv_const, ContinuousLinearMap.zero_apply]
""",
        "FunctionalAnalysis differentiate the constant orbit phase explicitly",
    )
    fa = replace_exact(
        fa,
        """      GL (Fin 2) ℝ)).val.det) := by
  simp
""",
        """      GL (Fin 2) ℝ)).val.det) := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  norm_num
""",
        "FunctionalAnalysis expose the special-linear determinant unit",
    )
    fa = replace_exact(
        fa,
        """        (UpperHalfPlane.hasStrictDerivAt_smul
          (inverseEtaPaperOrbit_det_pos γ)
          (⟨w, hw⟩ : ℍ)).differentiableAt
""",
        """        (UpperHalfPlane.hasStrictDerivAt_smul
          (inverseEtaPaperOrbit_det_pos γ)
          (⟨w, hw⟩ : ℍ)).hasDerivAt.differentiableAt
""",
        "FunctionalAnalysis pass through HasDerivAt before differentiability",
    )
    fa = replace_exact(
        fa,
        """      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
        (g • (⟨w, hw⟩ : ℍ)).im_pos).comp w hAction
""",
        """      by
        simpa only [Function.comp_apply] using
          (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
            (g • (⟨w, hw⟩ : ℍ)).im_pos).comp w hAction
""",
        "FunctionalAnalysis identify eta composition with the displayed lambda",
    )
    fa = replace_exact(
        fa,
        ").\n        differentiableWithinAt",
        ").differentiableWithinAt",
        "FunctionalAnalysis repair split differentiableWithinAt projections",
        expected=2,
    )
    fa = replace_exact(
        fa,
        ").restrictScalars.\n        contDiffOn_of_completeSpace",
        ").restrictScalars.contDiffOn_of_completeSpace",
        "FunctionalAnalysis repair split restrictScalars projections",
        expected=5,
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
