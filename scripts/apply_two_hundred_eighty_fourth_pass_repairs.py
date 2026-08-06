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
        """  · have hdiv :
        (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ g.1) 0 0 /
          (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ g.1) 1 0 ≠ 0 :=
      div_ne_zero ha hc
    simpa [OnePoint.smul_infty_eq_ite, hc] using hdiv
""",
        """  · have hdiv :
        (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ g.1) 0 0 /
          (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ g.1) 1 0 ≠ 0 :=
      div_ne_zero ha hc
    rw [OnePoint.smul_infty_eq_ite, if_neg hc]
    simpa only [OnePoint.some_eq_iff] using hdiv
""",
        "Mock2 close the nonzero projective cusp branch directly",
    )
    m2 = replace_exact(
        m2,
        """def verticalSolution (r : RadiusBase) :
    Fibre twoComponentAnalyticData r :=
  ⟨⟨WithLp.toLp 2 (0, 1), by simp [twoComponentAnalyticData]⟩, by
    change WithLp.toLp 2 (0, 0) = 0
    apply WithLp.ofLp_injective 2
    simp⟩
""",
        """def verticalSolution (r : RadiusBase) :
    Fibre twoComponentAnalyticData r := by
  let u : twoComponentAnalyticData.domain :=
    ⟨WithLp.toLp 2 ((0 : ℂ), (1 : ℂ)), by simp [twoComponentAnalyticData]⟩
  refine ⟨u, ?_⟩
  change twoComponentAnalyticData.totalOperator u = 0
  apply WithLp.ofLp_injective 2
  simp [AnalyticData.totalOperator, twoComponentAnalyticData,
    firstCoordinateOperator, u]
""",
        "Mock2 construct the vertical kernel vector with typed coordinates",
    )
    m2 = replace_exact(
        m2,
        """  have hneg :
      scalarSolution 1 quarterRadius = -scalarSolution 1 quarterRadius := by
    simpa using hvalue
""",
        """  have hneg :
      scalarSolution 1 quarterRadius = -scalarSolution 1 quarterRadius := by
    simpa [scalarSolution] using hvalue
""",
        "Mock2 normalize the radius-independent scalar solution",
    )
    m2 = replace_exact(
        m2,
        "structure LiteralPaperAnalyticClosure extends LiteralDefinition11Closure : Prop where",
        "structure LiteralPaperAnalyticClosure : Prop extends LiteralDefinition11Closure where",
        "Mock2 use the current structure-extends syntax",
    )
    m2 = replace_exact(
        m2,
        "theorem certificate : Certificate :=",
        "noncomputable def certificate : Certificate :=",
        "Mock2 make the integrated certificate a data definition",
    )
    m2 = replace_exact(
        m2,
        "theorem checklist_4_6_through_5_3_unconditional : Certificate :=",
        "noncomputable def checklist_4_6_through_5_3_unconditional : Certificate :=",
        "Mock2 make the paper-facing certificate a data definition",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  rw [Set.preimage_image_eq _ UpperHalfPlane.coe_injective] at h
  change IntegrableOn
    (fun x : UpperHalfPlane => fdHeightMajorant ((x : ℂ).im))
    ModularGroup.fd (volume.comap UpperHalfPlane.coe)
  simpa only [Function.comp_apply] using h
""",
        """  rw [Set.preimage_image_eq _ UpperHalfPlane.coe_injective] at h
  have hfun :
      ((fun z : ℂ => fdHeightMajorant z.im) ∘ UpperHalfPlane.coe) =
        (fun x : UpperHalfPlane => fdHeightMajorant ((x : ℂ).im)) := by
    funext x
    rfl
  rw [hfun] at h
  exact h
""",
        "Mock2 Advanced identify the pulled-back height function extensionally",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 :=
  Q.baseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_baseExtension_le x

""",
        """theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.baseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_baseExtension_le x

""",
        "FunctionalAnalysis fix the completion scalar instance for the base norm",
    )
    fa = replace_exact(
        fa,
        """theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 :=
  Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_raiseExtension_le x

""",
        """theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_raiseExtension_le x

""",
        "FunctionalAnalysis fix the completion scalar instance for the raised norm",
    )
    fa = replace_exact(
        fa,
        """theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 :=
  Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_lowerExtension_le x

""",
        """theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_lowerExtension_le x

""",
        "FunctionalAnalysis fix the completion scalar instance for the lowered norm",
    )
    fa = replace_exact(
        fa,
        """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion :=
  innerSLFlip ℂ
""",
        """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact innerSLFlip ℂ
""",
        "FunctionalAnalysis fix the completion scalar instance for the energy operator",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
