from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


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
        """    change F.res ((U i).infLELeft (U j)) (sf i) =
      F.res ((U i).infLERight (U j)) (sf j) at hij
    exact hij
""",
        """    change F.res ((U i).infLELeft (U j)).le (sf i) =
      F.res ((U i).infLERight (U j)).le (sf j) at hij
    exact hij
""",
        "Mock2 extract order proofs from the Opens overlap morphisms",
    )
    m2 = replace_exact(
        m2,
        "SpecialLinearGroup.mapGL ℝ g.1",
        "Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ g.1",
        "Mock2 fully qualify the integral special-linear map",
        expected=9,
    )
    m2 = replace_exact(
        m2,
        "(⊤ : OnePoint ℝ)",
        "(OnePoint.infty : OnePoint ℝ)",
        "Mock2 use the actual one-point infinity constructor",
        expected=5,
    )
    m2 = replace_exact(
        m2,
        """def verticalSolution (r : RadiusBase) :
    Fibre twoComponentAnalyticData r :=
  ⟨⟨WithLp.toLp 2 (0, 1), by simp [twoComponentAnalyticData]⟩, by
    simp [AnalyticData.solutionSpace, AnalyticData.totalOperator,
      twoComponentAnalyticData, firstCoordinateOperator]⟩
""",
        """def verticalSolution (r : RadiusBase) :
    Fibre twoComponentAnalyticData r :=
  ⟨⟨WithLp.toLp 2 (0, 1), by simp [twoComponentAnalyticData]⟩, by
    change WithLp.toLp 2 (0, 0) = 0
    apply WithLp.ofLp_injective 2
    simp⟩
""",
        "Mock2 prove the vertical vector lies in the projection kernel",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  simpa only [Function.comp_apply,
    Set.preimage_image_eq _ UpperHalfPlane.coe_injective] using h
""",
        """  rw [Set.preimage_image_eq _ UpperHalfPlane.coe_injective] at h
  change IntegrableOn
    (fun x : UpperHalfPlane => fdHeightMajorant ((x : ℂ).im))
    ModularGroup.fd (volume.comap UpperHalfPlane.coe)
  simpa only [Function.comp_apply] using h
""",
        "Mock2 Advanced simplify the comap set before the coerced height function",
    )
    m2a = replace_exact(
        m2a,
        """theorem integralMatrixAction_measurableEmbedding
    (g : Gamma2SixCellPolygon.IntegralSpecialLinear) :
    MeasurableEmbedding (fun τ : UpperHalfPlane => g • τ) := by
  simpa only [MulAction.compHom_smul_def] using
    (Homeomorph.smul
      ((Matrix.SpecialLinearGroup.mapGL
        (n := Fin 2) (R := ℤ) ℝ) g)).measurableEmbedding
""",
        """theorem integralMatrixAction_measurableEmbedding
    (g : Gamma2SixCellPolygon.IntegralSpecialLinear) :
    MeasurableEmbedding (fun τ : UpperHalfPlane => g • τ) := by
  change MeasurableEmbedding
    ⇑(Homeomorph.smul
      ((Matrix.SpecialLinearGroup.mapGL
        (n := Fin 2) (R := ℤ) ℝ) g))
  exact
    (Homeomorph.smul
      ((Matrix.SpecialLinearGroup.mapGL
        (n := Fin 2) (R := ℤ) ℝ) g)).measurableEmbedding
""",
        "Mock2 Advanced identify the integral matrix action with its homeomorphism",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
