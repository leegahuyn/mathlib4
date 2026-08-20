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
        """    (curvatureAlgebra.formPresheaf 2).IsGluing C
      (localCurvatureFamily C A) (connectionCurvature Aglobal) := by
  intro i
  calc
    restrictForm (C.piece_le_target i) (connectionCurvature Aglobal) =
        connectionCurvature
          (connectionPresheaf.res (C.piece_le_target i) Aglobal) :=
      connectionCurvature_restrict (C.piece_le_target i) Aglobal
    _ = connectionCurvature (A i) := congrArg connectionCurvature (hAglobal i)
    _ = localCurvatureFamily C A i := rfl
""",
        """    (curvatureAlgebra.formPresheaf 2).IsGluing C
      (localCurvatureFamily C A) (connectionCurvature Aglobal) := by
  intro i
  rw [connectionCurvature_restrict]
  exact congrArg connectionCurvature (hAglobal i)
""",
        "Mock2 avoid the dependent calc transitivity ambiguity in curvature gluing",
    )
    m2 = replace_exact(
        m2,
        """  simp [IsFlat, curvatureForm, zeroGlobalConnection,
    Proposition17And18FinalSpecialization.connectionCurvature,
    Proposition17And18FinalSpecialization.curvature_apply]
""",
        """  simp [IsFlat, curvatureForm, zeroGlobalConnection,
    Proposition17And18FinalSpecialization.zeroConnection,
    Proposition17And18FinalSpecialization.connectionCurvature,
    Proposition17And18FinalSpecialization.curvature_apply]
""",
        "Mock2 unfold the concrete zero connection in the flatness witness",
    )
    m2 = replace_exact(
        m2,
        """structure HypothesisH2 (Mq : MqFunctional μ I)
    (Rq : RqFunctional μ I) : Prop where
""",
        """structure HypothesisH2 (Mq : MqFunctional μ I)
    (Rq : RqFunctional μ I) : Type where
""",
        "Mock2 make H2 a certificate type because it contains a vacuum witness",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  · change
      1 / ((x : ℂ) + (Y : ℂ) * Complex.I) ^ 2 =
        1 / (-((x : ℂ) + (Y : ℂ) * Complex.I)) ^ 2
    rw [neg_sq]
""",
        """  · simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve, neg_sq]
""",
        "Mock2 Advanced unfold the finite-cusp tangent before normalizing the even square",
    )
    m2a = replace_exact(
        m2a,
        """  field_simp [hτ]
  simpa [mul_comm]
""",
        """  field_simp [hτ]
  rw [sub_eq_add_neg]
""",
        "Mock2 Advanced close the post-field-simp subtraction definitionally",
    )
    m2a = replace_exact(
        m2a,
        """  norm_num [pow_two, Matrix.mul_fin_two] <;> ring_nf
""",
        """  norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
""",
        "Mock2 Advanced evaluate the concrete two-by-two matrix product entrywise",
    )
    m2a = replace_exact(
        m2a,
        """  constructor
  · intro h a
    simpa only [Function.comp_apply, Pi.mul_apply] using h a
  · intro h a
    simpa only [Function.comp_apply, Pi.mul_apply] using h a
""",
        """  constructor
  · intro h a
    filter_upwards [h a] with τ hτ
    exact hτ
  · intro h a
    filter_upwards [h a] with τ hτ
    exact hτ
""",
        "Mock2 Advanced bridge the two AE equality presentations pointwise",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  calc
    _ = -(fixedPhaseGreenScalarDensity n u v z *
        ((ξ.re : ℂ) + (ξ.im : ℂ) * Complex.I)) := by ring
    _ = -(fixedPhaseGreenScalarDensity n u v z * ξ) := by
      rw [Complex.re_add_im]
""",
        """  calc
    _ = -(fixedPhaseGreenScalarDensity n u v z *
        ((ξ.re : ℂ) + (ξ.im : ℂ) * Complex.I)) := by ring
    _ = -fixedPhaseGreenScalarDensity n u v z * ξ := by
      rw [Complex.re_add_im, neg_mul]
""",
        "FunctionalAnalysis finish the flux identity with the outer negation distributed",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
