from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  · rw [show -((Y : ℂ) * Complex.I) + -(x : ℂ) =
        -((x : ℂ) + (Y : ℂ) * Complex.I) by ring, inv_neg]
    ring
""",
        """  · change
      1 / ((x : ℂ) + (Y : ℂ) * Complex.I) ^ 2 =
        1 / (-((x : ℂ) + (Y : ℂ) * Complex.I)) ^ 2
    rw [neg_sq]
""",
        "Mock2 Advanced reduce the finite-cusp tangent to neg_sq",
    )
    m2a = replace_exact(
        m2a,
        """  field_simp [hτ]
  ring

theorem factor_sq""",
        """  field_simp [hτ]
  ring_nf

theorem factor_sq""",
        "Mock2 Advanced normalize the commuting scalar order in the base product",
    )
    m2a = replace_exact(
        m2a,
        """  norm_num [Matrix.mul_fin_two] <;> ring
""",
        """  norm_num [Matrix.mul_fin_two] <;> ring_nf
""",
        "Mock2 Advanced normalize the evaluated zero-translation denominator",
    )
    m2a = replace_exact(
        m2a,
        """theorem standardTheta_isAutomorphic :
    IsAutomorphic standardThetaMultiplier ConcreteUnaryTheta.theta :=
""",
        """theorem standardTheta_isAutomorphic :
    GenuineHalfWeightAutomorphy.IsAutomorphic
      standardThetaMultiplier ConcreteUnaryTheta.theta :=
""",
        "Mock2 Advanced select the genuine automorphy predicate",
    )
    m2a = replace_exact(
        m2a,
        """  simp only [IsAutomorphicClass, pullback, factorClass,
    AEEqFun.compMeasurePreserving_mk, AEEqFun.mk_mul_mk,
    AEEqFun.mk_eq_mk, GenuineHalfWeightAutomorphy.IsAEAutomorphic,
    Function.comp_apply, Pi.mul_apply]
""",
        """  simp only [IsAutomorphicClass, pullback, factorClass,
    AEEqFun.compMeasurePreserving_mk, AEEqFun.mk_mul_mk,
    AEEqFun.mk_eq_mk, GenuineHalfWeightAutomorphy.IsAEAutomorphic]
  constructor
  · intro h a
    simpa only [Function.comp_apply, Pi.mul_apply] using h a
  · intro h a
    simpa only [Function.comp_apply, Pi.mul_apply] using h a
""",
        "Mock2 Advanced pass explicitly between eventual function equality and pointwise AE form",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  unfold fluxOneFormValue fixedPhaseGreenFluxX fixedPhaseGreenFluxY
  rw [← Complex.re_add_im ξ]
  simp <;> ring
""",
        """  unfold fluxOneFormValue fixedPhaseGreenFluxX fixedPhaseGreenFluxY
  calc
    _ = -(fixedPhaseGreenScalarDensity n u v z *
        ((ξ.re : ℂ) + (ξ.im : ℂ) * Complex.I)) := by ring
    _ = -(fixedPhaseGreenScalarDensity n u v z * ξ) := by
      rw [Complex.re_add_im]
""",
        "FunctionalAnalysis reconstruct the complex flux without simp reversing re_add_im",
    )
    fa = replace_exact(
        fa,
        """  rw [← mul_assoc, hSignC]
  ring
""",
        """  rw [← mul_assoc, hSignC]
""",
        "FunctionalAnalysis remove the tactic after the orientation goal is closed",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
