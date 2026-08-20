from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


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
        """  · ring

/-- Exact tangent formula for the cusp at one. -/
""",
        """  · unfold cuspFiniteAmbientTangent cuspHorizontalAmbientCurve
    ring_nf

/-- Exact tangent formula for the cusp at one. -/
""",
        "Mock2 Advanced unfold the reciprocal tangent before ring normalization",
    )
    m2a = replace_exact(
        m2a,
        """  field_simp [hτ]
  ring

theorem factor_sq""",
        """  field_simp [hτ]
  ring_nf

theorem factor_sq""",
        "Mock2 Advanced normalize the casted factor base product",
    )
    m2a = replace_exact(
        m2a,
        """@[simp]
theorem isAutomorphicClass_zero (ν : Multiplier) :
    IsAutomorphicClass ν (0 : Section) := by
  intro a
  rw [pullback_zero]
  exact (mul_zero (factorClass ν a)).symm
""",
        """@[simp]
theorem isAutomorphicClass_zero (ν : Multiplier) :
    IsAutomorphicClass ν (0 : Section) := by
  intro a
  rw [pullback_zero]
  apply AEEqFun.ext
  filter_upwards with x
  change (0 : ℂ) = factorClass ν a x * 0
  simp
""",
        "Mock2 Advanced prove zero automorphy pointwise in both conventions",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """theorem IsAutomorphicClass.add
    {ν : Multiplier} {u v : Section}
    (hu : IsAutomorphicClass ν u)
    (hv : IsAutomorphicClass ν v) :
    IsAutomorphicClass ν (u + v) := by
  intro a
  rw [pullback_add, hu a, hv a, mul_add]
""",
        """theorem IsAutomorphicClass.add
    {ν : Multiplier} {u v : Section}
    (hu : IsAutomorphicClass ν u)
    (hv : IsAutomorphicClass ν v) :
    IsAutomorphicClass ν (u + v) := by
  intro a
  rw [pullback_add, hu a, hv a]
  apply AEEqFun.ext
  filter_upwards with x
  exact (mul_add _ _ _).symm
""",
        "Mock2 Advanced prove additive automorphy pointwise in both conventions",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """  filter_upwards [hcentral, AEEqFun.coeFn_zero] with τ hτ hzero
  rw [hzero]
""",
        """  filter_upwards [hcentral] with τ hτ
  change u τ = 0
""",
        "Mock2 Advanced remove the polymorphic quotient-zero witness",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """    (continuousAt_jacobiTheta τ.im_pos).comp τ
      UpperHalfPlane.continuous_coe.continuousAt
""",
        """    (continuousAt_jacobiTheta τ.im_pos).comp
      UpperHalfPlane.continuous_coe.continuousAt
""",
        "Mock2 Advanced use the current ContinuousAt.comp API",
    )
    m2a = replace_exact(
        m2a,
        """  simp only [IsAutomorphicClass, pullback, factorClass,
    AEEqFun.compMeasurePreserving_mk, AEEqFun.mk_mul_mk,
    AEEqFun.mk_eq_mk,
    GenuineInverseHalfWeightAutomorphy.IsAEAutomorphic,
    Function.comp_apply, Pi.mul_apply]
""",
        """  simp only [IsAutomorphicClass, pullback, factorClass,
    AEEqFun.compMeasurePreserving_mk, AEEqFun.mk_mul_mk,
    AEEqFun.mk_eq_mk,
    GenuineInverseHalfWeightAutomorphy.IsAEAutomorphic]
  constructor
  · intro h a
    simpa only [Function.comp_apply, Pi.mul_apply] using h a
  · intro h a
    simpa only [Function.comp_apply, Pi.mul_apply] using h a
""",
        "Mock2 Advanced expose inverse automorphy representatives explicitly",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
