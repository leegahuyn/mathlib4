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
        """  field_simp [hτ]
  ring_nf

theorem factor_sq""",
        """  field_simp [hτ]
  simpa [mul_comm]

theorem factor_sq""",
        "Mock2 Advanced close the base product by explicit commutativity",
    )
    m2a = replace_exact(
        m2a,
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
        """@[simp]
theorem isAutomorphicClass_zero (ν : Multiplier) :
    IsAutomorphicClass ν (0 : Section) := by
  intro a
  rw [pullback_zero]
  exact (mul_zero (factorClass ν a : Section)).symm
""",
        "Mock2 Advanced prove zero automorphy as a typed Section identity",
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
  rw [pullback_add, hu a, hv a]
  apply AEEqFun.ext
  filter_upwards with x
  exact (mul_add _ _ _).symm
""",
        """theorem IsAutomorphicClass.add
    {ν : Multiplier} {u v : Section}
    (hu : IsAutomorphicClass ν u)
    (hv : IsAutomorphicClass ν v) :
    IsAutomorphicClass ν (u + v) := by
  intro a
  rw [pullback_add, hu a, hv a]
  exact (mul_add (factorClass ν a : Section) u v).symm
""",
        "Mock2 Advanced prove additive automorphy as a typed Section identity",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """  filter_upwards [hcentral] with τ hτ
  change u τ = 0
  have hfixed :
""",
        """  filter_upwards [hcentral] with τ hτ
  suffices hzero : u τ = (0 : ℂ) by
    simpa using hzero
  have hfixed :
""",
        "Mock2 Advanced bridge quotient-zero evaluation before the central-phase proof",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """theorem continuous_concreteTheta :
    Continuous ConcreteUnaryTheta.theta := by
  rw [continuous_iff_continuousAt]
  intro τ
  simpa [ConcreteUnaryTheta.theta, Function.comp_def] using
    (continuousAt_jacobiTheta τ.im_pos).comp
      UpperHalfPlane.continuous_coe.continuousAt
""",
        """theorem continuous_concreteTheta :
    Continuous ConcreteUnaryTheta.theta := by
  rw [continuous_iff_continuousAt]
  intro τ
  change ContinuousAt (fun x : UpperHalfPlane => jacobiTheta (x : ℂ)) τ
  exact
    (continuousAt_jacobiTheta τ.im_pos).comp
      UpperHalfPlane.continuous_coe.continuousAt
""",
        "Mock2 Advanced state concrete theta continuity in its unfolded function type",
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
    simpa only [Function.comp_apply, Pi.mul_apply] using hτ
  · intro h a
    filter_upwards [h a] with τ hτ
    simpa only [Function.comp_apply, Pi.mul_apply] using hτ
""",
        "Mock2 Advanced convert inverse automorphy equalities pointwise under eventually",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
