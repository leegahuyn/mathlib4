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
        """  field_simp [hτ]
  simpa [mul_comm]

theorem factor_sq""",
        """  field_simp [hτ]
  simpa [mul_comm, sub_eq_add_neg]

theorem factor_sq""",
        "Mock2 Advanced normalize subtraction after commuting the base product",
    )
    m2a = replace_exact(
        m2a,
        """@[simp]
theorem isAutomorphicClass_zero (ν : Multiplier) :
    IsAutomorphicClass ν (0 : Section) := by
  intro a
  rw [pullback_zero]
  exact (mul_zero (factorClass ν a : Section)).symm
""",
        """@[simp]
theorem isAutomorphicClass_zero (ν : Multiplier) :
    IsAutomorphicClass ν (0 : Section) := by
  intro a
  rw [pullback_zero]
  refine AEEqFun.induction_on (factorClass ν a) ?_
  intro f hf
  simp [AEEqFun.zero_def]
""",
        "Mock2 Advanced prove zero automorphy on measurable representatives",
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
  exact (mul_add (factorClass ν a : Section) u v).symm
""",
        """theorem IsAutomorphicClass.add
    {ν : Multiplier} {u v : Section}
    (hu : IsAutomorphicClass ν u)
    (hv : IsAutomorphicClass ν v) :
    IsAutomorphicClass ν (u + v) := by
  intro a
  rw [pullback_add, hu a, hv a]
  refine AEEqFun.induction_on₂ (factorClass ν a) u ?_
  intro f hf g hg
  refine AEEqFun.induction_on v ?_
  intro k hk
  simp only [AEEqFun.mk_add_mk, AEEqFun.mk_mul_mk,
    AEEqFun.mk_eq_mk]
  filter_upwards with x
  ring
""",
        "Mock2 Advanced prove additive automorphy on measurable representatives",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """  filter_upwards [hcentral] with τ hτ
  suffices hzero : u τ = (0 : ℂ) by
    simpa using hzero
  have hfixed :
""",
        """  have hz :
      ((0 : Section) : UpperHalfPlane → ℂ) =ᵐ[hyperbolicMeasure] 0 :=
    AEEqFun.coeFn_zero
  filter_upwards [hcentral, hz] with τ hτ hzτ
  rw [hzτ]
  have hfixed :
""",
        "Mock2 Advanced rewrite the quotient zero representative explicitly",
        expected=2,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  simpa only [energyForm, inner_self_eq_norm_sq] using Q.graph_norm_sq u
""",
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  simpa [energyForm, inner_self_eq_norm_sq] using Q.graph_norm_sq u
""",
        "FunctionalAnalysis simplify the real part of the inner self norm square",
    )
    fa = replace_exact(
        fa,
        """    rw [energyForm, hgraph, inner_zero]
""",
        """    simp [energyForm, hgraph]
""",
        "FunctionalAnalysis use current simp lemmas for the zero inner product",
    )
    fa = replace_exact(
        fa,
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  rw [inner_self_eq_norm_sq]
  positivity
""",
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
  simpa [inner_self_eq_norm_sq] using hsq
""",
        "FunctionalAnalysis derive positive real inner self from the positive norm square",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
