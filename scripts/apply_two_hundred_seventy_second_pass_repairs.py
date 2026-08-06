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
        """  refine AEEqFun.induction_on (factorClass ν a) ?_
  intro f hf
  simp [AEEqFun.zero_def]
""",
        """  refine AEEqFun.induction_on (factorClass ν a) ?_
  intro f hf
  simp only [AEEqFun.zero_def, AEEqFun.mk_mul_mk, AEEqFun.mk_eq_mk]
  filter_upwards with x
  simp
""",
        "Mock2 Advanced prove zero automorphy pointwise on representatives",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """  simp only [AEEqFun.mk_add_mk, AEEqFun.mk_mul_mk,
    AEEqFun.mk_eq_mk]
  filter_upwards with x
  ring
""",
        """  simp only [AEEqFun.mk_add_mk, AEEqFun.mk_mul_mk,
    AEEqFun.mk_eq_mk]
  filter_upwards with x
  change f x * g x + f x * k x = f x * (g x + k x)
  ring
""",
        "Mock2 Advanced expose representative values before distributivity",
        expected=2,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  simpa [energyForm, inner_self_eq_norm_sq] using Q.graph_norm_sq u
""",
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  rw [energyForm, inner_self_eq_norm_sq]
  norm_num
  exact Q.graph_norm_sq u
""",
        "FunctionalAnalysis normalize the real part of the complex norm square",
    )
    fa = replace_exact(
        fa,
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
  simpa [inner_self_eq_norm_sq] using hsq
""",
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  rw [inner_self_eq_norm_sq]
  norm_num
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)
""",
        "FunctionalAnalysis normalize positivity of the complex norm square",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
