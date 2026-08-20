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
        """theorem pullback_add (a : Element) (u v : Section) :
    pullback a (u + v) = pullback a u + pullback a v := by
  refine AEEqFun.induction_on₂ u v ?_
  intro f hf g hg
  simp [pullback, Function.comp_def]
""",
        """theorem pullback_add (a : Element) (u v : Section) :
    pullback a (u + v) = pullback a u + pullback a v := by
  refine AEEqFun.induction_on₂ u v ?_
  intro f hf g hg
  simp [pullback, Function.comp_def]
  filter_upwards with x
  rfl
""",
        "Mock2 Advanced close pullback additivity pointwise",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """theorem pullback_smul (a : Element) (c : ℂ) (u : Section) :
    pullback a (c • u) = c • pullback a u := by
  refine AEEqFun.induction_on u ?_
  intro f hf
  simp [pullback, Function.comp_def]
""",
        """theorem pullback_smul (a : Element) (c : ℂ) (u : Section) :
    pullback a (c • u) = c • pullback a u := by
  refine AEEqFun.induction_on u ?_
  intro f hf
  simp [pullback, Function.comp_def]
  filter_upwards with x
  rfl
""",
        "Mock2 Advanced close pullback scalar compatibility pointwise",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """@[simp]
theorem isAutomorphicClass_zero (ν : Multiplier) :
    IsAutomorphicClass ν (0 : Section) := by
  intro a
  rw [pullback_zero, mul_zero]
""",
        """@[simp]
theorem isAutomorphicClass_zero (ν : Multiplier) :
    IsAutomorphicClass ν (0 : Section) := by
  intro a
  rw [pullback_zero]
  exact (mul_zero (factorClass ν a)).symm
""",
        "Mock2 Advanced orient the zero automorphy equation explicitly",
        expected=2,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  map_add' u v := by
    simpa only [map_add, WithLp.toLp_add]
  map_smul' c u := by
    simpa only [map_smul, WithLp.toLp_smul]
""",
        """  map_add' u v := by
    change WithLp.toLp 2
      (Q.base u + Q.base v,
        WithLp.toLp 2 (Q.raised u + Q.raised v, Q.lowered u + Q.lowered v)) =
      WithLp.toLp 2 (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u)) +
        WithLp.toLp 2 (Q.base v, WithLp.toLp 2 (Q.raised v, Q.lowered v))
    rw [← WithLp.toLp_add]
    congr 1
    exact WithLp.toLp_add _ _
  map_smul' c u := by
    change WithLp.toLp 2
      (c • Q.base u, WithLp.toLp 2 (c • Q.raised u, c • Q.lowered u)) =
      c • WithLp.toLp 2 (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u))
    rw [← WithLp.toLp_smul]
    congr 1
    exact WithLp.toLp_smul _ _
""",
        "FunctionalAnalysis apply outer and inner WithLp linearity explicitly",
    )
    fa = replace_exact(
        fa,
        """theorem energyForm_apply (u v : V) :
    Q.energyForm u v =
      ⟪Q.base u, Q.base v⟫_ℂ +
      ⟪Q.raised u, Q.raised v⟫_ℂ +
      ⟪Q.lowered u, Q.lowered v⟫_ℂ := by
  simp only [energyForm, graph, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, add_assoc]
""",
        """theorem energyForm_apply (u v : V) :
    Q.energyForm u v =
      ⟪Q.base u, Q.base v⟫_ℂ +
      ⟪Q.raised u, Q.raised v⟫_ℂ +
      ⟪Q.lowered u, Q.lowered v⟫_ℂ := by
  unfold energyForm
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  rfl
""",
        "FunctionalAnalysis expose both product inner coordinates definitionally",
    )
    fa = replace_exact(
        fa,
        """theorem graph_norm_sq (u : V) :
    ‖Q.graph u‖ ^ 2 =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2 (Q.graph u),
    WithLp.prod_norm_sq_eq_of_L2 (Q.graph u).snd]
  simp only [graph, WithLp.ofLp_toLp]
  ring
""",
        """theorem graph_norm_sq (u : V) :
    ‖Q.graph u‖ ^ 2 =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2 (Q.graph u),
    WithLp.prod_norm_sq_eq_of_L2 (Q.graph u).snd]
  change
    ‖Q.base u‖ ^ 2 + (‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2) =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2
  ring
""",
        "FunctionalAnalysis expose graph norm coordinates definitionally",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
