from __future__ import annotations

from pathlib import Path
import re

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
        """theorem denseRange_positiveRangeToClosedL2
    (ν : GenuineHalfWeightAutomorphy.Multiplier) :
    DenseRange (positiveRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (positiveL2Range ν).le_topologicalClosure)
  simpa [-SetLike.coe_sort_coe]
""",
        """theorem denseRange_positiveRangeToClosedL2
    (ν : GenuineHalfWeightAutomorphy.Multiplier) :
    DenseRange (positiveRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (positiveL2Range ν).le_topologicalClosure)
  rw [denseRange_inclusion_iff]
  · intro x hx
    exact hx
  · intro x hx
    exact (positiveL2Range ν).le_topologicalClosure hx
""",
        "Mock2 Advanced positive range density",
    )
    m2a = replace_exact(
        m2a,
        """theorem denseRange_inverseRangeToClosedL2
    (ν : GenuineInverseHalfWeightAutomorphy.Multiplier) :
    DenseRange (inverseRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (inverseL2Range ν).le_topologicalClosure)
  simpa [-SetLike.coe_sort_coe]
""",
        """theorem denseRange_inverseRangeToClosedL2
    (ν : GenuineInverseHalfWeightAutomorphy.Multiplier) :
    DenseRange (inverseRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (inverseL2Range ν).le_topologicalClosure)
  rw [denseRange_inclusion_iff]
  · intro x hx
    exact hx
  · intro x hx
    exact (inverseL2Range ν).le_topologicalClosure hx
""",
        "Mock2 Advanced inverse range density",
    )
    m2a = replace_exact(
        m2a,
        """  apply Prod.ext
  · simp [pairAction, integralFirstColumn,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two]
  · simp [pairAction, integralFirstColumn,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two]
""",
        """  apply Prod.ext
  · simp [pairAction, integralFirstColumn,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [pairAction, integralFirstColumn,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
""",
        "Mock2 Advanced first-column matrix multiplication",
    )
    m2a = replace_exact(
        m2a,
        """theorem partialSum_tendsto_tsum {f : ℕ → E} (hf : Summable f) :
    Tendsto (partialSum f) atTop (𝓝 (∑' n, f n)) := by
  simpa only [partialSum] using hf.hasSum.tendsto_sum_nat
""",
        """theorem partialSum_tendsto_tsum {f : ℕ → E} (hf : Summable f) :
    Tendsto (partialSum f) atTop (𝓝 (∑' n, f n)) := by
  change Tendsto (fun N => ∑ n ∈ Finset.range N, f n)
    atTop (𝓝 (∑' n, f n))
  exact hf.hasSum.tendsto_sum_nat
""",
        "Mock2 Advanced partial sums tend to the tsum",
    )
    m2a = replace_exact(
        m2a,
        """theorem tsum_sub_partialSum_tendsto_zero
    {f : ℕ → E} (hf : Summable f) :
    Tendsto (fun N => (∑' n, f n) - partialSum f N)
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    (tendsto_const_nhds.sub (partialSum_tendsto_tsum hf))
""",
        """theorem tsum_sub_partialSum_tendsto_zero
    {f : ℕ → E} (hf : Summable f) :
    Tendsto (fun N => (∑' n, f n) - partialSum f N)
      atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => ∑' n, f n)
      atTop (𝓝 (∑' n, f n)) := tendsto_const_nhds
  simpa only [sub_self] using
    hconst.sub (partialSum_tendsto_tsum hf)
""",
        "Mock2 Advanced series remainder tends to zero",
    )
    m2a, count = re.subn(r"⟨([^\n]*?)⟩_([ℂℝ])", r"⟪\1⟫_\2", m2a)
    if count != 22:
        raise RuntimeError(
            f"Mock2 Advanced inner-product notation: expected 22 matches, found {count}"
        )
    print(f"Mock2 Advanced inner-product notation: applied {count}")
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """/-- The Definition 1 Sobolev space: completion of the genuine energy graph. -/
abbrev SobolevCompletion :=
  UniformSpace.Completion Q.GraphRange

/-- Canonical isometric embedding of the graph core into its completion. -/
""",
        """/-- The Definition 1 Sobolev space: completion of the genuine energy graph. -/
abbrev SobolevCompletion :=
  UniformSpace.Completion Q.GraphRange

/-- Keep one coherent scalar and inner-product structure on the completion for
all subsequent bundled maps. -/
noncomputable local instance sobolevCompletionNormedSpace :
    NormedSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange

noncomputable local instance sobolevCompletionInnerProductSpace :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.innerProductSpace

/-- Canonical isometric embedding of the graph core into its completion. -/
""",
        "FunctionalAnalysis coherent completion instances",
    )
    for name in ("base", "raise", "lower"):
        fa = replace_exact(
            fa,
            f"""theorem norm_{name}Extension_le_one : ‖Q.{name}Extension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.{name}Extension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_{name}Extension_le x
""",
            f"""theorem norm_{name}Extension_le_one : ‖Q.{name}Extension‖ ≤ 1 := by
  exact Q.{name}Extension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_{name}Extension_le x
""",
            f"FunctionalAnalysis {name} extension operator norm",
        )
    fa = replace_exact(
        fa,
        """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact innerSLFlip ℂ
""",
        """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion :=
  innerSLFlip ℂ
""",
        "FunctionalAnalysis completion energy operator",
    )
    fa = replace_exact(
        fa,
        """@[simp]
theorem completionEnergyEquiv_apply (u : Q.SobolevCompletion) :
    Q.completionEnergyEquiv u = Q.completionEnergyOperator u :=
  rfl
""",
        """@[simp]
theorem completionEnergyEquiv_apply (u : Q.SobolevCompletion) :
    Q.completionEnergyEquiv u = Q.completionEnergyOperator u :=
  FredholmBypass.coerciveFormEquiv_apply
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive u
""",
        "FunctionalAnalysis completion energy equivalence application",
    )
    fa = replace_exact(
        fa,
        """theorem completionEnergyOperator_solveCompletionEnergy
    (F : StrongAntiDual Q.SobolevCompletion) :
    Q.completionEnergyOperator (Q.solveCompletionEnergy F) = F := by
  change Q.completionEnergyEquiv
    (Q.completionEnergyEquiv.symm F) = F
  exact Q.completionEnergyEquiv.apply_symm_apply F
""",
        """theorem completionEnergyOperator_solveCompletionEnergy
    (F : StrongAntiDual Q.SobolevCompletion) :
    Q.completionEnergyOperator (Q.solveCompletionEnergy F) = F := by
  rw [← Q.completionEnergyEquiv_apply]
  exact Q.completionEnergyEquiv.apply_symm_apply F
""",
        "FunctionalAnalysis solved completion energy equation",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
