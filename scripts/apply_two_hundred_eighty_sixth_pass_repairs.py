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
        """  sheaf : QGaugePresheaf (Opens X)
  isSheaf : IsSheafLike (QGaugePresheaf.toPresheafLike sheaf)
""",
        """  sheaf : QGaugePresheaf.{u, v} (Opens X)
  isSheaf : IsSheafLike (QGaugePresheaf.toPresheafLike sheaf)
""",
        "Mock2 fix the field universe of standalone ShP",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
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
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  · simp [pairAction, integralFirstColumn,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
""",
        "Mock2 Advanced evaluate the first column of a two-by-two product",
    )
    m2a = replace_exact(
        m2a,
        """def partialSum (f : ℕ → E) (N : ℕ) : E :=
  ∑ n ∈ Finset.range N, f n
""",
        """def partialSum (f : ℕ → E) (N : ℕ) : E :=
  ∑ n in Finset.range N, f n
""",
        "Mock2 Advanced use the canonical Finset range sum notation",
    )
    m2a = replace_exact(
        m2a,
        """theorem partialSum_tendsto_tsum {f : ℕ → E} (hf : Summable f) :
    Tendsto (partialSum f) atTop (𝓝 (∑' n, f n)) := by
  simpa only [partialSum] using hf.hasSum.tendsto_sum_nat
""",
        """theorem partialSum_tendsto_tsum {f : ℕ → E} (hf : Summable f) :
    Tendsto (partialSum f) atTop (𝓝 (∑' n, f n)) := by
  change Tendsto (fun N => ∑ n in Finset.range N, f n)
    atTop (𝓝 (∑' n, f n))
  exact hf.hasSum.tendsto_sum_nat
""",
        "Mock2 Advanced state the finite partial sums in the form returned by HasSum",
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
  have h :
      Tendsto (fun N => (∑' n, f n) - partialSum f N) atTop
        (𝓝 ((∑' n, f n) - (∑' n, f n))) :=
    tendsto_const_nhds.sub (partialSum_tendsto_tsum hf)
  simpa only [sub_self] using h
""",
        "Mock2 Advanced fix the constant in the vanishing remainder limit",
    )
    inner_patterns = [
        ("⟨x, y⟩_ℂ", "⟪x, y⟫_ℂ", 1),
        ("⟨A u, v⟩_ℂ", "⟪A u, v⟫_ℂ", 6),
        ("⟨A u, u⟩_ℂ", "⟪A u, u⟫_ℂ", 8),
        ("⟨A u, v⟩_ℝ", "⟪A u, v⟫_ℝ", 2),
        ("⟨laxMilgramEquiv A hc hA u, v⟩_ℝ",
         "⟪laxMilgramEquiv A hc hA u, v⟫_ℝ", 3),
        ("⟨laxMilgramEquiv A hc hA u, u⟩_ℝ",
         "⟪laxMilgramEquiv A hc hA u, u⟫_ℝ", 1),
        ("⟨e u, v⟩_ℝ", "⟪e u, v⟫_ℝ", 1),
    ]
    for old, new, expected in inner_patterns:
        m2a = replace_exact(
            m2a, old, new,
            f"Mock2 Advanced update inner-product notation {old}",
            expected=expected,
        )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.baseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_baseExtension_le x
""",
        """theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 := by
  apply Q.baseExtension.opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using Q.norm_baseExtension_le x
""",
        "FunctionalAnalysis use the canonical completion norm instance for the base map",
    )
    fa = replace_exact(
        fa,
        """theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_raiseExtension_le x
""",
        """theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 := by
  apply Q.raiseExtension.opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using Q.norm_raiseExtension_le x
""",
        "FunctionalAnalysis use the canonical completion norm instance for the raised map",
    )
    fa = replace_exact(
        fa,
        """theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_lowerExtension_le x
""",
        """theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 := by
  apply Q.lowerExtension.opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using Q.norm_lowerExtension_le x
""",
        "FunctionalAnalysis use the canonical completion norm instance for the lowered map",
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
  (innerSLFlip ℂ :
    Q.SobolevCompletion →L[ℂ] StrongAntiDual Q.SobolevCompletion)
""",
        "FunctionalAnalysis pin the completion energy operator to its declared anti-dual type",
    )
    fa = replace_exact(
        fa,
        """@[simp]
theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ :=
  innerSLFlip_apply_apply ℂ u v
""",
        """@[simp]
theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ := by
  simpa [completionEnergyOperator] using
    (innerSLFlip_apply_apply ℂ u v)
""",
        "FunctionalAnalysis expose the pinned completion energy operator",
    )
    fa = replace_exact(
        fa,
        """  rw [Q.completionEnergyOperator_apply]
  change ⟪Q.coreEmbedding (Q.toGraphRange v),
      Q.coreEmbedding (Q.toGraphRange u)⟫_ℂ = Q.energyForm v u
  rw [Q.coreEmbedding.inner_map_map, Q.inner_toGraphRange]
""",
        """  rw [Q.completionEnergyOperator_apply]
  change ⟪Q.coreEmbedding (Q.toGraphRange v),
      Q.coreEmbedding (Q.toGraphRange u)⟫_ℂ = Q.energyForm v u
  calc
    ⟪Q.coreEmbedding (Q.toGraphRange v),
        Q.coreEmbedding (Q.toGraphRange u)⟫_ℂ =
        ⟪Q.toGraphRange v, Q.toGraphRange u⟫_ℂ := by
      exact Q.coreEmbedding.inner_map_map _ _
    _ = Q.energyForm v u := Q.inner_toGraphRange v u
""",
        "FunctionalAnalysis prove core energy compatibility in two explicit steps",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
