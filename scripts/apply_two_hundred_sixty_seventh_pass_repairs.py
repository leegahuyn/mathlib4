from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
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
        """  rw [PolynomialMatrixDifferentialForms.matrixDifferential_zero]
  simp [PolynomialMatrixDifferentialForms.matrixWedge, Fin.sum_univ_two]
""",
        """  rw [PolynomialMatrixDifferentialForms.matrixDifferential_zero]
  apply Matrix.ext
  intro i j
  apply PolynomialMatrixDifferentialForms.ChartForm.ext <;>
    simp [PolynomialMatrixDifferentialForms.matrixWedge, Fin.sum_univ_two]
""",
        "Mock2 prove the remaining zero matrix wedge coefficientwise",
    )
    m2 = replace_exact(
        m2,
        """/-! ### Categorical equalizer universal property in `Type` -/
""",
        """/-! ### Categorical equalizer universal property in `Type` -/

/-- Underlying Type-valued morphism of the left overlap map. -/
def equation613LeftType : LocalFamily C ⟶ OverlapFamily C :=
  fun s => equation613Left C s

/-- Underlying Type-valued morphism of the right overlap map. -/
def equation613RightType : LocalFamily C ⟶ OverlapFamily C :=
  fun s => equation613Right C s
""",
        "Mock2 expose the equation-6.13 additive maps as Type morphisms",
    )
    m2 = replace_exact(
        m2,
        "(equation613Left C : LocalFamily C ⟶ OverlapFamily C)",
        "equation613LeftType C",
        "Mock2 use the underlying left Type morphism throughout the equalizer",
        expected=14,
    )
    m2 = replace_exact(
        m2,
        "(equation613Right C : LocalFamily C ⟶ OverlapFamily C)",
        "equation613RightType C",
        "Mock2 use the underlying right Type morphism throughout the equalizer",
        expected=14,
    )
    M2.write_text(m2, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  map_add' u v := by
    simp only [map_add]
    change WithLp.toLp 2
      ((Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u)) +
        (Q.base v, WithLp.toLp 2 (Q.raised v, Q.lowered v))) =
      WithLp.toLp 2 (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u)) +
        WithLp.toLp 2 (Q.base v, WithLp.toLp 2 (Q.raised v, Q.lowered v))
    exact WithLp.toLp_add _ _
  map_smul' c u := by
    simp only [map_smul, RingHom.id_apply]
    change WithLp.toLp 2
      (c • (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u))) =
      c • WithLp.toLp 2 (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u))
    exact WithLp.toLp_smul _ _
""",
        """  map_add' u v := by
    simpa only [map_add, WithLp.toLp_add]
  map_smul' c u := by
    simpa only [map_smul, RingHom.id_apply, WithLp.toLp_smul]
""",
        "FunctionalAnalysis let the expected graph type determine WithLp instances",
    )
    fa = replace_exact(
        fa,
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  rw [energyForm, inner_self_eq_norm_sq]
  exact Q.graph_norm_sq u
""",
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  simpa only [energyForm, inner_self_eq_norm_sq] using Q.graph_norm_sq u
""",
        "FunctionalAnalysis transport the graph norm square into the real energy form",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
