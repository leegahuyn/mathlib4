from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
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
        "FunctionalAnalysis normalize the three coordinate maps before WithLp linearity",
    )
    fa = replace_exact(
        fa,
        """theorem energyForm_apply (u v : V) :
    Q.energyForm u v =
      ⟪Q.base u, Q.base v⟫_ℂ +
      ⟪Q.raised u, Q.raised v⟫_ℂ +
      ⟪Q.lowered u, Q.lowered v⟫_ℂ := by
  unfold energyForm
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  rfl
""",
        """theorem energyForm_apply (u v : V) :
    Q.energyForm u v =
      ⟪Q.base u, Q.base v⟫_ℂ +
      ⟪Q.raised u, Q.raised v⟫_ℂ +
      ⟪Q.lowered u, Q.lowered v⟫_ℂ := by
  unfold energyForm
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change
    ⟪Q.base u, Q.base v⟫_ℂ +
        (⟪Q.raised u, Q.raised v⟫_ℂ +
          ⟪Q.lowered u, Q.lowered v⟫_ℂ) =
      ⟪Q.base u, Q.base v⟫_ℂ +
        ⟪Q.raised u, Q.raised v⟫_ℂ +
          ⟪Q.lowered u, Q.lowered v⟫_ℂ
  exact (add_assoc _ _ _).symm
""",
        "FunctionalAnalysis finish the product inner expansion by associativity",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
