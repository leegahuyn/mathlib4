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
        """  map_add' u v := by simp
  map_smul' c u := by simp
""",
        """  map_add' u v := by
    simpa only [map_add, WithLp.toLp_add]
  map_smul' c u := by
    simpa only [map_smul, WithLp.toLp_smul]
""",
        "FunctionalAnalysis prove graph linearity through the WithLp transport lemmas",
    )
    fa = replace_exact(
        fa,
        """  simp only [energyForm, WithLp.prod_inner_apply, graph_fst,
    graph_snd_fst, graph_snd_snd, add_assoc]
""",
        """  simp only [energyForm, graph, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, add_assoc]
""",
        "FunctionalAnalysis expose graph coordinates before evaluating the product inner form",
    )
    fa = replace_exact(
        fa,
        """theorem energyForm_add_left (u v w : V) :
    Q.energyForm (u + v) w = Q.energyForm u w + Q.energyForm v w := by
  simp [energyForm]
""",
        """theorem energyForm_add_left (u v w : V) :
    Q.energyForm (u + v) w = Q.energyForm u w + Q.energyForm v w := by
  rw [Q.energyForm_apply, Q.energyForm_apply, Q.energyForm_apply]
  simp only [map_add, inner_add_left]
  ring
""",
        "FunctionalAnalysis prove energy additivity on the left coordinatewise",
    )
    fa = replace_exact(
        fa,
        """theorem energyForm_add_right (u v w : V) :
    Q.energyForm u (v + w) = Q.energyForm u v + Q.energyForm u w := by
  simp [energyForm]
""",
        """theorem energyForm_add_right (u v w : V) :
    Q.energyForm u (v + w) = Q.energyForm u v + Q.energyForm u w := by
  rw [Q.energyForm_apply, Q.energyForm_apply, Q.energyForm_apply]
  simp only [map_add, inner_add_right]
  ring
""",
        "FunctionalAnalysis prove energy additivity on the right coordinatewise",
    )
    fa = replace_exact(
        fa,
        """theorem energyForm_smul_left (c : ℂ) (u v : V) :
    Q.energyForm (c • u) v = conj c * Q.energyForm u v := by
  simp [energyForm]
""",
        """theorem energyForm_smul_left (c : ℂ) (u v : V) :
    Q.energyForm (c • u) v = conj c * Q.energyForm u v := by
  rw [Q.energyForm_apply, Q.energyForm_apply]
  simp only [map_smul, inner_smul_left]
  ring
""",
        "FunctionalAnalysis prove conjugate homogeneity on the left coordinatewise",
    )
    fa = replace_exact(
        fa,
        """theorem energyForm_smul_right (c : ℂ) (u v : V) :
    Q.energyForm u (c • v) = c * Q.energyForm u v := by
  simp [energyForm]
""",
        """theorem energyForm_smul_right (c : ℂ) (u v : V) :
    Q.energyForm u (c • v) = c * Q.energyForm u v := by
  rw [Q.energyForm_apply, Q.energyForm_apply]
  simp only [map_smul, inner_smul_right]
  ring
""",
        "FunctionalAnalysis prove homogeneity on the right coordinatewise",
    )
    fa = replace_exact(
        fa,
        """  rw [WithLp.prod_norm_sq_eq_of_L2 (Q.graph u),
    WithLp.prod_norm_sq_eq_of_L2 (Q.graph u).snd]
  ring
""",
        """  rw [WithLp.prod_norm_sq_eq_of_L2 (Q.graph u),
    WithLp.prod_norm_sq_eq_of_L2 (Q.graph u).snd]
  simp only [graph, WithLp.ofLp_toLp]
  ring
""",
        "FunctionalAnalysis expose graph coordinates in the L2 norm square",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
