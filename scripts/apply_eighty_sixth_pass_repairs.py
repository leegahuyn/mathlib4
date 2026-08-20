from __future__ import annotations

from pathlib import Path

import apply_eighty_fifth_pass_repairs as pass85
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  funext i
  apply ChartForm.ext <;>
    simp [matrixVectorWedge, matrixWedge, Fin.sum_univ_two,
      wedge_add_left, wedge_add_right, wedge_assoc] <;> abel
""",
        """  funext i
  apply ChartForm.ext <;>
    simp [matrixVectorWedge, matrixWedge, Fin.sum_univ_two,
      wedge_add_left, wedge_add_right, wedge_assoc] <;> ring
""",
        1,
        "Mock2 normalize polynomial matrix-action associativity with ring",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]
    old = "exact (M.core_equivariant v hv).isAE μ)"
    new = "exact (M.core_equivariant v hv).isAE)"
    count = block.count(old)
    if count == 1:
        block = block.replace(old, new, 1)
        text = text[:start] + block + text[end:]
        changed = True
        print("Mock2Advanced restore implicit measure in half-weight isAE: applied 1")
    elif count == 0 and new in block:
        print("Mock2Advanced restore implicit measure in half-weight isAE: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced expected one half-weight isAE call, found {count}"
        )

    replacements = [
        (
            """  | succ N ih =>
      unfold abelRemainder at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      ring
""",
            """  | succ N ih =>
      unfold abelRemainder at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      abel
""",
            "Mock2Advanced close finite Abel summation by additive normalization",
        ),
        (
            """theorem basic_window_beta_one {α : ℝ} :
    basicGrowth α 1 < 1 ↔ α < -(1 / 2 : ℝ) := by
  simp [basicGrowth]
  linarith
""",
            """theorem basic_window_beta_one {α : ℝ} :
    basicGrowth α 1 < 1 ↔ α < -(1 / 2 : ℝ) := by
  unfold basicGrowth
  constructor <;> intro h <;> linarith
""",
            "Mock2Advanced split the basic cusp-window equivalence",
        ),
        (
            """theorem rankinSelberg_window_beta_one {α σ : ℝ} :
    rankinSelbergGrowth α 1 σ < 1 ↔
      α + eisensteinGrowth σ < -(1 / 2 : ℝ) := by
  simp [rankinSelbergGrowth, basicGrowth]
  linarith
""",
            """theorem rankinSelberg_window_beta_one {α σ : ℝ} :
    rankinSelbergGrowth α 1 σ < 1 ↔
      α + eisensteinGrowth σ < -(1 / 2 : ℝ) := by
  unfold rankinSelbergGrowth basicGrowth
  constructor <;> intro h <;> linarith
""",
            "Mock2Advanced split the Rankin-Selberg cusp-window equivalence",
        ),
        (
            """  rw [integrableOn_Ioi_rpow_iff hY]
  linarith
""",
            """  rw [integrableOn_Ioi_rpow_iff hY]
  constructor <;> intro h <;> linarith
""",
            "Mock2Advanced split the power-tail integrability equivalence",
        ),
        (
            """  rw [setIntegral_prod _ h, setIntegral_const]
  simp [Gamma2Cusp.width_eq_two]
""",
            """  rw [setIntegral_prod _ h]
  change
    (∫ _x in Ioc 0 (Gamma2Cusp.width κ : ℝ),
      ∫ y in Ioi Y, cuspPowerDensity growth y) =
        (Gamma2Cusp.width κ : ℝ) *
          ∫ y in Ioi Y, cuspPowerDensity growth y
  rw [setIntegral_const]
  simp [Gamma2Cusp.width_eq_two]
""",
            "Mock2Advanced expose the constant outer cusp-strip integrand",
        ),
    ]
    for old_text, new_text, label in replacements:
        text, did = replace_exact(text, old_text, new_text, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    rw [volume_eq_prod, Measure.prod_prod]
    simp
""",
            """    change (volume.prod volume)
      (({a} : Set ℝ) ×ˢ Set.univ) = 0
    simp
""",
            "FunctionalAnalysis expose product Lebesgue measure on a vertical line",
        ),
        (
            """      (measurableSet_eq Complex.measurable_re measurable_const).nullMeasurableSet
""",
            """      (measurableSet_eq).nullMeasurableSet
""",
            "FunctionalAnalysis infer the measurable equality set from context",
        ),
        (
            """  rw [CongruenceSubgroup.Gamma_mem]
  norm_num
""",
            """  rw [CongruenceSubgroup.Gamma_mem]
  decide
""",
            "FunctionalAnalysis decide minus-identity membership modulo two",
        ),
    ]
    for old_text, new_text, label in replacements:
        text, did = replace_exact(text, old_text, new_text, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass85.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
