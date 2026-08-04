from __future__ import annotations

from pathlib import Path

import apply_eighty_fourth_pass_repairs as pass84
import apply_seventy_fifth_pass_repairs as pass75
import apply_seventy_third_pass_repairs as pass73
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    typ = pass75._forall(
        "n : Nat",
        pass75._ref_type(
            text,
            "EntropyReproRequirementPayloadCertificate",
            "degeneracy_at",
        ),
    )
    text, changed = pass73._replace_structure_field_type(
        text,
        "AdvancedClaimsIIFormulaLevelMergeAuditCertificate",
        "entropy_degeneracy",
        typ,
    )
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1Advanced type the merge-audit entropy degeneracy field: applied 1")
    else:
        print("Mock1Advanced type the merge-audit entropy degeneracy field: already applied")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    text, changed = replace_exact(
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
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

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
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
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
            """      (measurableSet_singleton.preimage
        Complex.measurable_re).nullMeasurableSet
""",
            "FunctionalAnalysis prove vertical-line measurability as a singleton preimage",
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
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass84.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
