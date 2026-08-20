from __future__ import annotations

from pathlib import Path

import apply_seventy_eighth_pass_repairs as pass78
import apply_seventy_ninth_pass_repairs as pass79
import apply_eightieth_pass_repairs as pass80
import apply_eighty_second_pass_repairs as pass82
import apply_seventy_fifth_pass_repairs as pass75
import apply_seventy_third_pass_repairs as pass73
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    pass82.repair_mock1_advanced()
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
    pass82.repair_mock2()
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("theorem potential_action_assoc")
    end = text.index("\n\n/-- Paper equation", start)
    old = text[start:end]
    new = """theorem potential_action_assoc (C : Core U) (s : LocalFramedSection U) :
    matrixVectorWedge C.potential (matrixVectorWedge C.potential s) =
      matrixVectorWedge (matrixWedge C.potential C.potential) s := by
  funext i
  apply ChartForm.ext <;>
    simp [matrixVectorWedge, matrixWedge, Fin.sum_univ_two,
      wedge_add_left, wedge_add_right] <;> ring"""
    if old != new:
        text = text[:start] + new + text[end:]
        changed = True
        print("Mock2 replace matrix-action associativity proof by ring normalization: applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    pass80.repair_mock2_advanced()
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]
    old = "exact (M.core_equivariant v hv).isAE)"
    new = "exact (M.core_equivariant v hv).isAE μ)"
    count = block.count(old)
    if count == 1:
        block = block.replace(old, new, 1)
        text = text[:start] + block + text[end:]
        changed = True
        print("Mock2Advanced supply μ in the inverse-half-weight Sobolev block: applied 1")
    elif count == 0 and new in block:
        print("Mock2Advanced supply μ in the inverse-half-weight Sobolev block: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced expected one inverse-half-weight isAE projection, found {count}"
        )

    replacements = [
        (
            """  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      simp only [abelRemainder] at ih ⊢
      ring
""",
            """  | succ N ih =>
      unfold abelRemainder at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      abel
""",
            "Mock2Advanced normalize finite Abel summation additively",
        ),
        (
            """theorem pSeriesMajorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (pSeriesMajorant δ) := by
  simpa only [pSeriesMajorant] using
    (Real.summable_one_div_nat_add_rpow 1 (1 + δ)).2 (by linarith)
""",
            """theorem pSeriesMajorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (pSeriesMajorant δ) := by
  change Summable (fun n : ℕ =>
    1 / |(n : ℝ) + 1| ^ (1 + δ))
  exact (Real.summable_one_div_nat_add_rpow 1 (1 + δ)).2 (by linarith)
""",
            "Mock2Advanced expose the p-series majorant before convergence",
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
    pass79.repair_functional_analysis()
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("theorem inverseEtaRawFactor_mul")
    end = text.index("\n\n/-- Integer powers of the raw inverse-eta factor", start)
    old = text[start:end]
    new = """theorem inverseEtaRawFactor_mul (γ δ : SL(2, ℤ)) (z : ℍ) :
    inverseEtaRawFactor (γ * δ) z =
      inverseEtaRawFactor γ (δ • z) * inverseEtaRawFactor δ z := by
  rw [inverseEtaRawFactor_eq, inverseEtaRawFactor_eq,
    inverseEtaRawFactor_eq, mul_smul]
  simp only [div_eq_mul_inv]
  calc
    ModularForm.eta ↑z * (ModularForm.eta ↑(γ • δ • z))⁻¹ =
        (ModularForm.eta ↑(δ • z) *
          (ModularForm.eta ↑(δ • z))⁻¹) *
            (ModularForm.eta ↑z *
              (ModularForm.eta ↑(γ • δ • z))⁻¹) := by
      rw [mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), one_mul]
    _ =
        (ModularForm.eta ↑(δ • z) *
          (ModularForm.eta ↑(γ • δ • z))⁻¹) *
            (ModularForm.eta ↑z *
              (ModularForm.eta ↑(δ • z))⁻¹) := by ring"""
    if old != new:
        text = text[:start] + new + text[end:]
        changed = True
        print("FunctionalAnalysis install the compiled inverse-eta cocycle proof: applied")

    vertical_start = text.index("theorem complex_verticalLine_null")
    vertical_end = text.index(
        "\n\n/-- The part of the closed modular tile", vertical_start)
    vertical = text[vertical_start:vertical_end]
    vertical_replacements = [
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
    ]
    for old_text, new_text, label in vertical_replacements:
        count = vertical.count(old_text)
        if count == 1:
            vertical = vertical.replace(old_text, new_text, 1)
            changed = True
            print(f"{label}: applied 1")
        elif count == 0 and new_text in vertical:
            print(f"{label}: already applied")
        else:
            raise RuntimeError(f"{label}: expected one match in vertical-line theorem, found {count}")
    text = text[:vertical_start] + vertical + text[vertical_end:]

    text, did = replace_exact(
        text,
        """  rw [CongruenceSubgroup.Gamma_mem]
  norm_num
""",
        """  rw [CongruenceSubgroup.Gamma_mem]
  decide
""",
        1,
        "FunctionalAnalysis decide minus-identity membership modulo two",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass78.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
