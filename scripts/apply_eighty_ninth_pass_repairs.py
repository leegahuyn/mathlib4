from __future__ import annotations

from pathlib import Path

import apply_eighty_seventh_pass_repairs as pass87
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """      (AdvancedClaimsIIRlfFormulaProjectionCertificate.coeff_eq_object_at
        reference_advanced_claims_ii_rlf_formula_projection n)
""",
            """      (reference_advanced_claims_ii_rlf_coeff_eq_object_at n)
""",
            "Mock1Advanced use the existing coefficient-to-object projection",
        ),
        (
            """      (AdvancedClaimsIIRlfFormulaProjectionCertificate.coefficientAt_eq_object_at
        reference_advanced_claims_ii_rlf_formula_projection n)
""",
            """      (reference_advanced_claims_ii_rlf_coefficientAt_eq_object_at n)
""",
            "Mock1Advanced use the existing coefficientAt-to-object projection",
        ),
        (
            """def AdvancedClaimsIIPaperI2MahlerEval (n : Nat) : Int :=
  Finset.sum Finset.univ
    (fun j : Fin 6 =>
      AdvancedClaimsIIPaperI2MahlerCoefficient j *
        mahlerBinomialBasis (j : Nat) n)
""",
            """def AdvancedClaimsIIPaperI2MahlerEval (n : Nat) : Int :=
  (Finset.sum Finset.univ
    (fun j : Fin 6 =>
      AdvancedClaimsIIPaperI2MahlerCoefficient j *
        mahlerBinomialBasis (j : Nat) n)) %
    (PrimePower AdvancedClaimsIIPaperI2Prime
      AdvancedClaimsIIPaperI2Precision : Int)
""",
            "Mock1Advanced evaluate the finite Mahler table modulo p to the k",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    start = text.index("Paper Item I.2 concrete finite p-adic data.")
    end = text.index("\n/-!", start + 50)
    block = text[start:end]
    count = block.count("native_decide")
    if count == 12:
        block = block.replace("native_decide", "decide")
        text = text[:start] + block + text[end:]
        changed = True
        print("Mock1Advanced replace twelve native decisions by kernel decisions: applied 12")
    elif count == 0 and block.count("decide") >= 12:
        print("Mock1Advanced replace twelve native decisions by kernel decisions: already applied")
    else:
        raise RuntimeError(
            f"Mock1Advanced expected twelve native decisions in paper I.2, found {count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  funext i
  apply ChartForm.ext <;>
    simp [matrixVectorWedge, matrixWedge, Fin.sum_univ_two,
      wedge_add_left, wedge_add_right] <;> abel_nf
""",
        """  funext i
  apply ChartForm.ext <;>
    simp [matrixVectorWedge, matrixWedge, Fin.sum_univ_two,
      wedge_add_left, wedge_add_right] <;> ring
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

    weighted_start = text.index("namespace GenuineWeightedSobolev")
    weighted_end = text.index("end GenuineWeightedSobolev", weighted_start)
    weighted = text[weighted_start:weighted_end]
    old = """        exact (M.core_equivariant v hv).isAE μ)
"""
    new = """        exact (M.core_equivariant v hv).isAE)
"""
    count = weighted.count(old)
    if count == 1:
        weighted = weighted.replace(old, new, 1)
        text = text[:weighted_start] + weighted + text[weighted_end:]
        changed = True
        print("Mock2Advanced keep the half-weight measure implicit: applied 1")
    elif count == 0 and new in weighted:
        print("Mock2Advanced keep the half-weight measure implicit: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced expected one half-weight isAE call, found {count}"
        )

    replacements = [
        (
            """      rw [hrem]
      ring
""",
            """      rw [hrem]
      unfold abelRemainder
      ring
""",
            "Mock2Advanced expose the final Abel remainder before ring normalization",
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
            """theorem gammaTwoToSL2Real_isClosedEmbedding :
    Topology.IsClosedEmbedding gammaTwoToSL2Real := by
  convert
    (Matrix.SpecialLinearGroup.isClosedEmbedding_mapGLInt
      (n := Fin 2)).comp
      ((isClosed_discrete (GammaTwo : Set SL(2, ℤ))).isClosedEmbedding_subtypeVal)
    using 1 <;> rfl
""",
            """theorem gammaTwoToSL2Real_isClosedEmbedding :
    Topology.IsClosedEmbedding gammaTwoToSL2Real := by
  change Topology.IsClosedEmbedding
    (fun γ : GammaTwo =>
      Matrix.SpecialLinearGroup.map (algebraMap ℤ ℝ) (γ : SL(2, ℤ)))
  exact
    Real.isClosedEmbedding_intCast.specialLinearGroup_map.comp
      ((isClosed_discrete (GammaTwo : Set SL(2, ℤ))).isClosedEmbedding_subtypeVal)
""",
            "FunctionalAnalysis compose the two closed SL embeddings directly",
        ),
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
    pass87.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
