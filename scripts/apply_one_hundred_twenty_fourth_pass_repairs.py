from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twenty_third_pass_repairs as pass123
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """  cases r <;>
    simp_all [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass] <;>
    decide
""",
            """  cases r <;>
    simp_all [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass] <;>
    simp only [List.mem_cons, true_or, or_true]
""",
            1,
            "Mock1Advanced prove direct enum membership without a DecidableEq instance",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    ring
""",
            """  map_smul' c x := by
    change
      c * (inverseEvalLinear A q x.2.2) +
          c * (evalLinear A q x.2.1) =
        (inverseEvalLinear A q x.2.2) * c +
          (evalLinear A q x.2.1) * c
    ring
""",
            1,
            "Mock2 expose product scalar multiplication in the homogeneous functional",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  have hnatL : Int.natAbs (L 1 1) = 1 := by
    nlinarith [hnatLsq]
  have hnatR : Int.natAbs (R 0 0) = 1 := by
    nlinarith [hnatRsq]
""",
            """  have hnatL : Int.natAbs (L 1 1) = 1 := by
    exact Nat.dvd_one.mp ⟨Int.natAbs (L 1 1), hnatLsq.symm⟩
  have hnatR : Int.natAbs (R 0 0) = 1 := by
    exact Nat.dvd_one.mp ⟨Int.natAbs (R 0 0), hnatRsq.symm⟩
""",
            1,
            "Mock2Advanced derive natural unit values from divisibility of one",
        ),
        (
            """  exact Eventually.of_forall fun t => by
    rw [hF m t, hρ κ m t]
""",
            """  exact Eventually.of_forall fun t => by
    simpa only using congrArg
      (fun a => a * Complex.normSq (R.cuspCoefficient κ m t)) (hF m t) |>.trans
        (congrArg
          (fun a => D.test t * Complex.normSq a) (hρ κ m t))
""",
            1,
            "Mock2Advanced transport both pointwise Rankin-Selberg identifications explicitly",
        ),
        (
            """  Mock2Adv.Interchange.sum_integral_interchange (B.integrable m)
    (B.summable_integral_norm m)
""",
            """  Interchange.sum_integral_interchange (B.integrable m)
    (B.summable_integral_norm m)
""",
            1,
            "Mock2Advanced call the sibling interchange namespace in the current corrected-lemmas scope",
        ),
        (
            """theorem kernel_integrable (m i : ℕ) :
    Integrable (kernel m i) (Measure.dirac (0 : ℝ)) := by
  exact integrable_dirac (by positivity)
""",
            """theorem kernel_integrable (m i : ℕ) :
    Integrable (kernel m i) (Measure.dirac (0 : ℝ)) := by
  exact integrable_dirac continuous_const.aestronglyMeasurable
""",
            1,
            "Mock2Advanced prove Dirac integrability from measurability of the constant kernel",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  exact isCompact_iUnion fun q ↦
    (ModularGroup.isCompact_truncatedFundamentalDomain
      (gammaTwoCuspLevel Y)).smul (gammaTwoCosetRep q)
""",
            """  exact isCompact_iUnion fun q ↦ by
    change IsCompact
      ((fun z : ℍ => gammaTwoCosetRep q • z) ''
        ModularGroup.truncatedFundamentalDomain (gammaTwoCuspLevel Y))
    exact
      (ModularGroup.isCompact_truncatedFundamentalDomain
        (gammaTwoCuspLevel Y)).image
          (HalfIntegralMultiplier.continuous_sl2z_smul (gammaTwoCosetRep q))
""",
            1,
            "FunctionalAnalysis prove compactness of a translated tile as a continuous image",
        ),
        (
            """      refine Set.mem_smul_set.mpr
        ⟨(gammaTwoCosetRep q)⁻¹ • z, ?_, by simp⟩
""",
            """      refine Set.mem_smul_set.mpr
        ⟨(gammaTwoCosetRep q)⁻¹ • z, ?_, by simp [q']⟩
""",
            1,
            "FunctionalAnalysis unfold the selected cusp representative in the cancellation witness",
        ),
        (
            """  have hzTileInterior :
      z ∈ interior (gammaTwoCosetRep q • ModularGroup.fd) := by
    rw [interior_smul]
    exact Set.mem_smul_set.mpr ⟨w, hwInterior, hEq⟩
""",
            """  have hzTileInterior :
      z ∈ interior (gammaTwoCosetRep q • ModularGroup.fd) := by
    let e : ℍ ≃ₜ ℍ :=
      { toEquiv :=
          { toFun := fun u => gammaTwoCosetRep q • u
            invFun := fun u => (gammaTwoCosetRep q)⁻¹ • u
            left_inv := by intro u; simp
            right_inv := by intro u; simp }
        continuous_toFun :=
          HalfIntegralMultiplier.continuous_sl2z_smul (gammaTwoCosetRep q)
        continuous_invFun :=
          HalfIntegralMultiplier.continuous_sl2z_smul (gammaTwoCosetRep q)⁻¹ }
    change z ∈ interior (e '' ModularGroup.fd)
    rw [← e.image_interior]
    exact ⟨w, hwInterior, hEq⟩
""",
            1,
            "FunctionalAnalysis transport tile interior through an explicit modular homeomorphism",
        ),
        (
            """    exact ((gammaTwoThreeCuspStrictHeightSublevel_isOpen Y).mem_nhds
      hzStrict).mono (gammaTwoThreeCuspStrictHeightSublevel_subset Y)
""",
            """    exact Filter.mem_of_superset
      ((gammaTwoThreeCuspStrictHeightSublevel_isOpen Y).mem_nhds hzStrict)
      (gammaTwoThreeCuspStrictHeightSublevel_subset Y)
""",
            1,
            "FunctionalAnalysis use filter monotonicity explicitly for the strict height neighborhood",
        ),
    ])


def main() -> int:
    pass123.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
