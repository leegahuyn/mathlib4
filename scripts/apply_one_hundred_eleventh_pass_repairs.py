from __future__ import annotations

from pathlib import Path

import apply_one_hundred_tenth_pass_repairs as pass110
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
            """  cases hblock with
  | head => norm_num [referenceMock1MList, referenceMock1RPhases]
  | tail _ hblock =>
      cases hblock with
      | head => norm_num [referenceMock1MList, referenceMock1RPhases]
      | tail _ hblock =>
          cases hblock with
          | head => norm_num [referenceMock1MList, referenceMock1RPhases]
          | tail _ hnil => cases hnil
""",
            """  cases hblock with
  | head => simp [referenceMock1MList, referenceMock1RPhases,
      List.mem_cons, List.mem_singleton]
  | tail _ hblock =>
      cases hblock with
      | head => simp [referenceMock1MList, referenceMock1RPhases,
          List.mem_cons, List.mem_singleton]
      | tail _ hblock =>
          cases hblock with
          | head => simp [referenceMock1MList, referenceMock1RPhases,
              List.mem_cons, List.mem_singleton]
          | tail _ hnil => cases hnil
""",
            1,
            "Mock1Advanced close the three concrete block memberships by simplification",
        ),
        (
            """  cases r <;>
    simp [evidenceClass, finiteExactRequirements,
      analyticBoundaryRequirements, diagnosticMetadataRequirements,
      aggregateRequirements, all]
""",
            """  cases r <;>
    simp [evidenceClass, finiteExactRequirements,
      analyticBoundaryRequirements, diagnosticMetadataRequirements,
      aggregateRequirements, all, List.mem_cons, List.mem_singleton]
""",
            1,
            "Mock1Advanced reduce every evidence-class list membership",
        ),
        (
            """theorem advanced_claims_ii_ramanujan_f_paper_beta_excludes_legacy_slope :
    Not
      (referenceBetaInterval.Contains
        AdvancedClaimsIILegacyEntropyLogSlope) := by
  native_decide
""",
            """theorem advanced_claims_ii_ramanujan_f_paper_beta_excludes_legacy_slope :
    Not
      (referenceBetaInterval.Contains
        AdvancedClaimsIILegacyEntropyLogSlope) := by
  norm_num [RationalInterval.Contains, referenceBetaInterval,
    closedRatInterval, AdvancedClaimsIILegacyEntropyLogSlope]
""",
            1,
            "Mock1Advanced prove beta-interval exclusion by rational arithmetic",
        ),
    ])


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            "(presheaf K).res hUV s r",
            "((presheaf K).res hUV s).toFun r",
            1,
            "Mock2 evaluate the presheaf restriction through toFun",
        ),
        (
            "(actualBundle K).res hUV s r",
            "((actualBundle K).res hUV s).toFun r",
            24,
            "Mock2 evaluate twenty-four bundle restrictions through toFun",
        ),
        (
            "s ⟨r.1, hUV r.2⟩",
            "s.toFun ⟨r.1, hUV r.2⟩",
            5,
            "Mock2 evaluate five local sections through toFun",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    for theorem in ["locality", "gluing_exists", "gluing_unique", "existsUnique_gluing"]:
        old = f"theorem {theorem} (K : KernelData) {{ι : Type u}}"
        new = f"theorem {theorem} (K : KernelData) {{ι : Type}}"
        text, did = replace_exact(
            text, old, new, 1,
            f"Mock2 specialize {theorem} cover indices to the radius-base universe",
        )
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  rw [hzero]
  exact Filter.eventually_bot
""",
            """  rw [hzero]
  change ∀ᶠ t : ℝ in (⊥ : Filter ℝ),
    K.normalization t * K.kernel t x = (0 : ℂ)
  exact Filter.eventually_bot
""",
            1,
            "Mock2Advanced expose zero-measure AE equality as bottom-filter eventuality",
        ),
        (
            """  simp_rw only [Convention.scaleNormalization_normalizedKernel]
""",
            """  simp_rw [Convention.scaleNormalization_normalizedKernel]
""",
            1,
            "Mock2Advanced use valid simp_rw syntax for normalized kernels",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    typed_count = text.count("ContDiff ℝ (∞ : ℕ∞)")
    top_count = text.count("ContDiff ℝ ⊤")
    if typed_count == 16:
        text = text.replace("ContDiff ℝ (∞ : ℕ∞)", "ContDiff ℝ ⊤")
        changed = True
        print("Mock2Advanced express sixteen smoothness orders as top: applied 16")
    elif top_count >= 16:
        print("Mock2Advanced express sixteen smoothness orders as top: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced smoothness-order count unexpected: typed={typed_count}, top={top_count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """    _ = ⋃ q : GammaTwoRightCoset,
          closure (gammaTwoCosetRep q • ModularGroup.fdo) := by
            simp_rw [closure_smul]
""",
            """    _ = ⋃ q : GammaTwoRightCoset,
          closure (gammaTwoCosetRep q • ModularGroup.fdo) := by
            apply iUnion_congr
            intro q
            change
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
                  (gammaTwoCosetRep q)) • closure ModularGroup.fdo =
                closure
                  (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
                    (gammaTwoCosetRep q)) • ModularGroup.fdo)
            exact (closure_smul _ _).symm
""",
            1,
            "FunctionalAnalysis commute closure with each real SL2 action",
        ),
        (
            """  exact MeasurableSet.const_smul modularHalfOpenTile_measurable
    (gammaTwoCosetRep q)
""",
            """  change MeasurableSet
    (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      (gammaTwoCosetRep q)) • modularHalfOpenTile)
  exact MeasurableSet.const_smul modularHalfOpenTile_measurable
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      (gammaTwoCosetRep q))
""",
            1,
            "FunctionalAnalysis prove tile measurability through the real SL2 action",
        ),
    ])


def main() -> int:
    pass110.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
