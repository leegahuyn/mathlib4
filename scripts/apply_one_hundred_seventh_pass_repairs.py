from __future__ import annotations

from pathlib import Path

import apply_one_hundred_sixth_pass_repairs as pass106
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
            """norm_num [Fin.sum_univ_succ, Finset.sum_range_succ,
      AdvancedClaimsIIPaperI2PrecisionTube,""",
            """norm_num [Nat.choose, Fin.sum_univ_succ, Finset.sum_range_succ,
      AdvancedClaimsIIPaperI2PrecisionTube,""", 1,
            "Mock1Advanced evaluate binomial choices in precision-tube arithmetic",
        ),
        (
            """norm_num [Finset.sum_range_succ,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifferenceResidue,""",
            """norm_num [Nat.choose, Finset.sum_range_succ,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifferenceResidue,""", 1,
            "Mock1Advanced evaluate binomial choices in residue arithmetic",
        ),
        (
            """norm_num [Finset.sum_range_succ,
      FiniteCongruenceMod, IntCongruent, PrimePower,""",
            """norm_num [Nat.choose, Finset.sum_range_succ,
      FiniteCongruenceMod, IntCongruent, PrimePower,""", 1,
            "Mock1Advanced evaluate binomial choices in congruence arithmetic",
        ),
        (
            """rcases hblock with rfl | rfl | rfl <;>
    simp [referenceMock1MList, referenceMock1RPhases]""",
            """rcases hblock with (rfl | rfl | rfl) <;>
    simp [referenceMock1MList, referenceMock1RPhases]""", 1,
            "Mock1Advanced parenthesize the three weighted-block cases",
        ),
        (
            """rcases hterm with rfl | rfl | rfl <;> norm_num""",
            """rcases hterm with (rfl | rfl | rfl) <;> norm_num""", 1,
            "Mock1Advanced parenthesize the three principal-term cases",
        ),
        (
            """theorem advanced_claims_ii_paper_item1_one_cusp_relevant :
    List.Mem advancedClaimsIIPaperItem1OneCuspLabel
      referenceAdvancedClaimsIIPaperItem1Cusps := by
  simp [referenceAdvancedClaimsIIPaperItem1Cusps]
""",
            """theorem advanced_claims_ii_paper_item1_one_cusp_relevant :
    List.Mem advancedClaimsIIPaperItem1OneCuspLabel
      referenceAdvancedClaimsIIPaperItem1Cusps := by
  simp only [referenceAdvancedClaimsIIPaperItem1Cusps, List.mem_cons,
    List.mem_singleton]
  exact Or.inr (Or.inr rfl)
""", 1,
            "Mock1Advanced construct the third cusp-list membership explicitly",
        ),
        (
            """  simp [referenceTransportAcrossAllCuspsCertificate, referenceRelevantCusps,
    advanced_claims_ii_paper_item1_one_cusp_ne_infinity,
    advanced_claims_ii_paper_item1_one_cusp_ne_zero]
""",
            """  intro h
  simp only [referenceTransportAcrossAllCuspsCertificate, referenceRelevantCusps,
    List.mem_cons, List.mem_singleton] at h
  rcases h with h | h
  · exact advanced_claims_ii_paper_item1_one_cusp_ne_infinity h
  · exact advanced_claims_ii_paper_item1_one_cusp_ne_zero h
""", 1,
            "Mock1Advanced eliminate the two modeled cusp alternatives explicitly",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """          Complex.I = 2 * Complex.I + 1 := by
    ext <;> norm_num [UpperHalfPlane.denom, gammaLower]
  rw [hdenom, UpperHalfPlane.I_im]""",
            """          (UpperHalfPlane.I : ℂ) = 2 * Complex.I + 1 := by
    apply Complex.ext <;> norm_num [UpperHalfPlane.denom, gammaLower]
  rw [hdenom, UpperHalfPlane.I_im]""", 1,
            "Mock2 compute the denominator at the coerced upper-half-plane point",
        ),
        (
            """  have heq := congrArg (fun f => f.toFun z) (hs j i)
  simpa [glueFunction, j, z, presheaf, openInclusion] using heq""",
            """  have heq := congrArg (fun f => f.toFun z) (hs j i)
  change (s j).toFun ⟨x.1, hxj⟩ = (s i).toFun ⟨x.1, hxi⟩ at heq
  simpa [glueFunction, j] using heq""", 1,
            "Mock2 expose overlap comaps before chart-independence simplification",
        ),
        (
            """  have heq := congrArg (fun f => f.toFun zi) (hxy i)
  simpa [presheaf, openInclusion, zi] using heq""",
            """  have heq := congrArg (fun f => f.toFun zi) (hxy i)
  change x.toFun z = y.toFun z at heq
  exact heq""", 1,
            "Mock2 expose restriction comaps in the locality proof",
        ),
    ])


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False
    replacements = [
        (
            """  rw [profile_eq_sub_abs]
  · exact abs_of_nonneg ht.1
  · simpa [abs_of_nonneg ht.1] using ht.2""",
            """  rw [profile_eq_sub_abs]
  · rw [abs_of_nonneg ht.1]
  · simpa [abs_of_nonneg ht.1] using ht.2""", 1,
            "Mock2Advanced rewrite the absolute value inside the subtraction",
        ),
        (
            """(intervalIntegral.integral_add_adjacent_intervals
        (continuous_profile T).intervalIntegrable
        (continuous_profile T).intervalIntegrable).symm""",
            """(intervalIntegral.integral_add_adjacent_intervals
        ((continuous_profile T).intervalIntegrable (-T) 0)
        ((continuous_profile T).intervalIntegrable 0 T)).symm""", 1,
            "Mock2Advanced instantiate both adjacent interval-integrability proofs",
        ),
        (
            """    simpa only [mul_one] using
      ((((hasDerivAt_id (x : ℂ)).const_mul B).comp_ofReal).const_add A)""",
            """    convert
      ((((hasDerivAt_id (x : ℂ)).const_mul B).comp_ofReal).const_add A)
      using 1 <;> simp""", 1,
            "Mock2Advanced identify the affine complex derivative extensionally",
        ),
        (
            """    simpa only [mul_one] using
      ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal""",
            """    convert ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
      using 1 <;> simp""", 1,
            "Mock2Advanced identify the exponential phase derivative extensionally",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    count = text.count("intervalIntegrable_id")
    if count == 4:
        text = text.replace(
            "intervalIntegrable_id", "intervalIntegral.intervalIntegrable_id"
        )
        changed = True
        print("Mock2Advanced qualify four identity integrability lemmas: applied 4")
    elif text.count("intervalIntegral.intervalIntegrable_id") == 4:
        print("Mock2Advanced qualify four identity integrability lemmas: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced identity integrability occurrences unexpected: {count}"
        )
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    manual_fintypes = [
        (
            "GammaTwoCusp",
            "{.atInfinity, .zero, .one}",
            "gammaTwoCuspFintype",
        ),
        (
            "GammaTwoCuspEnd",
            "{.atInfinity, .zero, .one, .negOne}",
            "gammaTwoCuspEndFintype",
        ),
        (
            "GammaTwoStandardEdge",
            "{.leftVertical, .rightVertical, .leftCircular, .rightCircular}",
            "gammaTwoStandardEdgeFintype",
        ),
    ]
    for type_name, elems, instance_name in manual_fintypes:
        start = text.index(f"inductive {type_name}")
        old = "deriving DecidableEq, Fintype\n"
        pos = text.index(old, start)
        replacement = (
            "deriving DecidableEq\n\n"
            f"instance {instance_name} : Fintype {type_name} where\n"
            f"  elems := {elems}\n"
            "  complete x := by cases x <;> simp\n"
        )
        text = text[:pos] + replacement + text[pos + len(old):]
        changed = True
        print(f"FunctionalAnalysis define {type_name} Fintype explicitly: applied 1")

    for name in [
        "gammaTwoCuspHeight",
        "gammaTwoLeftCircleCenter",
        "gammaTwoRightCircleCenter",
        "gammaTwoLeftCircleDistance",
        "gammaTwoRightCircleDistance",
    ]:
        old = f"def {name}"
        new = f"noncomputable def {name}"
        count = text.count(old)
        if count == 1:
            text = text.replace(old, new, 1)
            changed = True
            print(f"FunctionalAnalysis mark {name} noncomputable: applied 1")
        elif new in text:
            print(f"FunctionalAnalysis mark {name} noncomputable: already applied")
        else:
            raise RuntimeError(f"FunctionalAnalysis definition {name} absent")

    old_continuity = """theorem gammaTwoCuspHeight_continuous (κ : GammaTwoCusp) :
    Continuous (gammaTwoCuspHeight κ) :=
  UpperHalfPlane.continuous_im.comp
    (continuous_const_smul (gammaTwoCuspScaling κ)⁻¹)"""
    new_continuity = """theorem gammaTwoCuspHeight_continuous (κ : GammaTwoCusp) :
    Continuous (gammaTwoCuspHeight κ) := by
  change Continuous (fun z : ℍ =>
    ((((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      ((gammaTwoCuspScaling κ)⁻¹)) • z).im)
  exact UpperHalfPlane.continuous_im.comp
    (continuous_const_smul
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
        ((gammaTwoCuspScaling κ)⁻¹)))"""
    text, did = replace_exact(
        text, old_continuity, new_continuity, 1,
        "FunctionalAnalysis prove cusp-height continuity through the SL2R action",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass106.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
