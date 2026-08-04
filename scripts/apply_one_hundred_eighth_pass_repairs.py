from __future__ import annotations

from pathlib import Path

import apply_one_hundred_seventh_pass_repairs as pass107
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
            """  simp only [referenceAdvancedClaimsIIPaperT3WeightedBlocks,
    List.mem_cons, List.mem_singleton] at hblock
  rcases hblock with (rfl | rfl | rfl) <;>
    simp [referenceMock1MList, referenceMock1RPhases]
""",
            """  change List.Mem block
    [ { m := 0, r := 0, coefficient := 1 }
    , { m := 1, r := 0, coefficient := (-1 / 2 : Rat) }
    , { m := 0, r := (1 / 2 : Rat), coefficient := (1 / 2 : Rat) } ] at hblock
  cases hblock with
  | head => simp [referenceMock1MList, referenceMock1RPhases]
  | tail _ hblock =>
      cases hblock with
      | head => simp [referenceMock1MList, referenceMock1RPhases]
      | tail _ hblock =>
          cases hblock with
          | head => simp [referenceMock1MList, referenceMock1RPhases]
          | tail _ hnil => cases hnil
""", 1,
            "Mock1Advanced eliminate weighted-block membership inductively",
        ),
        (
            """  simp only [referenceAdvancedClaimsIIPaperT3DeclaredPrincipalTerms,
    List.mem_cons, List.mem_singleton] at hterm
  rcases hterm with (rfl | rfl | rfl) <;> norm_num
""",
            """  change List.Mem term
    [ { exponent := (-6401 / 4 : Rat), coefficient := 1 }
    , { exponent := (-6353 / 4 : Rat), coefficient := (3 / 2 : Rat) }
    , { exponent := (-6281 / 4 : Rat), coefficient := (1 / 2 : Rat) } ] at hterm
  cases hterm with
  | head => norm_num
  | tail _ hterm =>
      cases hterm with
      | head => norm_num
      | tail _ hterm =>
          cases hterm with
          | head => norm_num
          | tail _ hnil => cases hnil
""", 1,
            "Mock1Advanced eliminate principal-term membership inductively",
        ),
        (
            """  simp only [referenceAdvancedClaimsIIPaperItem1Cusps, List.mem_cons,
    List.mem_singleton]
  exact Or.inr (Or.inr rfl)
""",
            """  change List.Mem advancedClaimsIIPaperItem1OneCuspLabel
    [infinityCuspLabel, zeroCuspLabel, advancedClaimsIIPaperItem1OneCuspLabel]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
""", 1,
            "Mock1Advanced construct cusp membership with List.Mem constructors",
        ),
        (
            """  intro h
  simp only [referenceTransportAcrossAllCuspsCertificate, referenceRelevantCusps,
    List.mem_cons, List.mem_singleton] at h
  rcases h with h | h
  · exact advanced_claims_ii_paper_item1_one_cusp_ne_infinity h
  · exact advanced_claims_ii_paper_item1_one_cusp_ne_zero h
""",
            """  intro h
  change List.Mem advancedClaimsIIPaperItem1OneCuspLabel
    [infinityCuspLabel, zeroCuspLabel] at h
  cases h with
  | head => exact advanced_claims_ii_paper_item1_one_cusp_ne_infinity rfl
  | tail _ h =>
      cases h with
      | head => exact advanced_claims_ii_paper_item1_one_cusp_ne_zero rfl
      | tail _ hnil => cases hnil
""", 1,
            "Mock1Advanced refute modeled cusp membership inductively",
        ),
        (
            """theorem advanced_claims_ii_paper_k_formula_manifest_incomplete :
    Not
      (AdvancedClaimsIIPaperKFormulaInputManifest.Complete
        referenceAdvancedClaimsIIPaperKFormulaInputManifest) := by
  native_decide
""",
            """theorem advanced_claims_ii_paper_k_formula_manifest_incomplete :
    Not
      (AdvancedClaimsIIPaperKFormulaInputManifest.Complete
        referenceAdvancedClaimsIIPaperKFormulaInputManifest) := by
  simp [AdvancedClaimsIIPaperKFormulaInputManifest.Complete,
    referenceAdvancedClaimsIIPaperKFormulaInputManifest]
""", 1,
            "Mock1Advanced prove paper-K manifest incompleteness propositionally",
        ),
        (
            """  prefix_eq := by
    intro n hn
    simp [TruncatedQSeries.coefficientAt, hn,
      referenceAdvancedClaimsIIRamanujanFTruncatedQSeries,
      referenceAdvancedClaimsIIRamanujanFQSeries]
""",
            """  prefix_eq := by
    intro n hn
    have hn16 : n < 16 := by
      simpa [referenceAdvancedClaimsIIRamanujanFTruncatedQSeries] using hn
    simp [TruncatedQSeries.coefficientAt, hn16,
      referenceAdvancedClaimsIIRamanujanFTruncatedQSeries,
      referenceAdvancedClaimsIIRamanujanFQSeries]
""", 1,
            "Mock1Advanced expose the concrete truncation bound",
        ),
        (
            """theorem advanced_claims_ii_rlf_ramanujan_f_input_manifest_incomplete :
    Not
      (AdvancedClaimsIIRlfRamanujanFInputManifest.Complete
        referenceAdvancedClaimsIIRlfRamanujanFInputManifest) := by
  native_decide
""",
            """theorem advanced_claims_ii_rlf_ramanujan_f_input_manifest_incomplete :
    Not
      (AdvancedClaimsIIRlfRamanujanFInputManifest.Complete
        referenceAdvancedClaimsIIRlfRamanujanFInputManifest) := by
  simp [AdvancedClaimsIIRlfRamanujanFInputManifest.Complete,
    referenceAdvancedClaimsIIRlfRamanujanFInputManifest]
""", 1,
            "Mock1Advanced prove RLF manifest incompleteness propositionally",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """          (UpperHalfPlane.I : ℂ) = 2 * Complex.I + 1 := by
    apply Complex.ext <;> norm_num [UpperHalfPlane.denom, gammaLower]
""",
            """          (UpperHalfPlane.I : ℂ) = 2 * Complex.I + 1 := by
    rw [UpperHalfPlane.denom_apply]
    norm_num [gammaLower]
""", 1,
            "Mock2 rewrite the modular denominator through denom_apply",
        ),
        (
            """theorem isSheaf : IsSheafLike (presheaf F) :=
  { locality := locality
    gluing_exists := gluing_exists
    gluing_unique := gluing_unique }
""",
            """theorem isSheaf : IsSheafLike (presheaf (X := X) F) :=
  { locality := locality (X := X) (F := F)
    gluing_exists := gluing_exists (X := X) (F := F)
    gluing_unique := gluing_unique (X := X) (F := F) }
""", 1,
            "Mock2 fix the sheaf carrier and proof universes explicitly",
        ),
        (
            """    IsLocallyConstant s :=
  s.isLocallyConstant
""",
            """    IsLocallyConstant s.toFun :=
  s.isLocallyConstant
""", 1,
            "Mock2 state local constancy on the underlying section function",
        ),
        (
            """    (Lq D).res hUW s x = s ⟨x.1, hUW x.2⟩ :=
  rfl
""",
            """    ((Lq D).res hUW s).toFun x = s.toFun ⟨x.1, hUW x.2⟩ :=
  rfl
""", 1,
            "Mock2 evaluate Lq restriction through LocallyConstant.toFun",
        ),
        (
            """      (s : (localSectionPresheaf D).Section U),
      IsLocallyConstant s
""",
            """      (s : (localSectionPresheaf D).Section U),
      IsLocallyConstant s.toFun
""", 1,
            "Mock2 record certificate local constancy on toFun",
        ),
    ])


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False
    count = text.count("intervalIntegral.integral_id")
    if count == 4:
        text = text.replace("intervalIntegral.integral_id", "integral_id")
        changed = True
        print("Mock2Advanced use the global integral_id theorem: applied 4")
    elif text.count("integral_id") >= 4:
        print("Mock2Advanced use the global integral_id theorem: already applied")
    else:
        raise RuntimeError(f"Mock2Advanced integral_id count unexpected: {count}")

    replacements = [
        (
            """      using 1 <;> simp
""",
            """      using 1 <;> rfl
""", 2,
            "Mock2Advanced close derivative conversions definitionally",
        ),
        (
            """  have hcontinuous : Continuous
      (fun t : ℝ =>
        Complex.exp (c * (t : ℂ)) * (profile T t : ℂ)) := by
    fun_prop
""",
            """  have hphase : Continuous
      (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by fun_prop
  have hprofile : Continuous (fun t : ℝ => (profile T t : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_profile T)
  have hcontinuous : Continuous
      (fun t : ℝ =>
        Complex.exp (c * (t : ℂ)) * (profile T t : ℂ)) :=
    hphase.mul hprofile
""", 1,
            "Mock2Advanced prove tent-kernel product continuity compositionally",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """    ((((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      ((gammaTwoCuspScaling κ)⁻¹)) • z).im)
  exact""",
            """    ((((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      ((gammaTwoCuspScaling κ)⁻¹)) • z).im))
  exact""", 1,
            "FunctionalAnalysis close the explicit SL2R continuity target",
        ),
    ])


def main() -> int:
    pass107.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
