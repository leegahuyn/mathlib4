from __future__ import annotations

from pathlib import Path

import apply_one_hundred_eighth_pass_repairs as pass108
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
  | head => simp [referenceMock1MList, referenceMock1RPhases]
  | tail _ hblock =>
      cases hblock with
      | head => simp [referenceMock1MList, referenceMock1RPhases]
      | tail _ hblock =>
          cases hblock with
          | head => simp [referenceMock1MList, referenceMock1RPhases]
          | tail _ hnil => cases hnil
""",
            """  cases hblock with
  | head => decide
  | tail _ hblock =>
      cases hblock with
      | head => decide
      | tail _ hblock =>
          cases hblock with
          | head => decide
          | tail _ hnil => cases hnil
""", 1,
            "Mock1Advanced decide the three concrete weighted-block memberships",
        ),
        (
            """  change List.Mem term
    [ { exponent := (-6401 / 4 : Rat), coefficient := 1 }
    , { exponent := (-6353 / 4 : Rat), coefficient := (3 / 2 : Rat) }
    , { exponent := (-6281 / 4 : Rat), coefficient := (1 / 2 : Rat) } ] at hterm
""",
            """  change List.Mem term
    [ { exponent := (-6439 / 4 : Rat), coefficient := (3 / 2 : Rat) }
    , { exponent := (-6353 / 4 : Rat), coefficient := (3 / 2 : Rat) }
    , { exponent := (-6281 / 4 : Rat), coefficient := (1 / 2 : Rat) } ] at hterm
""", 1,
            "Mock1Advanced match the declared principal-term list exactly",
        ),
        (
            """  change List.Mem advancedClaimsIIPaperItem1OneCuspLabel
    [infinityCuspLabel, zeroCuspLabel] at h
  cases h with
  | head => exact advanced_claims_ii_paper_item1_one_cusp_ne_infinity rfl
  | tail _ h =>
      cases h with
      | head => exact advanced_claims_ii_paper_item1_one_cusp_ne_zero rfl
      | tail _ hnil => cases hnil
""",
            """  change List.Mem advancedClaimsIIPaperItem1OneCuspLabel
    [infinityCuspLabel, zeroCuspLabel] at h
  rcases List.mem_cons.mp h with hInf | hRest
  · exact advanced_claims_ii_paper_item1_one_cusp_ne_infinity hInf
  · have hZero : advancedClaimsIIPaperItem1OneCuspLabel = zeroCuspLabel :=
      List.mem_singleton.mp hRest
    exact advanced_claims_ii_paper_item1_one_cusp_ne_zero hZero
""", 1,
            "Mock1Advanced refute modeled cusp membership without dependent cases",
        ),
        (
            """  finiteInsideOutside :=
    advanced_claims_ii_ramanujan_f_finite_inside_outside_identity
""",
            """  finiteInsideOutside :=
    advanced_claims_ii_ramanujan_finite_inside_outside_identity
""", 1,
            "Mock1Advanced reference the existing Ramanujan finite identity",
        ),
        (
            """  have h1 := h (1 : Fin 6)
  native_decide at h1
""",
            """  have h1 := h (1 : Fin 6)
  have hw := advanced_claims_ii_ramanujan_f_padic_worked_table_witness
  rw [hw.1, hw.2] at h1
  norm_num at h1
""", 1,
            "Mock1Advanced contradict the worked-table link with proved values",
        ),
        (
            """theorem advanced_claims_ii_entropy_paper_input_manifest_incomplete :
    Not
      (AdvancedClaimsIIEntropyPaperInputManifest.Complete
        referenceAdvancedClaimsIIEntropyPaperInputManifest) := by
  native_decide
""",
            """theorem advanced_claims_ii_entropy_paper_input_manifest_incomplete :
    Not
      (AdvancedClaimsIIEntropyPaperInputManifest.Complete
        referenceAdvancedClaimsIIEntropyPaperInputManifest) := by
  simp [AdvancedClaimsIIEntropyPaperInputManifest.Complete,
    referenceAdvancedClaimsIIEntropyPaperInputManifest]
""", 1,
            "Mock1Advanced prove entropy-manifest incompleteness propositionally",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """    rw [UpperHalfPlane.denom_apply]
    norm_num [gammaLower]
""",
            """    rw [ModularGroup.denom_apply]
    norm_num [gammaLower]
""", 1,
            "Mock2 use the current modular-group denominator application lemma",
        ),
        (
            """structure MockSheaf (X : Type u) [TopologicalSpace X] where
  toMockBundle : MockBundle (TopologicalSpace.Opens X)
  isSheaf : IsSheafLike (MockBundle.toPresheafLike toMockBundle)
""",
            """structure MockSheaf (X : Type u) [TopologicalSpace X] where
  toMockBundle : MockBundle.{u, u} (TopologicalSpace.Opens X)
  isSheaf : IsSheafLike
    (MockBundle.toPresheafLike (X := X) toMockBundle)
""", 1,
            "Mock2 fix the mock-sheaf section universe explicitly",
        ),
        (
            """theorem zero_convergesAt (q : ℂ) :
    (0 : QSeries).ConvergesAt q := by
  simp [ConvergesAt, term]
""",
            """theorem zero_convergesAt (q : ℂ) :
    (0 : QSeries).ConvergesAt q := by
  simpa [ConvergesAt, term] using
    (summable_zero : Summable (fun _ : ℕ => (0 : ℂ)))
""", 1,
            "Mock2 prove zero q-series convergence from summable_zero",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """    convert
      ((((hasDerivAt_id (x : ℂ)).const_mul B).comp_ofReal).const_add A)
      using 1 <;> rfl
""",
            """    simpa only [mul_one] using
      ((((hasDerivAt_id (x : ℂ)).const_mul B).comp_ofReal).const_add A)
""", 1,
            "Mock2Advanced simplify the affine derivative coefficient",
        ),
        (
            """    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    convert ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
      using 1 <;> rfl
""",
            """    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using
      ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
""", 1,
            "Mock2Advanced simplify the exponential-phase derivative coefficient",
        ),
        (
            """    apply intervalIntegral.integral_congr
    intro t ht
    rw [profile_on_nonpositive]
""",
            """    apply intervalIntegral.integral_congr
    intro t ht
    change Complex.exp (c * (t : ℂ)) * (profile T t : ℂ) =
      ((T : ℂ) + 1 * (t : ℂ)) * Complex.exp (c * (t : ℂ))
    rw [profile_on_nonpositive]
""", 1,
            "Mock2Advanced beta-reduce the nonpositive profile integral goal",
        ),
        (
            """    apply intervalIntegral.integral_congr
    intro t ht
    rw [profile_on_nonnegative]
""",
            """    apply intervalIntegral.integral_congr
    intro t ht
    change Complex.exp (c * (t : ℂ)) * (profile T t : ℂ) =
      ((T : ℂ) + (-1) * (t : ℂ)) * Complex.exp (c * (t : ℂ))
    rw [profile_on_nonnegative]
""", 1,
            "Mock2Advanced beta-reduce the nonnegative profile integral goal",
        ),
    ])


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    count = text.count("  apply EventuallyLE.antisymm")
    if count == 6:
        text = text.replace(
            "  apply EventuallyLE.antisymm",
            "  apply Filter.EventuallyLE.antisymm",
        )
        changed = True
        print("FunctionalAnalysis qualify six eventual-order antisymmetry uses: applied 6")
    elif text.count("  apply Filter.EventuallyLE.antisymm") >= 7:
        print("FunctionalAnalysis qualify six eventual-order antisymmetry uses: already applied")
    else:
        raise RuntimeError(
            f"FunctionalAnalysis direct EventuallyLE.antisymm count unexpected: {count}"
        )

    replacements = [
        (
            """theorem gammaTwoCircularPairingMatrix_mem :
    gammaTwoCircularPairingMatrix ∈ GammaTwo := by
  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [gammaTwoCircularPairingMatrix]
""",
            """theorem gammaTwoCircularPairingMatrix_mem :
    gammaTwoCircularPairingMatrix ∈ GammaTwo := by
  rw [CongruenceSubgroup.Gamma_mem]
  change (1 : ZMod 2) = 1 /\\
    (0 : ZMod 2) = 0 /\\
    (2 : ZMod 2) = 0 /\\
    (1 : ZMod 2) = 1
  decide
""", 1,
            "FunctionalAnalysis discharge the circular Gamma2 congruences",
        ),
        (
            """def gammaTwoStandardEdgeParam
    (e : GammaTwoStandardEdge) (t : GammaTwoPositiveEdgeParameter) : ℍ :=
""",
            """noncomputable def gammaTwoStandardEdgeParam
    (e : GammaTwoStandardEdge) (t : GammaTwoPositiveEdgeParameter) : ℍ :=
""", 1,
            "FunctionalAnalysis mark rational edge parametrization noncomputable",
        ),
        (
            """        field_simp [hden.ne']
        ring
""",
            """        norm_num
        field_simp [hden.ne']
        ring_nf
""", 2,
            "FunctionalAnalysis normalize both circular-edge norm identities",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass108.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
