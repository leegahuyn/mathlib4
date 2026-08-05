from __future__ import annotations

from pathlib import Path

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


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            '''    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    rw [tensorRestriction_tmul, hpot]
''',
            '''    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    change
      ((locallyConstantRestriction E hUV
          (pointwiseOperator P.qPotential V l) ⊗ₜ[ℂ]
        locallyConstantRestriction F hUV m) ⊗ₜ[ℂ]
          locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V)) =
        ((pointwiseOperator P.qPotential U
            (locallyConstantRestriction E hUV l) ⊗ₜ[ℂ]
          locallyConstantRestriction F hUV m) ⊗ₜ[ℂ] dlogFrame U)
    rw [hpot, hframe]
''',
            1,
            "Mock2 expose nested tensor restrictions in nabla naturality",
        ),
        (
            '''    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    rw [tensorRestriction_tmul, hlog]
''',
            '''    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    change
      ((locallyConstantRestriction E hUV l ⊗ₜ[ℂ]
        locallyConstantRestriction F hUV
          (pointwiseOperator P.logDerivative V m)) ⊗ₜ[ℂ]
          locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V)) =
        ((locallyConstantRestriction E hUV l ⊗ₜ[ℂ]
          pointwiseOperator P.logDerivative U
            (locallyConstantRestriction F hUV m)) ⊗ₜ[ℂ] dlogFrame U)
    rw [hlog, hframe]
''',
            1,
            "Mock2 expose nested tensor restrictions in logarithmic naturality",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            '''      apply
        (ShortComplex.exact_iff_mono _
          (cyclicFreeComplex_d_succ_succ N 0)).2
      rw [cyclicFreeComplex_d_one_zero,
        ModuleCat.mono_iff_injective]
''',
            '''      apply
        (ShortComplex.exact_iff_mono _
          (cyclicFreeComplex_d_succ_succ N 0)).2
      change Mono ((cyclicFreeComplex N).d 1 0)
      rw [cyclicFreeComplex_d_one_zero,
        ModuleCat.mono_iff_injective]
''',
            1,
            "Mock2Advanced expose the degree-one differential before mono rewriting",
        ),
        (
            '''theorem intRankOne_projective : Projective (ModuleCat.of ℤ ℤ) :=
  ModuleCat.projective_of_free (Basis.singleton (Fin 1) ℤ)
''',
            '''theorem intRankOne_projective : Projective (ModuleCat.of ℤ ℤ) := by
  infer_instance
''',
            1,
            "Mock2Advanced use the inherited projectivity of the rank-one free module",
        ),
        (
            '''    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [cyclicPresentationShortComplex])
      (by simp [cyclicPresentationShortComplex])
''',
            '''    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Category.id_comp, Category.comp_id])
      (by simp only [Category.id_comp, Category.comp_id])
''',
            1,
            "Mock2Advanced close the identity short-complex comparison categorically",
        ),
        (
            '''  quasiIso := fun n => by
    cases n with
    | zero => exact cyclicFreeAugmentation_quasiIsoAt_zero N
    | succ n => exact cyclicFreeAugmentation_quasiIsoAt_succ N hN n
''',
            '''  quasiIso := by
    rw [quasiIso_iff]
    intro n
    cases n with
    | zero => exact cyclicFreeAugmentation_quasiIsoAt_zero N
    | succ n => exact cyclicFreeAugmentation_quasiIsoAt_succ N hN n
''',
            1,
            "Mock2Advanced construct the bundled quasi-isomorphism from every degree",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            '''  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by
      simpa only [minSmoothness] using
        (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top)))).iteratedFDeriv_cons
''',
            '''  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by
      simpa [minSmoothness] using
        (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top)))).iteratedFDeriv_cons
''',
            1,
            "FunctionalAnalysis simplify the real-field minimum smoothness condition",
        ),
        (
            '''  simp only [raiseRaw, lowerRaw, star_add, star_mul', star_inv₀,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  field_simp [hh] <;> ring
''',
            '''  have hI : star (Complex.I) = -Complex.I := by simp
  have hweight :
      star (physicalExponent a * (heightC z)⁻¹) =
        physicalExponent a * (heightC z)⁻¹ := by
    simp only [star_mul', star_inv₀, conj_physicalExponent, conj_heightC]
    ring
  simp only [raiseRaw, lowerRaw, star_add, star_mul']
  rw [hI, hweight]
  field_simp [hh]
  ring
''',
            1,
            "FunctionalAnalysis normalize conjugation in the Green bulk identity",
        ),
        (
            '''  rw [notMem_tsupport_iff_eventuallyEq] at hz
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, eventuallyEq_map]
  simpa [upperLift, Function.comp_def] using hz
''',
            '''  rw [notMem_tsupport_iff_eventuallyEq] at hz
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq]
  change
    (fun w : ℍ => upperLift f (w : ℂ)) =ᶠ[nhds z]
      (fun _ : ℍ => (0 : ℂ))
  simpa [upperLift, Function.comp_def] using hz
''',
            1,
            "FunctionalAnalysis transport local zero through the mapped neighborhood definition",
        ),
        (
            "Submodule.codRestrict smoothQuotientCompactSubmodule",
            "LinearMap.codRestrict smoothQuotientCompactSubmodule",
            3,
            "FunctionalAnalysis use LinearMap.codRestrict on the quotient-compact domain",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
