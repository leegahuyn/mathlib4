from __future__ import annotations

from pathlib import Path

import apply_one_hundred_nineteenth_pass_repairs as pass119
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
            """  cases r <;> decide
""",
            """  cases r <;>
    simp_all [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass]
""",
            1,
            "Mock1Advanced solve the finite evidence partition without typeclass decision search",
        ),
        (
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  decide
""",
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  simp [finiteExactRequirements, all, evidenceClass]
""",
            1,
            "Mock1Advanced reduce finite-exact nonemptiness by simplification",
        ),
        (
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  decide
""",
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  simp [analyticBoundaryRequirements, all, evidenceClass]
""",
            1,
            "Mock1Advanced reduce analytic-boundary nonemptiness by simplification",
        ),
        (
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  decide
""",
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  simp [diagnosticMetadataRequirements, all, evidenceClass]
""",
            1,
            "Mock1Advanced reduce diagnostic nonemptiness by simplification",
        ),
        (
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  decide
""",
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  simp [aggregateRequirements, all, evidenceClass]
""",
            1,
            "Mock1Advanced reduce aggregate nonemptiness by simplification",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """  obj : TopologicalSpace.Opens X → ModuleCat.{0} ℂ
""",
            """  obj : TopologicalSpace.Opens X → ModuleCat.{max u v} ℂ
""",
            1,
            "Mock2 allow section carriers to live in the open-set/value universe maximum",
        ),
        (
            """def locallyConstantRestriction (E : ModuleCat ℂ)
""",
            """def locallyConstantRestriction (E : ModuleCat.{v} ℂ)
""",
            1,
            "Mock2 universe-polymorphic locally constant restriction",
        ),
        (
            """@[simp] theorem locallyConstantRestriction_apply (E : ModuleCat ℂ)
""",
            """@[simp] theorem locallyConstantRestriction_apply (E : ModuleCat.{v} ℂ)
""",
            1,
            "Mock2 universe-polymorphic restriction evaluation",
        ),
        (
            """theorem locallyConstantRestriction_id (E : ModuleCat ℂ)
""",
            """theorem locallyConstantRestriction_id (E : ModuleCat.{v} ℂ)
""",
            1,
            "Mock2 universe-polymorphic restriction identity",
        ),
        (
            """theorem locallyConstantRestriction_comp (E : ModuleCat ℂ)
""",
            """theorem locallyConstantRestriction_comp (E : ModuleCat.{v} ℂ)
""",
            1,
            "Mock2 universe-polymorphic restriction composition",
        ),
        (
            """def locallyConstantLinearPresheaf (E : ModuleCat ℂ) :
""",
            """def locallyConstantLinearPresheaf (E : ModuleCat.{v} ℂ) :
""",
            1,
            "Mock2 universe-polymorphic locally constant linear presheaf",
        ),
        (
            """@[simp] theorem locallyConstantLinearPresheaf_obj (E : ModuleCat ℂ)
""",
            """@[simp] theorem locallyConstantLinearPresheaf_obj (E : ModuleCat.{v} ℂ)
""",
            1,
            "Mock2 universe-polymorphic object formula",
        ),
        (
            """theorem locallyConstantLinearPresheaf_isSheaf (E : ModuleCat ℂ) :
""",
            """theorem locallyConstantLinearPresheaf_isSheaf (E : ModuleCat.{v} ℂ) :
""",
            1,
            "Mock2 universe-polymorphic sheaf theorem",
        ),
        (
            """theorem lq_fibre_has_module (D : Definition11.AnalyticData V)
""",
            """noncomputable def lq_fibre_has_module (D : Definition11.AnalyticData V)
""",
            1,
            "Mock2 make the module-valued fibre declaration a definition",
        ),
        (
            """  map_smul' c x := by
    simp [smul_add]
""",
            """  map_smul' c x := by
    ring
""",
            1,
            "Mock2 close homogeneous evaluation scalar linearity algebraically",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  rw [← normalizedFourier_eq_mathlib
    (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ]
""",
            """  rw [← TentKernel.normalizedFourier_eq_mathlib
    (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ]
""",
            1,
            "Mock2Advanced qualify the normalized Fourier bridge",
        ),
        (
            """    normalizedFourier
""",
            """    TentKernel.normalizedFourier
""",
            1,
            "Mock2Advanced qualify the first normalized Fourier occurrence",
        ),
        (
            """          normalizedFourier
""",
            """          TentKernel.normalizedFourier
""",
            1,
            "Mock2Advanced qualify the second normalized Fourier occurrence",
        ),
        (
            """      simp only [normalizedFourier, fourierPositiveSmoothTentFunction,
""",
            """      simp only [TentKernel.normalizedFourier, fourierPositiveSmoothTentFunction,
""",
            1,
            "Mock2Advanced unfold the qualified normalized Fourier definition",
        ),
        (
            """      rw [normalizedFourier_eq_mathlib,
""",
            """      rw [TentKernel.normalizedFourier_eq_mathlib,
""",
            1,
            "Mock2Advanced qualify the second Fourier bridge",
        ),
        (
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    change AEStronglyMeasurable
""",
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    simp only [profileBesselConvention, Convention.normalizedKernel, one_mul]
    change AEStronglyMeasurable
""",
            1,
            "Mock2Advanced unfold the concrete convention before changing the measurable kernel",
        ),
        (
            """  rw [hentry]
  apply (Int.natAbs_eq_iff_mul_self_eq).2
  calc
    (L 1 1 * G 1 0 * R 0 0) *
        (L 1 1 * G 1 0 * R 0 0) =
        (L 1 1 * L 1 1) * (G 1 0 * G 1 0) *
          (R 0 0 * R 0 0) := by ring
    _ = G 1 0 * G 1 0 := by rw [hLsq, hRsq]; ring
""",
            """  rw [hentry, Int.natAbs_mul, Int.natAbs_mul]
  have hnatLsq : Int.natAbs (L 1 1) * Int.natAbs (L 1 1) = 1 := by
    simpa only [Int.natAbs_mul, Int.natAbs_one] using congrArg Int.natAbs hLsq
  have hnatRsq : Int.natAbs (R 0 0) * Int.natAbs (R 0 0) = 1 := by
    simpa only [Int.natAbs_mul, Int.natAbs_one] using congrArg Int.natAbs hRsq
  have hnatL : Int.natAbs (L 1 1) = 1 := by omega
  have hnatR : Int.natAbs (R 0 0) = 1 := by omega
  simp [hnatL, hnatR]
""",
            1,
            "Mock2Advanced prove lower-left natAbs invariance through multiplicativity",
        ),
        (
            """  sum_integral_interchange (B.integrable m)
    (B.summable_integral_norm m)
""",
            """  Mock2Adv.Interchange.sum_integral_interchange (B.integrable m)
    (B.summable_integral_norm m)
""",
            1,
            "Mock2Advanced call the ambient Tonelli certificate rather than the method recursively",
        ),
        (
            """  exact integrable_dirac (by simp [kernel])
""",
            """  exact integrable_dirac (by positivity)
""",
            1,
            "Mock2Advanced prove positivity of the geometric denominator directly",
        ),
        (
            """  filter_upwards [hlt, eventually_ge_atTop m₀] with m hm_lt hm_ge
  exact (not_lt_of_ge (hlower m hm_ge)) hm_lt
""",
            """  have hex : ∃ m, massFunctional D m < ε ∧ m₀ ≤ m :=
    (hlt.and (eventually_ge_atTop m₀)).exists
  rcases hex with ⟨m, hm_lt, hm_ge⟩
  exact (not_lt_of_ge (hlower m hm_ge)) hm_lt
""",
            1,
            "Mock2Advanced extract one large index from the eventual contradiction",
        ),
        (
            """  activeSet_finite : volume activeSet ≠ (⊤ : ℝ≥0∞)
""",
            """  activeSet_finite : volume activeSet ≠ (⊤ : ENNReal)
""",
            1,
            "Mock2Advanced avoid parser ambiguity in the active-set finite-measure field",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """      have hnormSq :
          Complex.normSq (modularCircularArcParam t : ℂ) = 1 := by
        simp only [modularCircularArcParam, UpperHalfPlane.coe_mk,
          Complex.normSq_apply]
        nlinarith [hsqrt]
""",
            """      have hnormSq :
          Complex.normSq (modularCircularArcParam t : ℂ) = 1 := by
        simp only [modularCircularArcParam, UpperHalfPlane.coe_mk,
          Complex.normSq_apply]
        nlinarith [hsqrt]
      have hden :
          (t : ℝ) / 2 * ((t : ℝ) / 2) +
              Real.sqrt (1 - ((t : ℝ) / 2) ^ 2) *
                Real.sqrt (1 - ((t : ℝ) / 2) ^ 2) = 1 := by
        nlinarith [hsqrt]
""",
            1,
            "FunctionalAnalysis record the unit denominator on the circular edge",
        ),
        (
            """          modularTileEdgeParam, modularCircularArcParam, hnormSq]
""",
            """          modularTileEdgeParam, modularCircularArcParam, hnormSq, hden]
""",
            2,
            "FunctionalAnalysis simplify both circular pairing coordinates with the unit denominator",
        ),
        (
            """theorem modularBoundaryOrbit_smul_mem_iff
    (g : SL(2, ℤ)) (z : ℍ) :
    g • z ∈ modularBoundaryOrbit ↔ z ∈ modularBoundaryOrbit := by
  rw [← modularBoundaryOrbit_smul g,
    Set.mem_smul_set_iff_inv_smul_mem, inv_smul_smul]
""",
            """theorem modularBoundaryOrbit_smul_mem_iff
    (g : SL(2, ℤ)) (z : ℍ) :
    g • z ∈ modularBoundaryOrbit ↔ z ∈ modularBoundaryOrbit := by
  calc
    g • z ∈ modularBoundaryOrbit ↔
        g • z ∈ g • modularBoundaryOrbit := by rw [modularBoundaryOrbit_smul g]
    _ ↔ z ∈ modularBoundaryOrbit := by
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
""",
            1,
            "FunctionalAnalysis use orbit-set invariance in the correct membership orientation",
        ),
        (
            """  simpa only [hγ] using
    modularBoundaryOrbit_smul_mem_iff (γ : SL(2, ℤ)) z
""",
            """  rw [hγ z]
  exact modularBoundaryOrbit_smul_mem_iff (γ : SL(2, ℤ)) z
""",
            1,
            "FunctionalAnalysis rewrite the effective action pointwise",
        ),
        (
            """  change ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z ∈
    gammaTwoOpenCarrier
  rw [hcancel]
  exact htile
""",
            """  simpa only [gammaTwoEffectiveElement_smul] using
    hcancel.symm ▸ htile
""",
            1,
            "FunctionalAnalysis keep the orbit-cover target in the closed carrier",
        ),
        (
            """  unfold gammaTwoNamedScalingHeightSublevel
  exact isClosed_iInter fun κ ↦
    isClosed_le (gammaTwoCuspHeight_continuous κ) continuous_const
""",
            """  unfold gammaTwoNamedScalingHeightSublevel
  rw [show {z : ℍ | ∀ κ : GammaTwoCusp,
      gammaTwoCuspHeight κ z ≤ gammaTwoCuspLevel Y} =
      ⋂ κ : GammaTwoCusp,
        {z : ℍ | gammaTwoCuspHeight κ z ≤ gammaTwoCuspLevel Y} by
    ext z
    simp]
  exact isClosed_iInter fun κ ↦
    isClosed_le (gammaTwoCuspHeight_continuous κ) continuous_const
""",
            1,
            "FunctionalAnalysis expose the universal height predicate as an intersection",
        ),
        (
            """  exact isClosed_iUnion_of_finite fun q ↦
    ModularGroup.isClosed_fd.smul (gammaTwoCosetRep q)
""",
            """  exact isClosed_iUnion_of_finite fun q ↦ by
    let g : SL(2, ℤ) := gammaTwoCosetRep q
    have hset :
        g • ModularGroup.fd =
          (fun z : ℍ => g⁻¹ • z) ⁻¹' ModularGroup.fd := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_smul_set.mp hz with ⟨w, hw, rfl⟩
        simpa using hw
      · intro hz
        exact Set.mem_smul_set.mpr ⟨g⁻¹ • z, hz, by simp⟩
    rw [hset]
    exact ModularGroup.isClosed_fd.preimage
      (HalfIntegralMultiplier.continuous_sl2z_smul g⁻¹)
""",
            1,
            "FunctionalAnalysis prove closedness of each translated modular tile by preimage",
        ),
        (
            """  UpperHalfPlane.continuous_im.comp
    (continuous_const_smul (gammaTwoCosetRep q)⁻¹)
""",
            """  UpperHalfPlane.continuous_im.comp
    (HalfIntegralMultiplier.continuous_sl2z_smul (gammaTwoCosetRep q)⁻¹)
""",
            1,
            "FunctionalAnalysis use the explicit continuous integral modular action",
        ),
        (
            """  exact ∑ q in Finset.univ.filter (fun q : GammaTwoRightCoset ↦
    gammaTwoTileCuspClass q = κ), gammaTwoTileHeight q z
""",
            """  exact Finset.sum
    (Finset.univ.filter (fun q : GammaTwoRightCoset ↦
      gammaTwoTileCuspClass q = κ))
    (fun q => gammaTwoTileHeight q z)
""",
            1,
            "FunctionalAnalysis replace unsupported term-mode binder syntax with Finset.sum",
        ),
    ])


def main() -> int:
    pass119.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
