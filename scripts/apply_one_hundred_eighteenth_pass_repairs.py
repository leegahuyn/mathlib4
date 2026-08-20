from __future__ import annotations

from pathlib import Path

import apply_one_hundred_seventeenth_pass_repairs as pass117
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
            """  classical
  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass] <;>
    decide
""",
            """  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass,
      List.mem_cons]
""",
            1,
            "Mock1Advanced discharge finite enum memberships constructively",
        ),
        (
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  decide
""",
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  intro h
  have hm : List.Mem objectClaimRegistry finiteExactRequirements := by
    simp [finiteExactRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            1,
            "Mock1Advanced prove finite-exact bucket nonempty without classical decide",
        ),
        (
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  decide
""",
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  intro h
  have hm : List.Mem completionShadowHolomorphicConsequence
      analyticBoundaryRequirements := by
    simp [analyticBoundaryRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            1,
            "Mock1Advanced prove analytic-boundary bucket nonempty constructively",
        ),
        (
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  decide
""",
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  intro h
  have hm : List.Mem regressionCardySkeleton
      diagnosticMetadataRequirements := by
    simp [diagnosticMetadataRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            1,
            "Mock1Advanced prove diagnostic bucket nonempty constructively",
        ),
        (
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  decide
""",
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  intro h
  have hm : List.Mem namedConcretePaperInstance aggregateRequirements := by
    simp [aggregateRequirements, all, evidenceClass, List.mem_cons]
  rw [h] at hm
  exact nomatch hm
""",
            1,
            "Mock1Advanced prove aggregate bucket nonempty constructively",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """  res :
    ∀ {U V : TopologicalSpace.Opens X}, U ≤ V → obj V ⟶ obj U
""",
            """  res :
    ∀ {U V : TopologicalSpace.Opens X}, U ≤ V → (obj V ⟶ obj U)
""",
            1,
            "Mock2 parenthesize the morphism codomain of the restriction field",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  have hfun :
      (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) =
        (smoothTentAutocorrelationScale T hT : ℂ) •
          (fun x : ℝ => (smoothTentAutocorrelationRaw T hT x : ℂ)) := by
    funext x
    simp only [fourierPositiveSmoothTentFunction, Pi.smul_apply,
      smul_eq_mul, Complex.ofReal_mul]
  rw [hfun, FourierTransform.fourier_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [fourier_smoothTentAutocorrelationRaw_eq_normSq T hT ξ,
    ← Complex.ofReal_mul]
""",
            """  have hfun :
      (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) =
        smoothTentAutocorrelationScale T hT •
          (fun x : ℝ => (smoothTentAutocorrelationRaw T hT x : ℂ)) := by
    funext x
    simp [fourierPositiveSmoothTentFunction]
  rw [hfun, FourierTransform.fourier_smul,
    fourier_smoothTentAutocorrelationRaw_eq_normSq T hT ξ]
  simp [smul_eq_mul, Complex.ofReal_mul]
""",
            1,
            "Mock2Advanced use the available real Fourier homogeneity instance",
        ),
        (
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    change AEStronglyMeasurable
      (fun t : ℝ =>
        (TentKernel.profile 1 t : ℂ) * (besselEnvelope x : ℂ)) volume
    exact
      ((Complex.continuous_ofReal.comp
        (TentKernel.continuous_profile 1)).mul continuous_const).aestronglyMeasurable
  normalizedKernel_bound := by
    intro x hx
    refine Filter.Eventually.of_forall ?_
    intro t
    have hprofile0 : 0 ≤ TentKernel.profile 1 t :=
      TentKernel.profile_nonneg 1 t
    have hprofile1 : TentKernel.profile 1 t ≤ 1 := by
      simp [TentKernel.profile]
    have hbessel : 0 ≤ besselEnvelope x := besselEnvelope_nonneg x
    change
      ‖(TentKernel.profile 1 t : ℂ) * (besselEnvelope x : ℂ)‖ ≤
        1 * besselEnvelope x
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hprofile0, Real.norm_of_nonneg hbessel, one_mul]
    exact mul_le_mul_of_nonneg_right hprofile1 hbessel
""",
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    simpa [profileBesselConvention, Convention.normalizedKernel] using
      ((Complex.continuous_ofReal.comp
        (TentKernel.continuous_profile 1)).mul continuous_const).aestronglyMeasurable
  normalizedKernel_bound := by
    intro x hx
    refine Filter.Eventually.of_forall ?_
    intro t
    have hprofile0 : 0 ≤ TentKernel.profile 1 t :=
      TentKernel.profile_nonneg 1 t
    have hprofile1 : TentKernel.profile 1 t ≤ 1 := by
      simp [TentKernel.profile]
    have hbessel : 0 ≤ besselEnvelope x := besselEnvelope_nonneg x
    simp only [profileBesselConvention, Convention.normalizedKernel, one_mul,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hprofile0,
      Real.norm_of_nonneg hbessel]
    exact mul_le_mul_of_nonneg_right hprofile1 hbessel
""",
            1,
            "Mock2Advanced unfold the concrete convention instead of relying on change",
        ),
        (
            """  simpa using
    (profileBesselUniformKernelEnvelope.autocorrelationFourierPositiveSmoothTent_localFloorAndKernelEnvelope
      hT hx)
""",
            """  simpa [profileBesselUniformKernelEnvelope] using
    (profileBesselUniformKernelEnvelope.autocorrelationFourierPositiveSmoothTent_localFloorAndKernelEnvelope
      hT hx)
""",
            1,
            "Mock2Advanced reduce the concrete envelope constant to one",
        ),
        (
            """  rw [hentry]
  apply Int.natAbs_eq_iff_mul_self_eq.mpr
  calc
""",
            """  rw [hentry, Int.natAbs_eq_iff_sq_eq]
  simp only [pow_two]
  calc
""",
            1,
            "Mock2Advanced use the current natAbs square equivalence",
        ),
        (
            """    twistedKloostermanSum (cancellingMultiplierPhase m n) m n =
""",
            """    twistedKloostermanSum (cancellingMultiplierPhase (c := c) m n) m n =
""",
            1,
            "Mock2Advanced expose modulus in the cancelling multiplier sum",
        ),
        (
            """    ‖twistedKloostermanSum (cancellingMultiplierPhase m n) m n‖ =
""",
            """    ‖twistedKloostermanSum (cancellingMultiplierPhase (c := c) m n) m n‖ =
""",
            1,
            "Mock2Advanced expose modulus in the cancelling multiplier norm",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """    have himSq : z.im ^ 2 = 1 - z.re ^ 2 := by
      simp only [Complex.normSq_apply] at hnormSq
      nlinarith
""",
            """    have himSq : (z : ℂ).im ^ 2 = 1 - (z : ℂ).re ^ 2 := by
      simp only [Complex.normSq_apply] at hnormSq
      nlinarith
""",
            1,
            "FunctionalAnalysis state the circular-arc norm identity on the coerced complex value",
        ),
        (
            """      have hinside : 1 - ((2 * z.re) / 2) ^ 2 = z.im ^ 2 := by
        nlinarith
""",
            """      have hinside :
          1 - ((2 * (z : ℂ).re) / 2) ^ 2 = (z : ℂ).im ^ 2 := by
        nlinarith [himSq]
""",
            1,
            "FunctionalAnalysis keep the circular-arc square calculation in the complex carrier",
        ),
        (
            """    have hnormLower : 1 ≤ z.re * z.re + z.im * z.im := by
      simpa only [Complex.normSq_apply] using hzfd.1
    have hre : z.re = -((1 : ℝ) / 2) := hz.2
""",
            """    have hnormLower :
        1 ≤ (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im := by
      simpa only [Complex.normSq_apply] using hzfd.1
    have hre : (z : ℂ).re = -((1 : ℝ) / 2) := hz.2
""",
            1,
            "FunctionalAnalysis type the left-edge norm lower bound on the complex coercion",
        ),
        (
            """    have hnormLower : 1 ≤ z.re * z.re + z.im * z.im := by
      simpa only [Complex.normSq_apply] using hzfd.1
    have hre : z.re = (1 : ℝ) / 2 := hz.2
""",
            """    have hnormLower :
        1 ≤ (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im := by
      simpa only [Complex.normSq_apply] using hzfd.1
    have hre : (z : ℂ).re = (1 : ℝ) / 2 := hz.2
""",
            1,
            "FunctionalAnalysis type the right-edge norm lower bound on the complex coercion",
        ),
        (
            """def modularTileEdgeParamToEdge (e : GammaTwoModularTileEdge) :
""",
            """noncomputable def modularTileEdgeParamToEdge (e : GammaTwoModularTileEdge) :
""",
            1,
            "FunctionalAnalysis mark the subtype edge parametrization noncomputable",
        ),
        (
            """  intro z
  have hz : (z : ℍ) ∈ modularTileEdgeSet e := z.property
  rw [← modularTileEdgeParam_range e] at hz
  rcases hz with ⟨t, ht⟩
""",
            """  intro z
  have hz : (z : ℍ) ∈ Set.range (modularTileEdgeParam e) := by
    rw [modularTileEdgeParam_range e]
    exact z.property
  rcases hz with ⟨t, ht⟩
""",
            1,
            "FunctionalAnalysis avoid dependent rewriting through the modular-edge subtype",
        ),
        (
            """      have hprod :
          0 ≤ (1 - (t : ℝ)) * ((t : ℝ) + 1) :=
        mul_nonneg (sub_nonneg.mpr t.property.2)
          (add_nonneg.mpr t.property.1)
""",
            """      have hprod :
          0 ≤ (1 - (t : ℝ)) * ((t : ℝ) + 1) := by
        apply mul_nonneg (sub_nonneg.mpr t.property.2)
        linarith [t.property.1]
""",
            1,
            "FunctionalAnalysis replace the removed add_nonneg projection lemma",
        ),
        (
            """        rw [hsqrt]
        ring
""",
            """        nlinarith [hsqrt]
""",
            1,
            "FunctionalAnalysis normalize the circular-arc square algebraically",
        ),
        (
            """  intro z
  have hz : (z : ℍ) ∈ gammaTwoActualPolygonEdgeSet e := z.property
  rw [← gammaTwoActualPolygonEdgeParam_range e] at hz
  rcases hz with ⟨t, ht⟩
""",
            """  intro z
  have hz : (z : ℍ) ∈ Set.range (gammaTwoActualPolygonEdgeParam e) := by
    rw [gammaTwoActualPolygonEdgeParam_range e]
    exact z.property
  rcases hz with ⟨t, ht⟩
""",
            1,
            "FunctionalAnalysis avoid dependent rewriting through the actual-edge subtype",
        ),
    ])


def main() -> int:
    pass117.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
