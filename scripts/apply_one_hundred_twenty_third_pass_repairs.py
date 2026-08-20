from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twenty_second_pass_repairs as pass122
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
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass]
""",
            """  cases r <;>
    simp_all [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass] <;>
    decide
""",
            1,
            "Mock1Advanced close the residual finite enum membership goals",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """theorem locallyConstantLinearPresheaf_isSheaf (E : ModuleCat.{v} ℂ) :
    IsSheafLike (locallyConstantLinearPresheaf E).toPresheafLike := by
  change IsSheafLike (LocallyConstantValueSheaf.presheaf E)
  exact LocallyConstantValueSheaf.isSheaf
""",
            """theorem locallyConstantLinearPresheaf_isSheaf (E : ModuleCat.{v} ℂ) :
    IsSheafLike
      ((locallyConstantLinearPresheaf (X := X) E).toPresheafLike) := by
  change IsSheafLike (LocallyConstantValueSheaf.presheaf (X := X) E)
  exact LocallyConstantValueSheaf.isSheaf
""",
            1,
            "Mock2 determine the base space in the locally constant sheaf theorem",
        ),
        (
            """@[simp] theorem lqLinearPresheaf_res_apply
    (D : Definition11.AnalyticData V)
    {U W : TopologicalSpace.Opens Definition11.RadiusBase}
    (hUW : U ≤ W) (s : (lqLinearPresheaf D).obj W) (x : U) :
    (lqLinearPresheaf D).res hUW s x = s ⟨x.1, hUW x.2⟩ :=
  rfl
""",
            """@[simp] theorem lqLinearPresheaf_res_apply
    (D : Definition11.AnalyticData V)
    {U W : TopologicalSpace.Opens Definition11.RadiusBase}
    (hUW : U ≤ W) (s : (lqLinearPresheaf D).obj W) (x : U) :
    (((lqLinearPresheaf D).res hUW s :
        LocallyConstant U D.solutionSpace).toFun x) =
      (s : LocallyConstant W D.solutionSpace).toFun ⟨x.1, hUW x.2⟩ :=
  rfl
""",
            1,
            "Mock2 expose the locally constant carriers in the Lq restriction formula",
        ),
        (
            """  map_smul' c x := by
    ring
""",
            """  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    ring
""",
            1,
            "Mock2 simplify linear evaluation before proving homogeneous scalar compatibility",
        ),
        (
            """@[simp] theorem linearMmockPresheaf_res_apply (A : Set ℂ)
    {U V : TopologicalSpace.Opens Mmock.RadiusBase} (hUV : U ≤ V)
    (s : (linearMmockPresheaf A).obj V) (x : U) :
    (linearMmockPresheaf A).res hUV s x = s ⟨x.1, hUV x.2⟩ :=
  rfl

 theorem mmock_fibre_has_module""",
            """@[simp] theorem linearMmockPresheaf_res_apply (A : Set ℂ)
    {U V : TopologicalSpace.Opens Mmock.RadiusBase} (hUV : U ≤ V)
    (s : (linearMmockPresheaf A).obj V) (x : U) :
    (((linearMmockPresheaf A).res hUV s :
        LocallyConstant U (variationModule A)).toFun x) =
      (s : LocallyConstant V (variationModule A)).toFun ⟨x.1, hUV x.2⟩ :=
  rfl

 theorem mmock_fibre_has_module""",
            0,
            "unused guard",
        ),
    ])

    # The source has no leading space before the class-valued declaration; keep
    # this replacement separate so the exact matcher remains auditable.
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """@[simp] theorem linearMmockPresheaf_res_apply (A : Set ℂ)
    {U V : TopologicalSpace.Opens Mmock.RadiusBase} (hUV : U ≤ V)
    (s : (linearMmockPresheaf A).obj V) (x : U) :
    (linearMmockPresheaf A).res hUV s x = s ⟨x.1, hUV x.2⟩ :=
  rfl

 theorem mmock_fibre_has_module""".replace("\n theorem", "\ntheorem"),
            """@[simp] theorem linearMmockPresheaf_res_apply (A : Set ℂ)
    {U V : TopologicalSpace.Opens Mmock.RadiusBase} (hUV : U ≤ V)
    (s : (linearMmockPresheaf A).obj V) (x : U) :
    (((linearMmockPresheaf A).res hUV s :
        LocallyConstant U (variationModule A)).toFun x) =
      (s : LocallyConstant V (variationModule A)).toFun ⟨x.1, hUV x.2⟩ :=
  rfl

noncomputable def mmock_fibre_has_module""",
            1,
            "Mock2 expose Mmock restriction carriers and make the module witness a definition",
        ),
        (
            """theorem linearMmockPresheaf_isSheaf (A : Set ℂ) :
    IsSheafLike (linearMmockPresheaf A).toPresheafLike :=
  locallyConstantLinearPresheaf_isSheaf (variationModule A)
""",
            """theorem linearMmockPresheaf_isSheaf (A : Set ℂ) :
    IsSheafLike (linearMmockPresheaf A).toPresheafLike :=
  Definition12Tensor.locallyConstantLinearPresheaf_isSheaf
    (X := Mmock.RadiusBase) (variationModule A)
""",
            1,
            "Mock2 qualify the inherited locally constant sheaf theorem",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    simp only [profileBesselConvention, Convention.normalizedKernel, one_mul]
    change AEStronglyMeasurable
      (fun t : ℝ =>
        (TentKernel.profile 1 t : ℂ) * (besselEnvelope x : ℂ)) volume
    simpa only [Function.comp_apply, Pi.mul_apply] using
      ((Complex.continuous_ofReal.comp
        (TentKernel.continuous_profile 1)).mul continuous_const).aestronglyMeasurable
""",
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    simp only [profileBesselConvention, Convention.normalizedKernel, one_mul]
    change AEStronglyMeasurable
      (fun t : ℝ =>
        (TentKernel.profile 1 t : ℂ) * (besselEnvelope x : ℂ)) volume
    have hprofile : Integrable
        (fun t : ℝ => (TentKernel.profile 1 t : ℂ)) volume :=
      (TentKernel.integrable_profile (by norm_num)).ofReal
    have hkernel : Integrable
        (fun t : ℝ =>
          (TentKernel.profile 1 t : ℂ) * (besselEnvelope x : ℂ)) volume := by
      simpa only [mul_comm] using
        hprofile.const_mul (besselEnvelope x : ℂ)
    exact hkernel.aestronglyMeasurable
""",
            1,
            "Mock2Advanced derive kernel measurability from integrability in the exact volume instance",
        ),
        (
            """  have hnatL : Int.natAbs (L 1 1) = 1 := by omega
  have hnatR : Int.natAbs (R 0 0) = 1 := by omega
""",
            """  have hnatL : Int.natAbs (L 1 1) = 1 := by
    nlinarith [hnatLsq]
  have hnatR : Int.natAbs (R 0 0) = 1 := by
    nlinarith [hnatRsq]
""",
            1,
            "Mock2Advanced solve the nonlinear natural unit equations with nlinarith",
        ),
        (
            """  scatteringNormalization : ℝ≥0
""",
            """  scatteringNormalization : NNReal
""",
            1,
            "Mock2Advanced use the explicit nonnegative-real type name in the structure field",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """      apply Complex.ext
      · simp [GammaTwoModularTileEdge.pairingMatrix,
          GammaTwoModularTileEdge.paired,
          GammaTwoModularTileEdge.pairedParameter,
          modularTileEdgeParam, modularCircularArcParam, hnormSq, hden]
      · simp [GammaTwoModularTileEdge.pairingMatrix,
          GammaTwoModularTileEdge.paired,
          GammaTwoModularTileEdge.pairedParameter,
          modularTileEdgeParam, modularCircularArcParam, hnormSq, hden]
""",
            """      apply Complex.ext
      · simp [GammaTwoModularTileEdge.pairingMatrix,
          GammaTwoModularTileEdge.paired,
          GammaTwoModularTileEdge.pairedParameter,
          modularTileEdgeParam, modularCircularArcParam, hnormSq, hden]
        ring
      · simp [GammaTwoModularTileEdge.pairingMatrix,
          GammaTwoModularTileEdge.paired,
          GammaTwoModularTileEdge.pairedParameter,
          modularTileEdgeParam, modularCircularArcParam, hnormSq, hden]
        congr 1
        ring
""",
            1,
            "FunctionalAnalysis normalize both circular-edge pairing coordinates",
        ),
        (
            """def gammaTwoModularHeightEnvelope (z : ℍ) : ℝ :=
""",
            """noncomputable def gammaTwoModularHeightEnvelope (z : ℍ) : ℝ :=
""",
            1,
            "FunctionalAnalysis mark the real-division height envelope noncomputable",
        ),
        (
            """    rw [volume_eq_prod, Measure.prod_prod]
""",
            """    rw [Measure.volume_eq_prod, Measure.prod_prod]
""",
            1,
            "FunctionalAnalysis qualify the complex volume product theorem",
        ),
        (
            """  · exact
      (measurableSet_eq Complex.measurable_im measurable_const).nullMeasurableSet
""",
            """  · exact
      ((measurableSet_singleton b).preimage
        Complex.measurable_im).nullMeasurableSet
""",
            1,
            "FunctionalAnalysis prove horizontal-line measurability as a singleton preimage",
        ),
    ])


def main() -> int:
    pass122.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
