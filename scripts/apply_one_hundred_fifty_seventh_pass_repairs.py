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
            '''/-- Restriction naturality of `∇⁽q⁾ ⊗ id`, derived termwise. -/
theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  have hmap :
      (tensorRestriction (aqPresheaf E F)
          (omega1Presheaf (X := X)) hUV).comp
          (nablaTensorId P V) =
        (nablaTensorId P U).comp
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV) := by
    apply TensorProduct.ext'
    intro l m
    change
      TensorProduct.map
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV)
          (locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV)
          ((pointwiseOperator P.qPotential V l ⊗ₜ[ℂ] m) ⊗ₜ[ℂ]
            dlogFrame V) =
        ((pointwiseOperator P.qPotential U
              (locallyConstantRestriction E hUV l) ⊗ₜ[ℂ]
            locallyConstantRestriction F hUV m) ⊗ₜ[ℂ]
          dlogFrame U)
    rw [TensorProduct.map_tmul, tensorRestriction_tmul]
    have hpot := pointwiseOperator_restrict
      (X := X) P.qPotential hUV l
    change
      locallyConstantRestriction E hUV
          (pointwiseOperator P.qPotential V l) =
        pointwiseOperator P.qPotential U
          (locallyConstantRestriction E hUV l) at hpot
    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    rw [hpot, hframe]
  exact LinearMap.congr_fun hmap z
''',
            '''/-- Restriction naturality of `∇⁽q⁾ ⊗ id`, derived termwise. -/
theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  rw [nablaTensorId_localTrivialization,
    nablaTensorId_localTrivialization, tensorWithForm_apply,
    tensorWithForm_apply]
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (potentialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      potentialCoefficient P U
          ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ] dlogFrame U
  rw [tensorRestriction_tmul, potentialCoefficient_restrict,
    dlogFrame_restrict]
''',
            1,
            "Mock2 prove nabla restriction through the established coefficient naturality",
        ),
        (
            '''/-- Restriction naturality of `id ⊗ d_q`, derived termwise. -/
theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  have hmap :
      (tensorRestriction (aqPresheaf E F)
          (omega1Presheaf (X := X)) hUV).comp
          (idTensorDq P V) =
        (idTensorDq P U).comp
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV) := by
    apply TensorProduct.ext'
    intro l m
    change
      TensorProduct.map
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV)
          (locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV)
          ((l ⊗ₜ[ℂ] pointwiseOperator P.logDerivative V m) ⊗ₜ[ℂ]
            dlogFrame V) =
        ((locallyConstantRestriction E hUV l ⊗ₜ[ℂ]
            pointwiseOperator P.logDerivative U
              (locallyConstantRestriction F hUV m)) ⊗ₜ[ℂ]
          dlogFrame U)
    rw [TensorProduct.map_tmul, tensorRestriction_tmul]
    have hlog := pointwiseOperator_restrict
      (X := X) P.logDerivative hUV m
    change
      locallyConstantRestriction F hUV
          (pointwiseOperator P.logDerivative V m) =
        pointwiseOperator P.logDerivative U
          (locallyConstantRestriction F hUV m) at hlog
    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    rw [hlog, hframe]
  exact LinearMap.congr_fun hmap z
''',
            '''/-- Restriction naturality of `id ⊗ d_q`, derived termwise. -/
theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  rw [idTensorDq_localTrivialization,
    idTensorDq_localTrivialization, tensorWithForm_apply,
    tensorWithForm_apply]
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (logRadialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      logRadialCoefficient P U
          ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ] dlogFrame U
  rw [tensorRestriction_tmul, logRadialCoefficient_restrict,
    dlogFrame_restrict]
''',
            1,
            "Mock2 prove logarithmic restriction through coefficient naturality",
        ),
        (
            '''theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (nablaTensorId P V z + idTensorDq P V z) =
      nablaTensorId P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) +
        idTensorDq P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z)
  calc
    _ = tensorRestriction (aqPresheaf E F)
          (omega1Presheaf (X := X)) hUV (nablaTensorId P V z) +
        tensorRestriction (aqPresheaf E F)
          (omega1Presheaf (X := X)) hUV (idTensorDq P V z) :=
      (tensorRestriction (aqPresheaf E F)
        (omega1Presheaf (X := X)) hUV).map_add _ _
    _ = _ := by rw [nablaTensorId_restrict, idTensorDq_restrict]
''',
            '''theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  rw [Dq_apply, Dq_apply, map_add, nablaTensorId_restrict,
    idTensorDq_restrict]
''',
            1,
            "Mock2 derive full Dq restriction from the two established summands",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            '''theorem restrictionToCompatibleGaugeFamily_surjective
    {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (D : GaugeDescentSheaf X E)
''',
            '''theorem restrictionToCompatibleGaugeFamily_surjective
    {X : Type uSheafX} {E : Type uSheafE} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type uSheafX} (D : GaugeDescentSheaf X E)
''',
            1,
            "Mock2Advanced align surjectivity cover universes",
        ),
        (
            '''theorem restrictionToCompatibleGaugeFamily_bijective
    {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (D : GaugeDescentSheaf X E)
''',
            '''theorem restrictionToCompatibleGaugeFamily_bijective
    {X : Type uSheafX} {E : Type uSheafE} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type uSheafX} (D : GaugeDescentSheaf X E)
''',
            1,
            "Mock2Advanced align bijectivity cover universes",
        ),
        (
            '''noncomputable def globalGaugeFormsEquivCompatibleGaugeFamily
    {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (D : GaugeDescentSheaf X E)
''',
            '''noncomputable def globalGaugeFormsEquivCompatibleGaugeFamily
    {X : Type uSheafX} {E : Type uSheafE} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type uSheafX} (D : GaugeDescentSheaf X E)
''',
            1,
            "Mock2Advanced align the global equalizer equivalence universes",
        ),
        (
            '''noncomputable def trivialBundleGlobalSectionsEquivCompatibleGaugeFamily
    {X Fiber ι : Type*} [TopologicalSpace X]
    [AddCommGroup Fiber] [Module ℂ Fiber]
''',
            '''noncomputable def trivialBundleGlobalSectionsEquivCompatibleGaugeFamily
    {X : Type uSheafX} {Fiber : Type uSheafE}
    {ι : Type uSheafX} [TopologicalSpace X]
    [AddCommGroup Fiber] [Module ℂ Fiber]
''',
            1,
            "Mock2Advanced align the concrete global equalizer universes",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            '''  (RealSmooth.contDiffAt_upperLift hu z).of_le
    (show (2 : WithTop ℕ) ≤ (⊤ : WithTop ℕ) from le_top)
''',
            '''  (RealSmooth.contDiffAt_upperLift hu z).of_le (by exact le_top)
''',
            1,
            "FunctionalAnalysis let the smoothness order infer its native type",
        ),
        (
            '''  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (show (max 2 2 : WithTop ℕ) ≤ (⊤ : WithTop ℕ) from le_top)).iteratedFDeriv_cons
''',
            '''  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by exact le_top)).iteratedFDeriv_cons
''',
            1,
            "FunctionalAnalysis infer the native second-derivative order",
        ),
        (
            '''  have hreduce :
      heightC z * v z * physicalExponent a * (heightC z)⁻¹ * star (u z) =
        v z * physicalExponent a * star (u z) := by
    field_simp [hh]
    ring
  rw [hreduce]
  ring
''',
            '''  field_simp [hh] <;> ring
''',
            1,
            "FunctionalAnalysis close the normalized Green identity after denominator clearing",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
