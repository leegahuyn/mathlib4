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
            """theorem localCoefficient_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqPresheaf E F).res hUV (localCoefficient P V z) =
      localCoefficient P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV (localCoefficient P V z) =
      localCoefficient P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z)
  rw [localCoefficient_apply, LinearMap.map_add,
    logRadialCoefficient_restrict, potentialCoefficient_restrict,
    localCoefficient_apply]
""",
            """theorem localCoefficient_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqPresheaf E F).res hUV (localCoefficient P V z) =
      localCoefficient P U ((aqPresheaf E F).res hUV z) := by
  have hmap :
      (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV).comp
          (localCoefficient P V) =
        (localCoefficient P U).comp
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV) := by
    apply TensorProduct.ext'
    intro l m
    simp [localCoefficient_tmul, tensorRestriction_tmul,
      pointwiseOperator_restrict]
  exact LinearMap.congr_fun hmap z
""",
            1,
            "Mock2 prove local coefficient naturality on pure tensors",
        ),
        (
            """theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (potentialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      potentialCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, potentialCoefficient_restrict,
    dlogFrame_restrict]
""",
            """theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
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
    simp [nablaTensorId_tmul, tensorRestriction_tmul,
      potentialCoefficient_tmul, pointwiseOperator_restrict,
      dlogFrame_restrict]
  exact LinearMap.congr_fun hmap z
""",
            1,
            "Mock2 prove nabla tensor naturality on pure tensors",
        ),
        (
            """theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (logRadialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      logRadialCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, logRadialCoefficient_restrict,
    dlogFrame_restrict]
""",
            """theorem idTensorDq_restrict {E F : ModuleCat ℂ}
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
    simp [idTensorDq_tmul, tensorRestriction_tmul,
      logRadialCoefficient_tmul, pointwiseOperator_restrict,
      dlogFrame_restrict]
  exact LinearMap.congr_fun hmap z
""",
            1,
            "Mock2 prove logarithmic tensor naturality on pure tensors",
        ),
        (
            """theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (localCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      localCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, localCoefficient_restrict, dlogFrame_restrict]
""",
            """theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  rw [Dq_eq_nablaTensorId_add_idTensorDq,
    Dq_eq_nablaTensorId_add_idTensorDq, LinearMap.map_add,
    nablaTensorId_restrict, idTensorDq_restrict]
""",
            1,
            "Mock2 derive full derivative naturality from the two summands",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """theorem exterior_analytic :
    AnalyticOn ℂ exterior
      (exteriorVariableDomain innerRadius outerRadius) := by
  simpa only [exterior] using
    (analyticOn_id : AnalyticOn ℂ (fun w : ℂ ↦ w)
      (exteriorVariableDomain innerRadius outerRadius))
""",
            """theorem exterior_analytic :
    AnalyticOn ℂ exterior
      (exteriorVariableDomain innerRadius outerRadius) := by
  change AnalyticOn ℂ (fun w : ℂ => w)
    (exteriorVariableDomain innerRadius outerRadius)
  exact analyticOn_id
""",
            1,
            "Mock2Advanced expose the exterior identity function",
        ),
        (
            """theorem psi_analytic :
    AnalyticOn ℂ psi sample := by
  simpa only [psi, inside] using inside_analytic
""",
            """theorem psi_analytic :
    AnalyticOn ℂ psi sample := by
  change AnalyticOn ℂ (fun q : ℂ => q⁻¹) sample
  exact inside_analytic
""",
            1,
            "Mock2Advanced expose the concrete psi inverse",
        ),
        (
            """theorem shadow_analytic :
    AnalyticOn ℂ shadow sample := by
  simpa only [shadow, inside] using inside_analytic
""",
            """theorem shadow_analytic :
    AnalyticOn ℂ shadow sample := by
  change AnalyticOn ℂ (fun q : ℂ => q⁻¹) sample
  exact inside_analytic
""",
            1,
            "Mock2Advanced expose the concrete shadow inverse",
        ),
        (
            """theorem correction_analytic :
    AnalyticOn ℂ correction sample := by
  simpa only [correction] using
    ((analyticOn_id : AnalyticOn ℂ (fun q : ℂ ↦ q) sample).pow 2)
""",
            """theorem correction_analytic :
    AnalyticOn ℂ correction sample := by
  change AnalyticOn ℂ (fun q : ℂ => q ^ 2) sample
  exact (analyticOn_id : AnalyticOn ℂ (fun q : ℂ => q) sample).pow 2
""",
            1,
            "Mock2Advanced expose the concrete polynomial correction",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        ("hu.contDiffAt_upperLift", "RealSmooth.contDiffAt_upperLift hu", 10,
          "FunctionalAnalysis call upper-lift smoothness explicitly for hu"),
        ("hv.contDiffAt_upperLift", "RealSmooth.contDiffAt_upperLift hv", 2,
          "FunctionalAnalysis call upper-lift smoothness explicitly for hv"),
        ("hf.contDiffAt_upperLift", "RealSmooth.contDiffAt_upperLift hf", 6,
          "FunctionalAnalysis call upper-lift smoothness explicitly for hf"),
        ("hu.contDiffAt_two_upperLift", "RealSmooth.contDiffAt_two_upperLift hu", 2,
          "FunctionalAnalysis call second upper-lift smoothness explicitly for hu"),
        ("hv.contDiffAt_two_upperLift", "RealSmooth.contDiffAt_two_upperLift hv", 1,
          "FunctionalAnalysis call second upper-lift smoothness explicitly for hv"),
        ("hf.contDiffAt_two_upperLift", "RealSmooth.contDiffAt_two_upperLift hf", 1,
          "FunctionalAnalysis call second upper-lift smoothness explicitly for hf"),
        ("hf.d1_constDirection", "RealSmooth.d1_constDirection hf", 6,
          "FunctionalAnalysis call directional smoothness explicitly"),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
