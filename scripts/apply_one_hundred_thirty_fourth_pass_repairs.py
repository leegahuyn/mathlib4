from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_third_pass_repairs as pass133
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
            """structure AdvancedClaimsIISectionwiseFormulaAtomicBridgeCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Prop where
""",
            """structure AdvancedClaimsIISectionwiseFormulaAtomicBridgeCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Type where
""",
            1,
            "Mock1Advanced place the sectionwise formula bridge in Type",
        ),
        (
            """theorem reference_advanced_claims_ii_sectionwise_formula_atomic_bridge
""",
            """noncomputable def reference_advanced_claims_ii_sectionwise_formula_atomic_bridge
""",
            1,
            "Mock1Advanced define the data-bearing sectionwise formula bridge",
        ),
        (
            """structure AdvancedClaimsIIObjectiveFinalSynthesisCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Prop where
""",
            """structure AdvancedClaimsIIObjectiveFinalSynthesisCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Type where
""",
            1,
            "Mock1Advanced place the objective final synthesis in Type",
        ),
        (
            """theorem reference_advanced_claims_ii_objective_final_synthesis
""",
            """noncomputable def reference_advanced_claims_ii_objective_final_synthesis
""",
            1,
            "Mock1Advanced define the data-bearing objective final synthesis",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """theorem locallyConstantTensorSheaf_isSheaf (E F : ModuleCat ℂ) :
    IsSheafLike (locallyConstantTensorSheaf E F).toPresheafLike :=
  Definition12Tensor.locallyConstantLinearPresheaf_isSheaf
    (X := X) (ModuleCat.of ℂ (TensorProduct ℂ E F))
""",
            """theorem locallyConstantTensorSheaf_isSheaf (E F : ModuleCat ℂ) :
    IsSheafLike
      ((locallyConstantTensorSheaf (X := X) E F).toPresheafLike) :=
  Definition12Tensor.locallyConstantLinearPresheaf_isSheaf
    (X := X) (ModuleCat.of ℂ (TensorProduct ℂ E F))
""",
            1,
            "Mock2 determine the base space in tensor-sheaf sheafness",
        ),
        (
            """structure LocalTrivializationComparison (E F : ModuleCat ℂ) where
  app :
    ∀ U : TopologicalSpace.Opens X,
      (locallyConstantPointwiseTensor E F).obj U ≃ₗ[ℂ]
        (locallyConstantTensorSheaf E F).obj U
  app_tmul :
    ∀ (U : TopologicalSpace.Opens X)
      (s : LocallyConstant U E) (t : LocallyConstant U F) (x : U),
      app U (s ⊗ₜ[ℂ] t) x = s x ⊗ₜ[ℂ] t x
""",
            """structure LocalTrivializationComparison (E F : ModuleCat ℂ) where
  app :
    ∀ U : TopologicalSpace.Opens X,
      (locallyConstantPointwiseTensor (X := X) E F).obj U ≃ₗ[ℂ]
        (locallyConstantTensorSheaf (X := X) E F).obj U
  app_tmul :
    ∀ (U : TopologicalSpace.Opens X)
      (s : LocallyConstant U E) (t : LocallyConstant U F) (x : U),
      ((app U (s ⊗ₜ[ℂ] t) :
          LocallyConstant U (TensorProduct ℂ E F)).toFun x) =
        s x ⊗ₜ[ℂ] t x
""",
            1,
            "Mock2 expose the locally constant carrier in the comparison field",
        ),
        (
            """def toLinearPresheafEquiv (H : LocalTrivializationComparison E F) :
    LinearPresheafEquiv (locallyConstantPointwiseTensor E F)
      (locallyConstantTensorSheaf E F) where
""",
            """def toLinearPresheafEquiv (H : LocalTrivializationComparison E F) :
    LinearPresheafEquiv
      (locallyConstantPointwiseTensor (X := X) E F)
      (locallyConstantTensorSheaf (X := X) E F) where
""",
            1,
            "Mock2 determine both base spaces in the comparison equivalence",
        ),
        (
            """theorem pointwiseTensor_isSheaf (H : LocalTrivializationComparison E F) :
    IsSheafLike (locallyConstantPointwiseTensor E F).toPresheafLike :=
  H.toLinearPresheafEquiv.isSheaf_of_equiv
    (locallyConstantTensorSheaf_isSheaf E F)
""",
            """theorem pointwiseTensor_isSheaf (H : LocalTrivializationComparison E F) :
    IsSheafLike
      ((locallyConstantPointwiseTensor (X := X) E F).toPresheafLike) :=
  H.toLinearPresheafEquiv.isSheaf_of_equiv
    (locallyConstantTensorSheaf_isSheaf (X := X) E F)
""",
            1,
            "Mock2 determine the base space in conditional tensor sheafness",
        ),
        (
            """structure TensorSheafBoundaryCertificate (E F : ModuleCat ℂ) : Prop where
  tensor_target_isSheaf :
    IsSheafLike (locallyConstantTensorSheaf E F).toPresheafLike
""",
            """structure TensorSheafBoundaryCertificate (E F : ModuleCat ℂ) : Prop where
  tensor_target_isSheaf :
    IsSheafLike
      ((locallyConstantTensorSheaf (X := X) E F).toPresheafLike)
""",
            1,
            "Mock2 determine the base space in the tensor boundary certificate",
        ),
        (
            """theorem tensorSheafBoundary_certificate (E F : ModuleCat ℂ) :
    TensorSheafBoundaryCertificate E F := by
""",
            """theorem tensorSheafBoundary_certificate (E F : ModuleCat ℂ) :
    TensorSheafBoundaryCertificate (X := X) E F := by
""",
            1,
            "Mock2 determine the base space in the tensor boundary constructor",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  exact setIntegral_eq_variableTruncation
    mu F (truncatedFundamentalDomain F)
    (fun _ : PUnit => density) (fun _ => Y)
    (fun _ => truncatedFundamentalDomain_subset F Y)
    (fun _ x hx => hsupport x (fun hxK => hx (hKY hxK)))
    PUnit.unit
""",
            """  exact setIntegral_eq_variableTruncation
    mu F (truncatedFundamentalDomain F)
    (fun _ : Unit => density) (fun _ => Y)
    (fun _ => truncatedFundamentalDomain_subset F Y)
    (fun _ x hx => hsupport x (fun hxK => hx (hKY hxK)))
    Unit.unit
""",
            1,
            "Mock2Advanced use the concrete Unit universe for the one-parameter family",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  have hsqrt :
      (Real.sqrt (1 - ((t : ℝ) / 2) ^ 2)) ^ 2 =
        1 - ((t : ℝ) / 2) ^ 2 :=
    Real.sq_sqrt hinside
  change
    Real.sqrt (1 - ((t : ℝ) / 2) ^ 2) =
      gammaTwoCuspLevel Y *
        ((gammaTwoCornerLowerLeft (e, .circularArc) q *
              ((t : ℝ) / 2) +
            gammaTwoCornerLowerRight (e, .circularArc) q) ^ 2 +
          gammaTwoCornerLowerLeft (e, .circularArc) q ^ 2 *
            (Real.sqrt (1 - ((t : ℝ) / 2) ^ 2)) ^ 2) at hcleared
  nlinarith
""",
            """  have hsqrt :
      (Real.sqrt (1 - ((t : ℝ) / 2) ^ 2)) ^ 2 =
        1 - ((t : ℝ) / 2) ^ 2 :=
    Real.sq_sqrt hinside
  change
    Real.sqrt (1 - ((t : ℝ) / 2) ^ 2) =
      gammaTwoCuspLevel Y *
        ((gammaTwoCornerLowerLeft (e, .circularArc) q *
              ((t : ℝ) / 2) +
            gammaTwoCornerLowerRight (e, .circularArc) q) ^ 2 +
          gammaTwoCornerLowerLeft (e, .circularArc) q ^ 2 *
            (Real.sqrt (1 - ((t : ℝ) / 2) ^ 2)) ^ 2) at hcleared
  have hquad :
      (gammaTwoCornerLowerLeft (e, .circularArc) q *
              ((t : ℝ) / 2) +
            gammaTwoCornerLowerRight (e, .circularArc) q) ^ 2 +
          gammaTwoCornerLowerLeft (e, .circularArc) q ^ 2 *
            (Real.sqrt (1 - ((t : ℝ) / 2) ^ 2)) ^ 2 =
        gammaTwoCornerLowerLeft (e, .circularArc) q ^ 2 +
          gammaTwoCornerLowerRight (e, .circularArc) q ^ 2 +
          gammaTwoCornerLowerLeft (e, .circularArc) q *
            gammaTwoCornerLowerRight (e, .circularArc) q * (t : ℝ) := by
    rw [hsqrt]
    ring
  rw [hquad] at hcleared
  have hsq := congrArg (fun y : ℝ => y ^ 2) hcleared
  nlinarith [hsqrt, hsq]
""",
            1,
            "FunctionalAnalysis square the cleared circular-height identity explicitly",
        ),
    ])


def main() -> int:
    pass133.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
