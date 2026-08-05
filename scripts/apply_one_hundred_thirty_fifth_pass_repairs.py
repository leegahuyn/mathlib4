from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_fourth_pass_repairs as pass134
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
            """theorem formula_atomic_bridge_at
    {n : Nat}
""",
            """noncomputable def formula_atomic_bridge_at
    {n : Nat}
""",
            1,
            "Mock1Advanced define the data-valued formula bridge projection",
        ),
        (
            """structure AdvancedClaimsIIFormulaAtomicItemMatrixCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Prop where
""",
            """structure AdvancedClaimsIIFormulaAtomicItemMatrixCertificate
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
            "Mock1Advanced place the formula atomic item matrix in Type",
        ),
        (
            """theorem reference_advanced_claims_ii_formula_atomic_item_matrix
""",
            """noncomputable def reference_advanced_claims_ii_formula_atomic_item_matrix
""",
            1,
            "Mock1Advanced define the data-bearing formula atomic item matrix",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """def toLinearPresheafEquiv (H : LocalTrivializationComparison E F) :
""",
            """def toLinearPresheafEquiv
    (H : LocalTrivializationComparison (X := X) E F) :
""",
            1,
            "Mock2 determine the base space of the local comparison equivalence",
        ),
        (
            """theorem pointwiseTensor_isSheaf (H : LocalTrivializationComparison E F) :
""",
            """theorem pointwiseTensor_isSheaf
    (H : LocalTrivializationComparison (X := X) E F) :
""",
            1,
            "Mock2 determine the base space of conditional pointwise sheafness",
        ),
        (
            """      pointwiseTensorComparison E F U (s ⊗ₜ[ℂ] t) x =
""",
            """      pointwiseTensorComparison (X := X) E F U (s ⊗ₜ[ℂ] t) x =
""",
            1,
            "Mock2 determine the base space in the pure-tensor comparison field",
        ),
        (
            """      (z : (locallyConstantPointwiseTensor E F).obj V),
      pointwiseTensorComparison E F U
          ((locallyConstantPointwiseTensor E F).res hUV z) =
        (locallyConstantTensorSheaf E F).res hUV
          (pointwiseTensorComparison E F V z)
""",
            """      (z : (locallyConstantPointwiseTensor (X := X) E F).obj V),
      pointwiseTensorComparison (X := X) E F U
          ((locallyConstantPointwiseTensor (X := X) E F).res hUV z) =
        (locallyConstantTensorSheaf (X := X) E F).res hUV
          (pointwiseTensorComparison (X := X) E F V z)
""",
            1,
            "Mock2 determine every base space in the comparison naturality field",
        ),
        (
            """    ∀ H : LocalTrivializationComparison E F,
      IsSheafLike (locallyConstantPointwiseTensor E F).toPresheafLike
""",
            """    ∀ H : LocalTrivializationComparison (X := X) E F,
      IsSheafLike
        ((locallyConstantPointwiseTensor (X := X) E F).toPresheafLike)
""",
            1,
            "Mock2 determine the base space in the conditional boundary field",
        ),
        (
            """    TensorSheafBoundaryCertificate (X := X) E F := by
  exact
    { tensor_target_isSheaf := locallyConstantTensorSheaf_isSheaf E F
      comparison_on_pure_tensors :=
        pointwiseTensorComparison_tmul_apply E F
      comparison_natural := pointwiseTensorComparison_naturality_apply E F
""",
            """    TensorSheafBoundaryCertificate E F := by
  exact
    { tensor_target_isSheaf := locallyConstantTensorSheaf_isSheaf (X := X) E F
      comparison_on_pure_tensors :=
        pointwiseTensorComparison_tmul_apply (X := X) E F
      comparison_natural :=
        pointwiseTensorComparison_naturality_apply (X := X) E F
""",
            1,
            "Mock2 construct the tensor boundary certificate with explicit base-space calls",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  apply not_differentiableAt_abs_zero
  simpa only [sub_sub_cancel_left] using
    (differentiableAt_const (c := T)).sub hsub
""",
            """  apply not_differentiableAt_abs_zero
  have hdiff :
      DifferentiableAt ℝ (fun t : ℝ => T - (T - |t|)) 0 :=
    (differentiableAt_const (c := T)).sub hsub
  convert hdiff using 1
  funext t
  ring
""",
            1,
            "Mock2Advanced recover differentiability of abs by explicit function extensionality",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  refine ⟨a • z, ⟨ha, ?_⟩, ?_⟩
  · simpa only [gammaTwoQuotientMk_smul] using hx
  · exact gammaTwoQuotientMk_smul a z
""",
            """  refine ⟨a • z, ⟨ha, ?_⟩, ?_⟩
  · change gammaTwoQuotientMk (a • z) ∈ K
    simpa only [gammaTwoQuotientMk_smul] using hx
  · exact gammaTwoQuotientMk_smul a z
""",
            1,
            "FunctionalAnalysis expose quotient-preimage membership before orbit simplification",
        ),
    ])


def main() -> int:
    pass134.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
