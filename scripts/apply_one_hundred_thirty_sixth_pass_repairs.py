from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_fifth_pass_repairs as pass135
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
            """structure AdvancedClaimsIIActualInputDataMatrixCertificate
    (n : Nat)
    (x : Unit)
    (hn : referenceAdvancedClaimsIICompletionCertificate.padicAnalyticRange.cutoff <= n)
    (row : ResidualTableRow)
    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Prop where
""",
            """structure AdvancedClaimsIIActualInputDataMatrixCertificate
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
            "Mock1Advanced place the actual input data matrix in Type",
        ),
        (
            """theorem reference_advanced_claims_ii_actual_input_data_matrix
""",
            """noncomputable def reference_advanced_claims_ii_actual_input_data_matrix
""",
            1,
            "Mock1Advanced define the data-bearing actual input matrix",
        ),
        (
            """theorem final_synthesis_at
    {n : Nat}
""",
            """noncomputable def final_synthesis_at
    {n : Nat}
""",
            1,
            "Mock1Advanced define the data-valued microlocal final synthesis projection",
        ),
        (
            """theorem actual_input_matrix_at
    {n : Nat}
""",
            """noncomputable def actual_input_matrix_at
    {n : Nat}
""",
            1,
            "Mock1Advanced define the data-valued actual input projection",
        ),
        (
            """theorem formula_atomic_matrix_at
    {n : Nat}
""",
            """noncomputable def formula_atomic_matrix_at
    {n : Nat}
""",
            1,
            "Mock1Advanced define the data-valued atomic matrix projection",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """abbrev TensorSection (L M : LinearPresheaf.{u, v} X)
""",
            """abbrev TensorSection
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 allow tensor factors in independent value universes",
        ),
        (
            """def tensorRestriction (L M : LinearPresheaf.{u, v} X)
""",
            """def tensorRestriction
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 allow mixed-universe tensor restrictions",
        ),
        (
            """@[simp] theorem tensorRestriction_tmul (L M : LinearPresheaf X)
""",
            """@[simp] theorem tensorRestriction_tmul
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize the pure-tensor restriction lemma",
        ),
        (
            """theorem tensorRestriction_id (L M : LinearPresheaf X)
""",
            """theorem tensorRestriction_id
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize tensor restriction identity",
        ),
        (
            """theorem tensorRestriction_comp (L M : LinearPresheaf X)
""",
            """theorem tensorRestriction_comp
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize tensor restriction composition",
        ),
        (
            """def tensorPresheaf (L M : LinearPresheaf.{u, v} X) :
    LinearPresheaf.{u, v} X where
  obj U := ModuleCat.of.{max u v, 0} ℂ (TensorSection L M U)
""",
            """def tensorPresheaf
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X) :
    LinearPresheaf.{u, max v w} X where
  obj U := ModuleCat.of.{max u (max v w), 0} ℂ (TensorSection L M U)
""",
            1,
            "Mock2 place a mixed-universe tensor presheaf in the maximum value universe",
        ),
        (
            """@[simp] theorem tensorPresheaf_obj (L M : LinearPresheaf X)
""",
            """@[simp] theorem tensorPresheaf_obj
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize tensor object evaluation",
        ),
        (
            """@[simp] theorem tensorPresheaf_res_hom (L M : LinearPresheaf X)
""",
            """@[simp] theorem tensorPresheaf_res_hom
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize tensor restriction hom evaluation",
        ),
        (
            """@[simp] theorem tensorPresheaf_res_tmul (L M : LinearPresheaf X)
""",
            """@[simp] theorem tensorPresheaf_res_tmul
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize tensor restriction on pure tensors",
        ),
        (
            """noncomputable def tensor_fibre_has_module (L M : LinearPresheaf X)
""",
            """noncomputable def tensor_fibre_has_module
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize the tensor fibre module witness",
        ),
        (
            """theorem tensor_restriction_isLinear (L M : LinearPresheaf X)
""",
            """theorem tensor_restriction_isLinear
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize the tensor restriction linearity witness",
        ),
        (
            """structure GenuineTensorCertificate (L M : LinearPresheaf X) : Prop where
""",
            """structure GenuineTensorCertificate
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X) : Prop where
""",
            1,
            "Mock2 generalize the genuine tensor certificate",
        ),
        (
            """theorem genuineTensor_certificate (L M : LinearPresheaf X) :
""",
            """theorem genuineTensor_certificate
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X) :
""",
            1,
            "Mock2 generalize the genuine tensor certificate constructor",
        ),
        (
            """    TensorSheafBoundaryCertificate E F := by
""",
            """    TensorSheafBoundaryCertificate (X := X) E F := by
""",
            1,
            "Mock2 determine the base space of the tensor boundary certificate",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  by_cases hi : i = i₀
  · simp only [hi, if_true]
  · simpa only [hi, if_false] using hf i
""",
            """  by_cases hi : i = i₀
  · simp [hi]
  · simpa only [hi, if_false] using hf i
""",
            1,
            "Mock2Advanced close the zero branch of complement nonnegativity",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """    simpa [gammaTwoTopologicalTruncation] using
      hn.trans (hstage.trans (Set.image_mono hmono))
""",
            """    have hfloor :
        ⌊(((n + 2 : ℕ) : ℝ))⌋₊ = n + 2 := by
      norm_num
    simpa [gammaTwoTopologicalTruncation, hfloor] using
      hn.trans (hstage.trans (Set.image_mono hmono))
""",
            1,
            "FunctionalAnalysis normalize the natural stage recovered from a real height",
        ),
        (
            """def upperLift (u : ℍ → ℂ) : ℂ → ℂ :=
""",
            """noncomputable def upperLift (u : ℍ → ℂ) : ℂ → ℂ :=
""",
            1,
            "FunctionalAnalysis mark the complex chart pullback noncomputable",
        ),
    ])


def main() -> int:
    pass135.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
