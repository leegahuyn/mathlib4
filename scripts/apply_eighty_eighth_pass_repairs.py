from __future__ import annotations

from pathlib import Path

import apply_eighty_seventh_pass_repairs as pass87
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """      (AdvancedClaimsIIRlfFormulaProjectionCertificate.coeff_eq_object_at
        reference_advanced_claims_ii_rlf_formula_projection n)
""",
            """      (reference_advanced_claims_ii_rlf_formula_projection.coeff_eq_object n)
""",
            "Mock1Advanced use the existing coefficient projection field directly",
        ),
        (
            """      (AdvancedClaimsIIRlfFormulaProjectionCertificate.coefficientAt_eq_object_at
        reference_advanced_claims_ii_rlf_formula_projection n)
""",
            """      (reference_advanced_claims_ii_rlf_formula_projection.coefficientAt_eq_object n)
""",
            "Mock1Advanced use the existing coefficientAt projection field directly",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """theorem potential_action_assoc (C : Core U) (s : LocalFramedSection U) :
    matrixVectorWedge C.potential (matrixVectorWedge C.potential s) =
      matrixVectorWedge (matrixWedge C.potential C.potential) s := by
  funext i
  apply ChartForm.ext <;>
    simp [matrixVectorWedge, matrixWedge, Fin.sum_univ_two,
      wedge_add_left, wedge_add_right] <;> abel_nf
""",
        """theorem potential_action_assoc (C : Core U) (s : LocalFramedSection U) :
    matrixVectorWedge C.potential (matrixVectorWedge C.potential s) =
      matrixVectorWedge (matrixWedge C.potential C.potential) s := by
  funext i
  apply ChartForm.ext <;>
    simp [matrixVectorWedge, matrixWedge, Fin.sum_univ_two,
      wedge_add_left, wedge_add_right] <;> ring
""",
        1,
        "Mock2 normalize polynomial matrix-action associativity with ring",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """        exact (M.core_equivariant v hv).isAE μ)
""",
        """        exact (M.core_equivariant v hv).isAE)
""",
        2,
        "Mock2Advanced keep the target measure implicit in isAE",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """theorem gammaTwoToSL2Real_isClosedEmbedding :
    Topology.IsClosedEmbedding gammaTwoToSL2Real := by
  convert
    (Matrix.SpecialLinearGroup.isClosedEmbedding_mapGLInt
      (n := Fin 2)).comp
      ((isClosed_discrete (GammaTwo : Set SL(2, ℤ))).isClosedEmbedding_subtypeVal)
    using 1 <;> rfl
""",
        """theorem gammaTwoToSL2Real_isClosedEmbedding :
    Topology.IsClosedEmbedding gammaTwoToSL2Real := by
  change Topology.IsClosedEmbedding
    (fun γ : GammaTwo =>
      Matrix.SpecialLinearGroup.map (algebraMap ℤ ℝ) (γ : SL(2, ℤ)))
  exact
    Real.isClosedEmbedding_intCast.specialLinearGroup_map.comp
      ((isClosed_discrete (GammaTwo : Set SL(2, ℤ))).isClosedEmbedding_subtypeVal)
""",
        1,
        "FunctionalAnalysis compose the two closed SL embeddings directly",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass87.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
