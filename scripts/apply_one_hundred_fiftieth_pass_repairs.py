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
            """    apply TensorProduct.ext'
    intro l m
    simp [localCoefficient_tmul, tensorRestriction_tmul,
      pointwiseOperator_restrict]
""",
            """    apply TensorProduct.ext'
    intro l m
    simp only [LinearMap.comp_apply, localCoefficient_tmul,
      LinearMap.map_add, tensorRestriction_tmul]
    rw [pointwiseOperator_restrict, pointwiseOperator_restrict]
""",
            1,
            "Mock2 unfold linear-map composition before local coefficient naturality",
        ),
        (
            """    apply TensorProduct.ext'
    intro l m
    simp [nablaTensorId_tmul, tensorRestriction_tmul,
      potentialCoefficient_tmul, pointwiseOperator_restrict,
      dlogFrame_restrict]
""",
            """    apply TensorProduct.ext'
    intro l m
    simp only [LinearMap.comp_apply, nablaTensorId_tmul,
      tensorRestriction_tmul, potentialCoefficient_tmul]
    rw [pointwiseOperator_restrict, dlogFrame_restrict]
""",
            1,
            "Mock2 unfold composition before nabla tensor naturality",
        ),
        (
            """    apply TensorProduct.ext'
    intro l m
    simp [idTensorDq_tmul, tensorRestriction_tmul,
      logRadialCoefficient_tmul, pointwiseOperator_restrict,
      dlogFrame_restrict]
""",
            """    apply TensorProduct.ext'
    intro l m
    simp only [LinearMap.comp_apply, idTensorDq_tmul,
      tensorRestriction_tmul, logRadialCoefficient_tmul]
    rw [pointwiseOperator_restrict, dlogFrame_restrict]
""",
            1,
            "Mock2 unfold composition before logarithmic tensor naturality",
        ),
        (
            """  rw [Dq_eq_nablaTensorId_add_idTensorDq,
    Dq_eq_nablaTensorId_add_idTensorDq, LinearMap.map_add,
    nablaTensorId_restrict, idTensorDq_restrict]
""",
            """  rw [Dq_eq_nablaTensorId_add_idTensorDq,
    Dq_eq_nablaTensorId_add_idTensorDq]
  simp only [LinearMap.add_apply]
  rw [map_add, nablaTensorId_restrict, idTensorDq_restrict]
""",
            1,
            "Mock2 expose the two derivative summands before restriction linearity",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """      map_add' := by
        intro s t
        funext r
        simp
      map_smul' := by
        intro c s
        funext r
        simp }
""",
            """      map_add' := by
        intro s t
        funext r
        have hfun :
            (fun q => L.trivialization q ((s + t) q)) =
              (fun q => L.trivialization q (s q)) +
                (fun q => L.trivialization q (t q)) := by
          funext q
          simp
        rw [hfun, map_add, map_add]
      map_smul' := by
        intro c s
        funext r
        have hfun :
            (fun q => L.trivialization q ((c • s) q)) =
              c • (fun q => L.trivialization q (s q)) := by
          funext q
          simp
        rw [hfun, map_smul, map_smul] }
""",
            1,
            "Mock2Advanced prove pulled-back connection linearity pointwise",
        ),
        (
            """    (L.connectionOfTrivialization D C).TrivializationCompatible C := by
  intro s r
  exact LinearEquiv.apply_symm_apply (L.trivialization r) _
""",
            """    (QLocalSystem.connectionOfTrivialization L D C).TrivializationCompatible C := by
  intro s r
  exact LinearEquiv.apply_symm_apply (L.trivialization r) _
""",
            1,
            "Mock2Advanced call the pulled-back connection constructor explicitly",
        ),
        (
            """    A = B := by
  apply DependentRadialConnection.ext
  apply LinearMap.ext
  intro s
  funext r
  apply (L.trivialization r).injective
  exact (hA s r).trans (hB s r).symm
""",
            """    A = B := by
  have hnabla : A.nabla = B.nabla := by
    apply LinearMap.ext
    intro s
    funext r
    apply (L.trivialization r).injective
    exact (hA s r).trans (hB s r).symm
  cases A
  cases B
  cases hnabla
  rfl
""",
            1,
            "Mock2Advanced prove dependent connection equality through the nabla field",
        ),
        (
            """    A = L.connectionOfTrivialization D C :=
  A.eq_of_trivializationCompatible (L.connectionOfTrivialization D C)
    hA (L.connectionOfTrivialization_compatible D C)
""",
            """    A = QLocalSystem.connectionOfTrivialization L D C :=
  DependentRadialConnection.eq_of_trivializationCompatible A
    (QLocalSystem.connectionOfTrivialization L D C)
    hA (QLocalSystem.connectionOfTrivialization_compatible L D C)
""",
            1,
            "Mock2Advanced state uniqueness without field notation",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """theorem RealSmooth.contDiffAt_two_upperLift {u : ℍ → ℂ}
    (hu : RealSmooth u) (z : ℍ) :
    ContDiffAt ℝ 2 (upperLift u) (z : ℂ) :=
  (RealSmooth.contDiffAt_upperLift hu z).of_le (by simp)
""",
            """theorem RealSmooth.contDiffAt_two_upperLift {u : ℍ → ℂ}
    (hu : RealSmooth u) (z : ℍ) :
    ContDiffAt ℝ 2 (upperLift u) (z : ℂ) :=
  (RealSmooth.contDiffAt_upperLift hu z).of_le le_top
""",
            1,
            "FunctionalAnalysis lower infinite smoothness to order two explicitly",
        ),
        (
            """theorem RealSmooth.inv {u : ℍ → ℂ} (hu : RealSmooth u)
    (hne : ∀ z, u z ≠ 0) : RealSmooth (fun z => (u z)⁻¹) := by
  unfold RealSmooth at hu ⊢
  simpa [upperLift, Function.comp_def] using
    hu.inv (fun w _ => hne (UpperHalfPlane.ofComplex w))
""",
            """theorem RealSmooth.inv {u : ℍ → ℂ} (hu : RealSmooth u)
    (hne : ∀ z, u z ≠ 0) : RealSmooth (fun z => (u z)⁻¹) := by
  unfold RealSmooth at hu ⊢
  change ContDiffOn ℝ ∞
    (fun w : ℂ => (u (UpperHalfPlane.ofComplex w))⁻¹)
    UpperHalfPlane.upperHalfPlaneSet
  exact hu.inv (fun w _ => hne (UpperHalfPlane.ofComplex w))
""",
            1,
            "FunctionalAnalysis fix reciprocal smoothness codomain inference",
        ),
        (
            """  unfold d1 d2
  rw [hLocal.fderiv_eq]
  have hField :
""",
            """  change
    (fderiv ℝ (upperLift (fun w : ℍ => d1 f w η)) (z : ℂ)) ξ =
      d2 f z ξ η
  rw [hLocal.fderiv_eq]
  unfold d2
  have hField :
""",
            1,
            "FunctionalAnalysis apply local derivative equality before unfolding the inner derivative",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
