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
            """    rw [tensorRestriction_tmul]
    have hpot := pointwiseOperator_restrict
""",
            """    rw [TensorProduct.map_tmul, tensorRestriction_tmul]
    have hpot := pointwiseOperator_restrict
""",
            1,
            "Mock2 reduce outer and inner potential tensor maps in order",
        ),
        (
            """    rw [tensorRestriction_tmul]
    have hlog := pointwiseOperator_restrict
""",
            """    rw [TensorProduct.map_tmul, tensorRestriction_tmul]
    have hlog := pointwiseOperator_restrict
""",
            1,
            "Mock2 reduce outer and inner logarithmic tensor maps in order",
        ),
        (
            """  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (nablaTensorId P V z + idTensorDq P V z) =
      nablaTensorId P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) +
        idTensorDq P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z)
  rw [LinearMap.map_add, nablaTensorId_restrict, idTensorDq_restrict]
""",
            """  change
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
""",
            1,
            "Mock2 prove Dq restriction through explicit linear-map additivity",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """theorem compatibleGaugeFamily_existsUniqueGlobal
    {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (D : GaugeDescentSheaf X E)
""",
            """theorem compatibleGaugeFamily_existsUniqueGlobal
    {X : Type uSheafX} {E : Type uSheafE} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type uSheafX} (D : GaugeDescentSheaf X E)
""",
            1,
            "Mock2Advanced align gauge gluing cover universe with the sheaf base",
        ),
        (
            """        (s.1 i : D.forms.section (V i)) :=
  simpa only using
    D.covariant_gluing_existsUnique (ι := ι) (U := U)
      V hVU hcover (fun i => s.1 i) (fun i j => s.2 i j)
""",
            """        (s.1 i : D.forms.section (V i)) := by
  simpa only using
    D.covariant_gluing_existsUnique (ι := ι) (U := U)
      V hVU hcover (fun i => s.1 i) (fun i j => s.2 i j)
""",
            1,
            "Mock2Advanced place the gluing simplification inside a proof block",
        ),
        (
            """theorem restrictionToCompatibleGaugeFamily_injective
    {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (D : GaugeDescentSheaf X E)
""",
            """theorem restrictionToCompatibleGaugeFamily_injective
    {X : Type uSheafX} {E : Type uSheafE} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type uSheafX} (D : GaugeDescentSheaf X E)
""",
            1,
            "Mock2Advanced align locality cover universe with the sheaf base",
        ),
        (
            """  apply D.sheaf_condition.locality (ι := ι) (U := U)
    V hVU hcover
""",
            """  apply D.sheaf_condition.locality V hVU hcover
""",
            1,
            "Mock2Advanced use locality after universe alignment",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le (by exact le_top)
""",
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le
    (show (2 : WithTop ℕ) ≤ (⊤ : WithTop ℕ) from le_top)
""",
            1,
            "FunctionalAnalysis type the finite-to-infinite differentiability comparison",
        ),
        (
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by exact le_top)).iteratedFDeriv_cons
""",
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (show (max 2 2 : WithTop ℕ) ≤ (⊤ : WithTop ℕ) from le_top)).iteratedFDeriv_cons
""",
            1,
            "FunctionalAnalysis type the second-order symmetry comparison",
        ),
        (
            """  field_simp [hh]
  ring_nf
  simp [Complex.I_sq]
  <;> ring
""",
            """  have hreduce :
      heightC z * v z * physicalExponent a * (heightC z)⁻¹ * star (u z) =
        v z * physicalExponent a * star (u z) := by
    field_simp [hh]
    ring
  rw [hreduce]
  ring
""",
            1,
            "FunctionalAnalysis cancel the nonzero height in the Green expansion explicitly",
        ),
        (
            """  simpa [weightCoefficient, div_eq_mul_inv] using
    RealSmooth.const_complex_smul q hInv
""",
            """  change RealSmooth (fun z => q * (heightC z)⁻¹)
  simpa only [Pi.smul_apply, smul_eq_mul] using
    RealSmooth.const_complex_smul q hInv
""",
            1,
            "FunctionalAnalysis expose the reciprocal weight coefficient pointwise",
        ),
        (
            """    d1 (weightCoefficient q) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ := by
      simpa [weightCoefficient, div_eq_mul_inv] using
        d1_smul q hInv z ξ
""",
            """    d1 (weightCoefficient q) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ := by
      change d1 (fun w => q * (heightC w)⁻¹) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ
      simpa only [Pi.smul_apply, smul_eq_mul] using
        d1_smul q hInv z ξ
""",
            1,
            "FunctionalAnalysis expose the weighted reciprocal derivative pointwise",
        ),
        (
            """theorem realSmooth_heightSq : RealSmooth heightSq := by
  simpa [heightSq] using realSmooth_heightC.pow 2
""",
            """theorem realSmooth_heightSq : RealSmooth heightSq := by
  change RealSmooth (fun z => heightC z ^ 2)
  exact realSmooth_heightC.pow 2
""",
            1,
            "FunctionalAnalysis expose square-height smoothness definitionally",
        ),
        ("hf.dx", "RealSmooth.dx hf", 11,
          "FunctionalAnalysis call x-derivative smoothness explicitly"),
        ("hf.dy", "RealSmooth.dy hf", 11,
          "FunctionalAnalysis call y-derivative smoothness explicitly"),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
