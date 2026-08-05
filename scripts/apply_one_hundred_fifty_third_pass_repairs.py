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
            """    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
    have hpot := pointwiseOperator_restrict
""",
            """    rw [tensorRestriction_tmul]
    have hpot := pointwiseOperator_restrict
""",
            1,
            "Mock2 reduce the inner potential tensor restriction only",
        ),
        (
            """    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
    have hlog := pointwiseOperator_restrict
""",
            """    rw [tensorRestriction_tmul]
    have hlog := pointwiseOperator_restrict
""",
            1,
            "Mock2 reduce the inner logarithmic tensor restriction only",
        ),
        (
            """  rw [Dq_apply, Dq_apply]
  change
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
  rw [LinearMap.map_add, nablaTensorId_restrict, idTensorDq_restrict]
""",
            1,
            "Mock2 unfold Dq through the target change instead of rewriting",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  flat_minimizer_mass_remainder_zero D hmass hremainder A A₀ hflat
    (D.action_eq_zero_of_flat_vacuum hflat₀ hmass₀ hremainder₀) hmin
""",
            """  flat_minimizer_mass_remainder_zero D hmass hremainder A A₀ hflat
    (EffectiveActionDecomposition.action_eq_zero_of_flat_vacuum
      D hflat₀ hmass₀ hremainder₀) hmin
""",
            1,
            "Mock2Advanced call flat-vacuum action vanishing explicitly",
        ),
        (
            """  D.covariant_gluing_existsUnique V hVU hcover s.1 s.2
""",
            """  simpa only using
    D.covariant_gluing_existsUnique (ι := ι) (U := U)
      V hVU hcover (fun i => s.1 i) (fun i j => s.2 i j)
""",
            1,
            "Mock2Advanced determine gauge gluing family and universes explicitly",
        ),
        (
            """  apply D.sheaf_condition.locality V hVU hcover
""",
            """  apply D.sheaf_condition.locality (ι := ι) (U := U)
    V hVU hcover
""",
            1,
            "Mock2Advanced determine locality cover universes explicitly",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le (by norm_num)
""",
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le (by exact le_top)
""",
            1,
            "FunctionalAnalysis lower infinite smoothness to order two by le_top",
        ),
        (
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by norm_num)).iteratedFDeriv_cons
""",
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by exact le_top)).iteratedFDeriv_cons
""",
            1,
            "FunctionalAnalysis supply second-order smoothness with expected-type le_top",
        ),
        (
            """  simp only [map_add, map_mul, map_div₀, map_neg,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
""",
            """  simp only [star_add, star_mul', star_div, star_neg,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
""",
            1,
            "FunctionalAnalysis use current star-ring simplification lemmas",
        ),
        (
            """def weightCoefficient (q : ℂ) (z : ℍ) : ℂ :=
""",
            """noncomputable def weightCoefficient (q : ℂ) (z : ℍ) : ℂ :=
""",
            1,
            "FunctionalAnalysis mark the reciprocal weight coefficient noncomputable",
        ),
        (
            """  have hInv : RealSmooth (fun z => (heightC z)⁻¹) :=
    realSmooth_heightC.inv heightC_ne_zero
  simpa [weightCoefficient, div_eq_mul_inv] using
    hInv.const_complex_smul q
""",
            """  have hInv : RealSmooth (fun z => (heightC z)⁻¹) :=
    RealSmooth.inv realSmooth_heightC heightC_ne_zero
  simpa [weightCoefficient, div_eq_mul_inv] using
    RealSmooth.const_complex_smul q hInv
""",
            1,
            "FunctionalAnalysis call reciprocal and scalar smoothness explicitly",
        ),
        (
            """  have hInv : RealSmooth (fun w => (heightC w)⁻¹) :=
    realSmooth_heightC.inv heightC_ne_zero
""",
            """  have hInv : RealSmooth (fun w => (heightC w)⁻¹) :=
    RealSmooth.inv realSmooth_heightC heightC_ne_zero
""",
            1,
            "FunctionalAnalysis call reciprocal smoothness explicitly in the derivative",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
