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
    simp only [LinearMap.comp_apply, localCoefficient_tmul,
      LinearMap.map_add, tensorRestriction_tmul]
    rw [pointwiseOperator_restrict, pointwiseOperator_restrict]
""",
            """    apply TensorProduct.ext'
    intro l m
    change
      TensorProduct.map
          (locallyConstantRestriction E hUV)
          (locallyConstantRestriction F hUV)
          ((l ⊗ₜ[ℂ] pointwiseOperator P.logDerivative V m) +
            (pointwiseOperator P.qPotential V l ⊗ₜ[ℂ] m)) =
        (locallyConstantRestriction E hUV l ⊗ₜ[ℂ]
            pointwiseOperator P.logDerivative U
              (locallyConstantRestriction F hUV m)) +
          (pointwiseOperator P.qPotential U
              (locallyConstantRestriction E hUV l) ⊗ₜ[ℂ]
            locallyConstantRestriction F hUV m)
    rw [LinearMap.map_add, TensorProduct.map_tmul,
      TensorProduct.map_tmul]
    have hlog := pointwiseOperator_restrict
      (X := X) P.logDerivative hUV m
    change
      locallyConstantRestriction F hUV
          (pointwiseOperator P.logDerivative V m) =
        pointwiseOperator P.logDerivative U
          (locallyConstantRestriction F hUV m) at hlog
    have hpot := pointwiseOperator_restrict
      (X := X) P.qPotential hUV l
    change
      locallyConstantRestriction E hUV
          (pointwiseOperator P.qPotential V l) =
        pointwiseOperator P.qPotential U
          (locallyConstantRestriction E hUV l) at hpot
    rw [hlog, hpot]
""",
            1,
            "Mock2 prove local coefficient naturality in the raw tensor carrier",
        ),
        (
            """    apply TensorProduct.ext'
    intro l m
    simp only [LinearMap.comp_apply, nablaTensorId_tmul,
      tensorRestriction_tmul, potentialCoefficient_tmul]
    rw [pointwiseOperator_restrict, dlogFrame_restrict]
""",
            """    apply TensorProduct.ext'
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
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
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
""",
            1,
            "Mock2 prove nabla tensor naturality in the raw tensor carrier",
        ),
        (
            """    apply TensorProduct.ext'
    intro l m
    simp only [LinearMap.comp_apply, idTensorDq_tmul,
      tensorRestriction_tmul, logRadialCoefficient_tmul]
    rw [pointwiseOperator_restrict, dlogFrame_restrict]
""",
            """    apply TensorProduct.ext'
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
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
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
""",
            1,
            "Mock2 prove logarithmic tensor naturality in the raw tensor carrier",
        ),
        (
            """  rw [Dq_eq_nablaTensorId_add_idTensorDq,
    Dq_eq_nablaTensorId_add_idTensorDq]
  simp only [LinearMap.add_apply]
  rw [map_add, nablaTensorId_restrict, idTensorDq_restrict]
""",
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
            1,
            "Mock2 derive full derivative naturality in the raw carrier",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """        rw [hfun, map_add, map_add]
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
            """        rw [hfun, map_add]
        simpa only [Pi.add_apply, map_add]
      map_smul' := by
        intro c s
        funext r
        have hfun :
            (fun q => L.trivialization q ((c • s) q)) =
              c • (fun q => L.trivialization q (s q)) := by
          funext q
          simp
        rw [hfun, map_smul]
        simpa only [Pi.smul_apply, RingHom.id_apply, map_smul] }
""",
            1,
            "Mock2Advanced finish pulled-back connection linearity pointwise",
        ),
        (
            """    T = L.transport r s := by
  ext x
  apply (L.trivialization s).injective
  rw [hT x]
  simp [QLocalSystem.transport]
""",
            """    T = L.transport r s := by
  apply LinearEquiv.ext
  intro x
  apply (L.trivialization s).injective
  rw [hT x]
  simp [QLocalSystem.transport]
""",
            1,
            "Mock2Advanced compare transports before subtype extensionality",
        ),
        (
            """  simpa using D.action_eq_zero_of_flat_vacuum hF hT hL hU
""",
            """  simpa using
    EffectiveActionDecomposition.action_eq_zero_of_flat_vacuum
      D hF hT hL hU
""",
            1,
            "Mock2Advanced call the effective-action vanishing theorem explicitly",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le le_top
""",
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le (by norm_num)
""",
            1,
            "FunctionalAnalysis prove finite differentiability order numerically",
        ),
        (
            """theorem RealSmooth.dx {f : ℍ → ℂ} (hf : RealSmooth f) :
    RealSmooth (dx f) := by
  simpa [dx] using RealSmooth.d1_constDirection hf (1 : ℂ)
""",
            """theorem RealSmooth.dx {f : ℍ → ℂ} (hf : RealSmooth f) :
    RealSmooth (dx f) := by
  change RealSmooth (fun z => d1 f z (1 : ℂ))
  exact RealSmooth.d1_constDirection hf (1 : ℂ)
""",
            1,
            "FunctionalAnalysis expose the x derivative definition",
        ),
        (
            """theorem RealSmooth.dy {f : ℍ → ℂ} (hf : RealSmooth f) :
    RealSmooth (dy f) := by
  simpa [dy] using RealSmooth.d1_constDirection hf Complex.I
""",
            """theorem RealSmooth.dy {f : ℍ → ℂ} (hf : RealSmooth f) :
    RealSmooth (dy f) := by
  change RealSmooth (fun z => d1 f z Complex.I)
  exact RealSmooth.d1_constDirection hf Complex.I
""",
            1,
            "FunctionalAnalysis expose the y derivative definition",
        ),
        (
            """theorem dx_dx {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dx (dx f) z = dxx f z := by
  simpa [dx, dxx] using d1_d1 hf z (1 : ℂ) (1 : ℂ)
""",
            """theorem dx_dx {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dx (dx f) z = dxx f z := by
  change d1 (fun w => d1 f w (1 : ℂ)) z (1 : ℂ) =
    d2 f z (1 : ℂ) (1 : ℂ)
  exact d1_d1 hf z (1 : ℂ) (1 : ℂ)
""",
            1,
            "FunctionalAnalysis expose the xx iterated derivative",
        ),
        (
            """theorem dx_dy {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dx (dy f) z = dxy f z := by
  simpa [dx, dy, dxy] using d1_d1 hf z (1 : ℂ) Complex.I
""",
            """theorem dx_dy {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dx (dy f) z = dxy f z := by
  change d1 (fun w => d1 f w Complex.I) z (1 : ℂ) =
    d2 f z (1 : ℂ) Complex.I
  exact d1_d1 hf z (1 : ℂ) Complex.I
""",
            1,
            "FunctionalAnalysis expose the xy iterated derivative",
        ),
        (
            """theorem dy_dx {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dy (dx f) z = dyx f z := by
  simpa [dx, dy, dyx] using d1_d1 hf z Complex.I (1 : ℂ)
""",
            """theorem dy_dx {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dy (dx f) z = dyx f z := by
  change d1 (fun w => d1 f w (1 : ℂ)) z Complex.I =
    d2 f z Complex.I (1 : ℂ)
  exact d1_d1 hf z Complex.I (1 : ℂ)
""",
            1,
            "FunctionalAnalysis expose the yx iterated derivative",
        ),
        (
            """theorem dy_dy {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dy (dy f) z = dyy f z := by
  simpa [dy, dyy] using d1_d1 hf z Complex.I Complex.I
""",
            """theorem dy_dy {f : ℍ → ℂ} (hf : RealSmooth f) (z : ℍ) :
    dy (dy f) z = dyy f z := by
  change d1 (fun w => d1 f w Complex.I) z Complex.I =
    d2 f z Complex.I Complex.I
  exact d1_d1 hf z Complex.I Complex.I
""",
            1,
            "FunctionalAnalysis expose the yy iterated derivative",
        ),
        (
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons
""",
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by norm_num)).iteratedFDeriv_cons
""",
            1,
            "FunctionalAnalysis prove second-order smoothness numerically",
        ),
        (
            """def physicalExponent (a : ℤ) : ℂ :=
""",
            """noncomputable def physicalExponent (a : ℤ) : ℂ :=
""",
            1,
            "FunctionalAnalysis mark the physical exponent noncomputable",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
