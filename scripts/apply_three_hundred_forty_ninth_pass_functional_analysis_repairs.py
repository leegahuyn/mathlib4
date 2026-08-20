from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "6941bcd0685044b1903cf0f380a7dc0e03ecc4a76981a75d5e0f6395ca172ab0"
EXPECTED_OUTPUT_SHA256 = "7fa46c797904dea5ffddc3605d2de28c24a5c0325f928d81c28735fc2e16b018"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_required(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(
            f"{label}: expected {expected} occurrence(s), found {count}"
        )
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass349] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass349 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_required(
        text,
        "rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov",
        "rw [← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov",
        "FunctionalAnalysis orient GammaTwo covariance transport backwards",
        expected=2,
    )
    text = replace_required(
        text,
        """    _ = 0 :=
      (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)""",
        """    _ = 0 :=
      norm_eq_zero.mpr rfl""",
        "FunctionalAnalysis prove the exact-tail zero norm by norm_eq_zero",
    )
    text = replace_required(
        text,
        "WeightSection.add_apply",
        "HalfIntegralMultiplier.WeightSection.add_apply",
        "FunctionalAnalysis fully qualify WeightSection addition evaluation",
        expected=4,
    )
    text = replace_required(
        text,
        "WeightSection.smul_apply",
        "HalfIntegralMultiplier.WeightSection.smul_apply",
        "FunctionalAnalysis fully qualify WeightSection scalar evaluation",
        expected=4,
    )

    text = replace_required(
        text,
        """  simp only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  change
    (((InverseEtaFixedPhaseCore.raise n)
        (cuspCutoffOperator N n u) :
          InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) z -
      (((cuspCutoffOperator N (n + 1))
        (InverseEtaFixedPhaseCore.raise n u) :
          InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) z = _
  simp only [InverseEtaFixedPhaseCore.raise_apply,
    cuspCutoffOperator_apply]
  rw [raiseRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
""",
        """  simp only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  change
    (InverseEtaFixedPhaseCore.toWeightSection (n + 1)
      ((InverseEtaFixedPhaseCore.raise n)
          (cuspCutoffOperator N n u) -
        (cuspCutoffOperator N (n + 1))
          (InverseEtaFixedPhaseCore.raise n u))) z = _
  rw [map_sub, HalfIntegralMultiplier.WeightSection.sub_apply]
  simp only [InverseEtaFixedPhaseCore.toWeightSection_apply,
    InverseEtaFixedPhaseCore.raise_apply, cuspCutoffOperator_apply]
  rw [raiseRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
""",
        "FunctionalAnalysis evaluate the raising commutator through toWeightSection",
    )
    text = replace_required(
        text,
        """  simp only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  change
    (((InverseEtaFixedPhaseCore.lower n)
        (cuspCutoffOperator N n u) :
          InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) z -
      (((cuspCutoffOperator N (n - 1))
        (InverseEtaFixedPhaseCore.lower n u) :
          InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) z = _
  simp only [InverseEtaFixedPhaseCore.lower_apply,
    cuspCutoffOperator_apply]
  rw [lowerRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
""",
        """  simp only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  change
    (InverseEtaFixedPhaseCore.toWeightSection (n - 1)
      ((InverseEtaFixedPhaseCore.lower n)
          (cuspCutoffOperator N n u) -
        (cuspCutoffOperator N (n - 1))
          (InverseEtaFixedPhaseCore.lower n u))) z = _
  rw [map_sub, HalfIntegralMultiplier.WeightSection.sub_apply]
  simp only [InverseEtaFixedPhaseCore.toWeightSection_apply,
    InverseEtaFixedPhaseCore.lower_apply, cuspCutoffOperator_apply]
  rw [lowerRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
""",
        "FunctionalAnalysis evaluate the lowering commutator through toWeightSection",
    )

    text = replace_required(
        text,
        """noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=
  (1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2

theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  simpa only [hyperbolicDensity] using
    ((continuous_const.div₀
      (UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)).pow 2)

theorem hyperbolicDensity_measurable :
    Measurable hyperbolicDensity :=
  hyperbolicDensity_continuous.measurable

@[simp]
theorem hyperbolicDensity_coe (z : ℍ) :
    (hyperbolicDensity z : ℝ) = (1 / z.im) ^ 2 := by
  simp [hyperbolicDensity]

theorem hyperbolicMeasure_eq_euclidean_withDensity :
    hyperbolicMeasure =
      upperEuclideanMeasure.withDensity fun z => hyperbolicDensity z := by
  simpa only [upperEuclideanMeasure, hyperbolicDensity] using
    hyperbolicMeasure_def
""",
        """noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=
  ⟨z.im⁻¹ ^ 2, sq_nonneg _⟩

@[simp]
theorem hyperbolicDensity_coe (z : ℍ) :
    (hyperbolicDensity z : ℝ) = z.im⁻¹ ^ 2 :=
  rfl

theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  exact
    ((UpperHalfPlane.continuous_im.inv₀ (fun z => z.im_ne_zero)).pow 2).subtype_mk
      (fun z => sq_nonneg (z.im⁻¹))

theorem hyperbolicDensity_measurable :
    Measurable hyperbolicDensity :=
  hyperbolicDensity_continuous.measurable

theorem hyperbolicMeasure_eq_euclidean_withDensity :
    hyperbolicMeasure =
      upperEuclideanMeasure.withDensity fun z => hyperbolicDensity z := by
  simpa only [upperEuclideanMeasure, hyperbolicDensity, one_div] using
    hyperbolicMeasure_def
""",
        "FunctionalAnalysis construct hyperbolic density through the real inverse",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass349 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass349] FunctionalAnalysis covariance, section algebra, commutator, "
        "and density roots repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
