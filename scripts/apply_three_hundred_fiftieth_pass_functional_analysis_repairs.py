from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "7fa46c797904dea5ffddc3605d2de28c24a5c0325f928d81c28735fc2e16b018"
EXPECTED_OUTPUT_SHA256 = "519d8b37b8fe03fedfd61d8afd60be98e9ac42e6eaee5dcf25a82891f18e80da"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_required(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass350] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass350 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_required(
        text,
        """  rw [inner_smul_left, inner_smul_right]
  unfold upstairsInnerDensity
    InvariantFiberMetric.pointwiseInnerDensity
    InvariantFiberMetric.weightFiberMetric
  have hScale := congrArg (fun r : ℝ => (r : ℂ))
    (euclideanGaugeScale_sq n z)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at hScale
  simp only [map_mul, Complex.conj_ofReal, NNReal.smul_def,
    smul_eq_mul]
  rw [← hScale]
  ring
""",
        """  rw [inner_smul_left, inner_smul_right]
  unfold upstairsInnerDensity
    InvariantFiberMetric.pointwiseInnerDensity
    InvariantFiberMetric.weightFiberMetric
  have hScale := congrArg (fun r : ℝ => (r : ℂ))
    (euclideanGaugeScale_sq n z)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at hScale
  simp only [Complex.conj_ofReal, NNReal.smul_def, smul_eq_mul]
  change
    ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
        (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
          (star (SmoothCompactWeightCore.toSection u.toSmoothCore z) *
            SmoothCompactWeightCore.toSection v.toSmoothCore z)) =
      ((hyperbolicDensity z : ℝ) : ℂ) *
        (((weightFiberScale (-paperOrbitExponent n) z : ℝ) : ℂ) *
          (star (SmoothCompactWeightCore.toSection u.toSmoothCore z) *
            SmoothCompactWeightCore.toSection v.toSmoothCore z))
  calc
    _ = (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) ^ 2) *
        (star (SmoothCompactWeightCore.toSection u.toSmoothCore z) *
          SmoothCompactWeightCore.toSection v.toSmoothCore z) := by ring
    _ = ((((hyperbolicDensity z : ℝ) *
        weightFiberScale (-paperOrbitExponent n) z : ℝ) : ℂ)) *
        (star (SmoothCompactWeightCore.toSection u.toSmoothCore z) *
          SmoothCompactWeightCore.toSection v.toSmoothCore z) := by
      rw [hScale]
    _ = _ := by
      simp only [Complex.ofReal_mul]
      ring
""",
        "FunctionalAnalysis normalize the Euclidean-gauge inner product",
    )
    text = replace_required(
        text,
        """  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hre := congrArg Complex.re
    (orbitEuclideanGauge_inner n u u z)
  simpa only [upstairsInnerDensity_self, NNReal.smul_def,
    Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using hre
""",
        """  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hre := congrArg Complex.re
    (orbitEuclideanGauge_inner n u u z)
  simpa only [upstairsInnerDensity_self, upstairsNormSqDensity,
    NNReal.smul_def, Complex.smul_re, Complex.ofReal_re,
    RCLike.ofReal_re, smul_eq_mul] using hre
""",
        "FunctionalAnalysis identify the real norm-squared density",
    )
    text = replace_required(
        text,
        """  have hNormHyperbolicRe :
      Integrable
        (fun z => RCLike.re
          ((upstairsNormSqDensity (OrbitMultiplier n) u.toSmoothCore z : ℝ) : ℂ))
        (hyperbolicMeasure.restrict
          chosenGammaTwoFundamentalDomain.carrier) := by
    simpa only [upstairsInnerDensity_self, upstairsNormSqDensity] using
      hHyperbolic.re
  have hNormHyperbolic :
      Integrable
        (upstairsNormSqDensity (OrbitMultiplier n) u.toSmoothCore)
        (hyperbolicMeasure.restrict
          chosenGammaTwoFundamentalDomain.carrier) := by
    simpa only [RCLike.ofReal_re, Complex.ofReal_re] using hNormHyperbolicRe
""",
        """  have hNormHyperbolic :
      Integrable
        (upstairsNormSqDensity (OrbitMultiplier n) u.toSmoothCore)
        (hyperbolicMeasure.restrict
          chosenGammaTwoFundamentalDomain.carrier) := by
    simpa only [upstairsInnerDensity_self, upstairsNormSqDensity,
      Complex.ofReal_re, RCLike.ofReal_re] using hHyperbolic.re
""",
        "FunctionalAnalysis obtain norm-density integrability directly",
    )
    text = replace_required(
        text,
        """  have hProd :=
    dx_mul (realSmooth_complexHeightRpow _)
      u.1.1.2 z
""",
        """  have hProd :=
    dx_mul
      (u := fun w : ℍ =>
        ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ))
      (v := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      u.1.1.2 z
""",
        "FunctionalAnalysis instantiate the horizontal product rule",
    )
    text = replace_required(
        text,
        """  have hProd :=
    dy_mul (realSmooth_complexHeightRpow _)
      u.1.1.2 z
""",
        """  have hProd :=
    dy_mul
      (u := fun w : ℍ =>
        ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ))
      (v := ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      u.1.1.2 z
""",
        "FunctionalAnalysis instantiate the vertical product rule",
    )
    text = replace_required(
        text,
        """theorem hyperbolicDensity_ne_zero (z : ℍ) :
    (hyperbolicDensity z : ℝ≥0∞) ≠ 0 := by
  apply ENNReal.coe_ne_zero.mpr
  apply pow_ne_zero
  exact div_ne_zero one_ne_zero <| by
    intro h
    apply z.im_ne_zero
    exact congrArg (fun r : NNReal => (r : ℝ)) h
""",
        """theorem hyperbolicDensity_ne_zero (z : ℍ) :
    (hyperbolicDensity z : ℝ≥0∞) ≠ 0 := by
  apply ENNReal.coe_ne_zero.mpr
  change z.im⁻¹ ^ 2 ≠ 0
  exact pow_ne_zero 2 (inv_ne_zero z.im_ne_zero)
""",
        "FunctionalAnalysis prove the hyperbolic density is nonzero",
    )
    text = replace_required(
        text,
        """  have hnot : ∀ᵐ z ∂upperEuclideanMeasure,
      z ∉ chosenGammaTwoFundamentalDomain.carrier \\
        gammaTwoOpenCarrier := by
    rw [ae_iff]
    convert chosenCarrier_diff_open_null_upperEuclidean using 1
    ext z
    simp
""",
        """  have hnot : ∀ᵐ z ∂upperEuclideanMeasure,
      z ∉ chosenGammaTwoFundamentalDomain.carrier \\
        gammaTwoOpenCarrier := by
    rw [ae_iff]
    simpa only [not_not, Set.mem_setOf_eq] using
      chosenCarrier_diff_open_null_upperEuclidean
""",
        "FunctionalAnalysis restore the exact AE set comprehension",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass350 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass350] FunctionalAnalysis Euclidean gauge, derivative, density, "
        "and AE roots repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
