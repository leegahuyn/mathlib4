from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "97bd40b0149364544c1fecb1a835c77b6190ebd66f141f8a9f3abc94ac84d977"
EXPECTED_OUTPUT_SHA256 = "ba8e9ae92a27b5ea965990b207458b477d1527fa081e854cd43b299eac82150e"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
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
        print("[pass345] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass345 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        """  rw [inner_smul_left, inner_smul_right]
  unfold upstairsInnerDensity
    InvariantFiberMetric.pointwiseInnerDensity
  have hScale := congrArg (fun r : ℝ => (r : ℂ))
""",
        """  rw [inner_smul_left, inner_smul_right]
  unfold upstairsInnerDensity
    InvariantFiberMetric.pointwiseInnerDensity
    InvariantFiberMetric.weightFiberMetric
  have hScale := congrArg (fun r : ℝ => (r : ℂ))
""",
        "FunctionalAnalysis unfold the orbit fiber metric scale",
    )
    text = replace_once(
        text,
        """  have h := orbitEuclideanGauge_inner n u u z
  have hre := congrArg Complex.re h
  simpa only [inner_self_eq_norm_sq, Complex.ofReal_re,
    upstairsInnerDensity_self, NNReal.smul_def,
    Complex.smul_re, smul_eq_mul] using hre
""",
        """  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hre := congrArg Complex.re
    (orbitEuclideanGauge_inner n u u z)
  simpa only [upstairsInnerDensity_self, NNReal.smul_def,
    Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using hre
""",
        "FunctionalAnalysis derive the Euclidean norm square from the inner product",
    )
    text = replace_once(
        text,
        """  have hNormHyperbolicRe :
      IntegrableOn
        (fun z => RCLike.re
          ((upstairsNormSqDensity (OrbitMultiplier n) u.toSmoothCore z : ℝ) : ℂ))
        chosenGammaTwoFundamentalDomain.carrier hyperbolicMeasure := by
    simpa only [upstairsInnerDensity_self, upstairsNormSqDensity] using
      hHyperbolic.re
  have hNormHyperbolic :
      IntegrableOn
        (upstairsNormSqDensity (OrbitMultiplier n) u.toSmoothCore)
        chosenGammaTwoFundamentalDomain.carrier hyperbolicMeasure := by
    simpa only [RCLike.ofReal_re, Complex.ofReal_re] using hNormHyperbolicRe
  change Integrable
    (upstairsNormSqDensity (OrbitMultiplier n) u.toSmoothCore)
    (hyperbolicMeasure.restrict
      chosenGammaTwoFundamentalDomain.carrier) at hNormHyperbolic
""",
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
        "FunctionalAnalysis express norm-density integrability on the restricted measure",
    )
    text = replace_once(
        text,
        """  simpa only [orbitPeterssonCoreToEuclideanL2] using
    MemLp.coeFn_toLp (orbitEuclideanGauge_memLp n u)
""",
        """  change
    ⇑((orbitEuclideanGauge_memLp n u).toLp
      (orbitEuclideanGauge n u)) =ᵐ[
        chosenEuclideanCarrierMeasure] orbitEuclideanGauge n u
  exact MemLp.coeFn_toLp (orbitEuclideanGauge_memLp n u)
""",
        "FunctionalAnalysis expose the literal L2 representative",
    )
    text = replace_once(
        text,
        """  rw [l2Coordinate_apply, PeterssonCoreSpace.toCompletion_apply,
    orbitPeterssonEuclideanEmbedding_coe]
  simpa only [orbitEuclideanGauge, coreEmbedding_toSmoothCore,
    InverseEtaFixedPhaseCore.toSmoothCompactWeightCore_apply] using
      coeFn_orbitPeterssonCoreToEuclideanL2 n (coreEmbedding n u)
""",
        """  rw [l2Coordinate_apply, PeterssonCoreSpace.toCompletion_apply,
    orbitPeterssonEuclideanEmbedding_coe]
  have h :=
    coeFn_orbitPeterssonCoreToEuclideanL2 n (coreEmbedding n u)
  filter_upwards [h] with z hz
  simpa only [orbitEuclideanGauge, coreEmbedding_toSmoothCore,
    InverseEtaFixedPhaseCore.toSmoothCompactWeightCore_apply] using hz
""",
        "FunctionalAnalysis transport the embedded L2 representative pointwise",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass345 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass345] FunctionalAnalysis Petersson-to-Euclidean realization roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
