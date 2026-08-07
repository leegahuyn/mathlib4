from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "f79ef8961deeda98a6b21dd731061d0f6124729a7562240c7eacbc13dea44f4c"
EXPECTED_OUTPUT_SHA256 = "204acd949c17f55013487819b215886ae5c1c5fb4d125d4683871f8fb94847ad"


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
        print("[pass336] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass336 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = [
        (
            """theorem orbitEuclideanGauge_inner (n : ℤ)
    (u v : OrbitPeterssonCore n) (z : ℍ) :
    inner ℂ (orbitEuclideanGauge n u z)
        (orbitEuclideanGauge n v z) =
      hyperbolicDensity z •
        upstairsInnerDensity (OrbitMultiplier n)
          u.toSmoothCore v.toSmoothCore z := by
  change
    star
          (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
            SmoothCompactWeightCore.toSection u.toSmoothCore z) *
        (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
          SmoothCompactWeightCore.toSection v.toSmoothCore z) = _
  unfold upstairsInnerDensity
    InvariantFiberMetric.pointwiseInnerDensity
  have hScale := congrArg (fun r : ℝ => (r : ℂ))
    (euclideanGaugeScale_sq n z)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at hScale
  simp only [map_mul, Complex.conj_ofReal, NNReal.smul_def,
    smul_eq_mul]
  rw [← hScale]
  ring
""",
            """theorem orbitEuclideanGauge_inner (n : ℤ)
    (u v : OrbitPeterssonCore n) (z : ℍ) :
    inner ℂ (orbitEuclideanGauge n u z)
        (orbitEuclideanGauge n v z) =
      hyperbolicDensity z •
        upstairsInnerDensity (OrbitMultiplier n)
          u.toSmoothCore v.toSmoothCore z := by
  change
    inner ℂ
        (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) •
          SmoothCompactWeightCore.toSection u.toSmoothCore z)
        (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) •
          SmoothCompactWeightCore.toSection v.toSmoothCore z) =
      hyperbolicDensity z •
        upstairsInnerDensity (OrbitMultiplier n)
          u.toSmoothCore v.toSmoothCore z
  rw [inner_smul_left, inner_smul_right]
  unfold upstairsInnerDensity
    InvariantFiberMetric.pointwiseInnerDensity
  have hScale := congrArg (fun r : ℝ => (r : ℂ))
    (euclideanGaugeScale_sq n z)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at hScale
  simp only [map_mul, Complex.conj_ofReal, NNReal.smul_def,
    smul_eq_mul]
  rw [← hScale]
  ring
""",
            "FunctionalAnalysis Euclidean-gauge inner product",
        ),
        (
            """  have hNormHyperbolic :
      IntegrableOn
        (upstairsNormSqDensity (OrbitMultiplier n) u.toSmoothCore)
        chosenGammaTwoFundamentalDomain.carrier hyperbolicMeasure := by
    simpa only [upstairsInnerDensity_self, upstairsNormSqDensity,
      RCLike.ofReal_re, Complex.ofReal_re] using
      hHyperbolic.re
""",
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
""",
            "FunctionalAnalysis Euclidean-gauge integrability real part",
        ),
        (
            """  map_smul' c u := by
    simpa only [orbitEuclideanGauge_smul] using
      (MemLp.toLp_const_smul c (orbitEuclideanGauge_memLp n u))
""",
            """  map_smul' c u := by
    change
      (orbitEuclideanGauge_memLp n (c • u)).toLp
          (orbitEuclideanGauge n (c • u)) =
        c • (orbitEuclideanGauge_memLp n u).toLp
          (orbitEuclideanGauge n u)
    simpa only [orbitEuclideanGauge_smul] using
      (MemLp.toLp_const_smul c (orbitEuclideanGauge_memLp n u))
""",
            "FunctionalAnalysis Euclidean L2 scalar linearity",
        ),
    ]

    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass336 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass336] FunctionalAnalysis Euclidean-gauge analytic frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
