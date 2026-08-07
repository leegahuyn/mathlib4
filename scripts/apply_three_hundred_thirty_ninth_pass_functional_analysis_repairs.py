from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "1d150bcb8bd909e1bde7ce3577cf754386efcd7be2902d68a7c78b72b28d6b39"
EXPECTED_OUTPUT_SHA256 = "6c277b2a7eefc7c4bd776ddd2b37550268a058d333b2457a6b5428d5cf419599"


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
        print("[pass339] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass339 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = [
        (
            """    _ = ∫ z in chosenGammaTwoFundamentalDomain.carrier,
        upstairsInnerDensity (OrbitMultiplier n)
          u.toSmoothCore v.toSmoothCore z
        ∂hyperbolicMeasure := by
      rw [hyperbolicMeasure_eq_euclidean_withDensity,
        setIntegral_withDensity_eq_setIntegral_smul
          hyperbolicDensity_measurable _
          chosenGammaTwoFundamentalDomain.carrier_measurable]
""",
            """    _ = ∫ z in chosenGammaTwoFundamentalDomain.carrier,
        upstairsInnerDensity (OrbitMultiplier n)
          u.toSmoothCore v.toSmoothCore z
        ∂hyperbolicMeasure := by
      rw [hyperbolicMeasure_eq_euclidean_withDensity]
      exact (setIntegral_withDensity_eq_setIntegral_smul
        hyperbolicDensity_measurable
        (fun z => upstairsInnerDensity (OrbitMultiplier n)
          u.toSmoothCore v.toSmoothCore z)
        chosenGammaTwoFundamentalDomain.carrier_measurable).symm
""",
            "FunctionalAnalysis explicit withDensity integral identity",
        ),
        (
            """  rw [l2Coordinate_apply,
    orbitPeterssonEuclideanEmbedding_coe]
  simpa only [orbitEuclideanGauge, coreEmbedding_toSmoothCore,
    InverseEtaFixedPhaseCore.toSmoothCompactWeightCore_apply] using
      coeFn_orbitPeterssonCoreToEuclideanL2 n (coreEmbedding n u)
""",
            """  rw [l2Coordinate_apply]
  change
    ⇑(orbitPeterssonEuclideanEmbedding n
      ((coreEmbedding n u : OrbitPeterssonCore n) : OrbitPeterssonHilbert n)) =ᵐ[
        chosenEuclideanCarrierMeasure]
      (fun z =>
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
          ((u : SmoothQuotientCompactFunction) z))
  rw [orbitPeterssonEuclideanEmbedding_coe]
  simpa only [orbitEuclideanGauge, coreEmbedding_toSmoothCore,
    InverseEtaFixedPhaseCore.toSmoothCompactWeightCore_apply] using
      coeFn_orbitPeterssonCoreToEuclideanL2 n (coreEmbedding n u)
""",
            "FunctionalAnalysis completion embedding coercion",
        ),
        (
            """  rw [dx_mul (realSmooth_complexHeightRpow _)
    u.1.1.2, dx_complexHeightRpow]
  simp only [Pi.mul_apply, zero_mul, zero_add]
""",
            """  have h := dx_mul
    (u := fun w : ℍ => ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ))
    (v := (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)))
    (realSmooth_complexHeightRpow _) u.1.1.2 z
  simpa only [dx_complexHeightRpow, Pi.mul_apply, zero_mul, zero_add] using h
""",
            "FunctionalAnalysis horizontal gauge product rule",
        ),
        (
            """  rw [dy_mul (realSmooth_complexHeightRpow _)
    u.1.1.2, dy_complexHeightRpow]
  rfl
""",
            """  have h := dy_mul
    (u := fun w : ℍ => ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ))
    (v := (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)))
    (realSmooth_complexHeightRpow _) u.1.1.2 z
  simpa only [dy_complexHeightRpow, Pi.mul_apply] using h
""",
            "FunctionalAnalysis vertical gauge product rule",
        ),
        (
            """  rw [dx_fixedPhaseEuclideanGauge,
    dy_fixedPhaseEuclideanGauge,
    euclideanGaugeScale_succ,
    complex_rpow_derivative_eq_div,
    physicalExponent_eq_twice_gaugeShift]
""",
            """  rw [dx_fixedPhaseEuclideanGauge,
    dy_fixedPhaseEuclideanGauge,
    euclideanGaugeScale_succ,
    complex_rpow_derivative_eq_div,
    physicalExponent_eq_twice_gaugeShift,
    fixedPhaseEuclideanGauge_apply]
""",
            "FunctionalAnalysis raising gauge zeroth term",
        ),
        (
            """  rw [dx_fixedPhaseEuclideanGauge,
    dy_fixedPhaseEuclideanGauge,
    euclideanGaugeScale_succ,
    euclideanGaugeExponent_succ,
    complex_rpow_derivative_eq_div]
""",
            """  rw [dx_fixedPhaseEuclideanGauge,
    dy_fixedPhaseEuclideanGauge,
    euclideanGaugeScale_succ,
    euclideanGaugeExponent_succ,
    complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply]
""",
            "FunctionalAnalysis lowering gauge zeroth term",
        ),
        (
            """  simpa only [euclideanRaiseGauge, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul, mul_assoc] using h
""",
            """  change RealSmooth
    ((Complex.I • (heightC * dx f)) +
      (heightC * dy f) +
      (((euclideanGaugeExponent n + 2 : ℝ) : ℂ) • f))
  exact h
""",
            "FunctionalAnalysis raising gauge smoothness target",
        ),
        (
            """  simpa only [euclideanLowerFromSuccGauge, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using h
""",
            """  change RealSmooth
    (((-Complex.I) • (heightC * dx f)) +
      (heightC * dy f) -
      (((euclideanGaugeExponent n + 1 : ℝ) : ℂ) • f))
  exact h
""",
            "FunctionalAnalysis lowering gauge smoothness target",
        ),
    ]

    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass339 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass339] FunctionalAnalysis density, completion, derivative, and gauge frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
