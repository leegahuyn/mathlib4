from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "4b5e548d48fbd76e4de329fdc20afa3f915dbea800d5e4044ec097474dbe6731"
EXPECTED_OUTPUT_SHA256 = "e1aeb94b938888551c6bc0445d53166c477e15f0f44813bb206ae72c89c627ec"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str) -> str:
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
        print("[pass341] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass341 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = [
        (
            """theorem orbitPeterssonEuclideanEmbedding_norm (n : ℤ)
    (x : OrbitPeterssonHilbert n) :
    ‖orbitPeterssonEuclideanEmbedding n x‖ = ‖x‖ := by
  refine UniformSpace.Completion.denseRange_coe.induction_on x
    (isClosed_eq (orbitPeterssonEuclideanEmbedding n).continuous.norm
      continuous_norm) ?_
  intro u
  rw [orbitPeterssonEuclideanEmbedding_coe]
  simpa only [orbitPeterssonCoreEuclideanIsometry,
    UniformSpace.Completion.norm_coe] using
      (orbitPeterssonCoreEuclideanIsometry n).norm_map u
""",
            """theorem orbitPeterssonEuclideanEmbedding_norm (n : ℤ)
    (x : OrbitPeterssonHilbert n) :
    ‖orbitPeterssonEuclideanEmbedding n x‖ = ‖x‖ := by
  refine UniformSpace.Completion.denseRange_coe.induction_on x
    (isClosed_eq (orbitPeterssonEuclideanEmbedding n).continuous.norm
      continuous_norm) ?_
  intro u
  rw [orbitPeterssonEuclideanEmbedding_coe,
    UniformSpace.Completion.norm_coe]
  change ‖orbitPeterssonCoreEuclideanIsometry n u‖ = ‖u‖
  exact (orbitPeterssonCoreEuclideanIsometry n).norm_map u
""",
            "completed Euclidean embedding norm",
        ),
        (
            """theorem coeFn_embedding_l2Coordinate (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) :
    ⇑(orbitPeterssonEuclideanEmbedding n (l2Coordinate n u)) =ᵐ[
      chosenEuclideanCarrierMeasure]
      (fun z =>
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
          ((u : SmoothQuotientCompactFunction) z)) := by
  rw [l2Coordinate_apply,
    orbitPeterssonEuclideanEmbedding_coe]
  simpa only [orbitEuclideanGauge, coreEmbedding_toSmoothCore,
    InverseEtaFixedPhaseCore.toSmoothCompactWeightCore_apply] using
      coeFn_orbitPeterssonCoreToEuclideanL2 n (coreEmbedding n u)
""",
            """theorem coeFn_embedding_l2Coordinate (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) :
    ⇑(orbitPeterssonEuclideanEmbedding n (l2Coordinate n u)) =ᵐ[
      chosenEuclideanCarrierMeasure]
      (fun z =>
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
          ((u : SmoothQuotientCompactFunction) z)) := by
  rw [l2Coordinate_apply, PeterssonCoreSpace.toCompletion_apply,
    orbitPeterssonEuclideanEmbedding_coe]
  simpa only [orbitEuclideanGauge, coreEmbedding_toSmoothCore,
    InverseEtaFixedPhaseCore.toSmoothCompactWeightCore_apply] using
      coeFn_orbitPeterssonCoreToEuclideanL2 n (coreEmbedding n u)
""",
            "completion coercion before embedding rewrite",
        ),
        (
            """theorem dx_fixedPhaseEuclideanGauge (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    dx (fixedPhaseEuclideanGauge n u) z =
      ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
        dx (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)) z := by
  change dx
    ((fun w : ℍ =>
        ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ)) *
      (((u : SmoothQuotientCompactFunction) : ℍ → ℂ))) z = _
  rw [dx_mul (realSmooth_complexHeightRpow _)
    u.1.1.2, dx_complexHeightRpow]
  simp only [Pi.mul_apply, zero_mul, zero_add]
""",
            """theorem dx_fixedPhaseEuclideanGauge (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    dx (fixedPhaseEuclideanGauge n u) z =
      ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
        dx (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)) z := by
  change dx
    ((fun w : ℍ =>
        ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ)) *
      (((u : SmoothQuotientCompactFunction) : ℍ → ℂ))) z = _
  have hProd := congrFun
    (dx_mul (realSmooth_complexHeightRpow _)
      u.1.1.2) z
  simpa only [dx_complexHeightRpow, Pi.mul_apply, zero_mul,
    zero_add] using hProd
""",
            "pointwise horizontal product derivative",
        ),
        (
            """theorem dy_fixedPhaseEuclideanGauge (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    dy (fixedPhaseEuclideanGauge n u) z =
      ((euclideanGaugeExponent n *
          z.im ^ (euclideanGaugeExponent n - 1) : ℝ) : ℂ) *
          ((u : SmoothQuotientCompactFunction) z) +
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
          dy (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)) z := by
  change dy
    ((fun w : ℍ =>
        ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ)) *
      (((u : SmoothQuotientCompactFunction) : ℍ → ℂ))) z = _
  rw [dy_mul (realSmooth_complexHeightRpow _)
    u.1.1.2, dy_complexHeightRpow]
  rfl
""",
            """theorem dy_fixedPhaseEuclideanGauge (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    dy (fixedPhaseEuclideanGauge n u) z =
      ((euclideanGaugeExponent n *
          z.im ^ (euclideanGaugeExponent n - 1) : ℝ) : ℂ) *
          ((u : SmoothQuotientCompactFunction) z) +
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) *
          dy (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)) z := by
  change dy
    ((fun w : ℍ =>
        ((w.im ^ euclideanGaugeExponent n : ℝ) : ℂ)) *
      (((u : SmoothQuotientCompactFunction) : ℍ → ℂ))) z = _
  have hProd := congrFun
    (dy_mul (realSmooth_complexHeightRpow _)
      u.1.1.2) z
  simpa only [dy_complexHeightRpow, Pi.mul_apply] using hProd
""",
            "pointwise vertical product derivative",
        ),
        (
            """    complex_rpow_derivative_eq_div,
    physicalExponent_eq_twice_gaugeShift]
""",
            """    complex_rpow_derivative_eq_div,
    physicalExponent_eq_twice_gaugeShift,
    fixedPhaseEuclideanGauge_apply]
""",
            "raising gauge point-value normalization",
        ),
        (
            """    euclideanGaugeExponent_succ,
    complex_rpow_derivative_eq_div]
""",
            """    euclideanGaugeExponent_succ,
    complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply]
""",
            "lowering gauge point-value normalization",
        ),
        (
            """  simpa only [euclideanRaiseGauge, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul, mul_assoc] using h
""",
            """  have hEq :
      euclideanRaiseGauge n f =
        (Complex.I • (heightC * dx f)) +
          (heightC * dy f) +
          (((euclideanGaugeExponent n + 2 : ℝ) : ℂ) • f) := by
    funext z
    simp only [euclideanRaiseGauge, Pi.add_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hEq]
  exact h
""",
            "raising gauge smooth function equality",
        ),
        (
            """  simpa only [euclideanLowerFromSuccGauge, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using h
""",
            """  have hEq :
      euclideanLowerFromSuccGauge n f =
        ((-Complex.I) • (heightC * dx f)) +
          (heightC * dy f) -
          (((euclideanGaugeExponent n + 1 : ℝ) : ℂ) • f) := by
    funext z
    simp only [euclideanLowerFromSuccGauge, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hEq]
  exact h
""",
            "lowering gauge smooth function equality",
        ),
    ]

    for old, new, label in replacements:
        text = replace_exact(text, old, new, label)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass341 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass341] Euclidean embedding and gauge API frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
