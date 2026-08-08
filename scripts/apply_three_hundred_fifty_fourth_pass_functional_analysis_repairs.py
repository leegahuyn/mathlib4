from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "986d7a309dc10a15e6bc918b17484d5873ab1364c2e72a7228a9be939925bd30"
EXPECTED_OUTPUT_SHA256 = "974545f05c6f2eaa981fd3ab3da37e61634c7a3db1088da1c10904e465ffbe47"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass354] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass354 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        """    _ = 0 := by
      apply norm_eq_zero.mpr
      rfl
""",
        """    _ = 0 := by
      exact norm_zero
""",
        "FunctionalAnalysis close the typed zero-form norm",
    )
    text = replace_exact(
        text,
        """  simp only [RCLike.inner_apply, Complex.conj_ofReal, starRingEnd_apply,
    NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]
  rw [← hScale]
  ring
""",
        """  simp only [RCLike.inner_apply, Complex.conj_ofReal, starRingEnd_apply,
    NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]
  have hReal :
      star (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ)) =
        (((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ)) := by
    simp
  rw [hReal, ← mul_assoc, ← pow_two, hScale]
  ring
""",
        "FunctionalAnalysis normalize the Euclidean gauge scale before rewriting",
    )
    text = replace_exact(
        text,
        """    simp [HalfWeightCompactCoordinateGreen.rpowScale, upperLift,
      Function.comp_def, hw, dif_pos,
      UpperHalfPlane.ofComplex_apply_of_im_pos, z,
      euclideanRaiseGauge, dx_conj hf z, dy_conj hf z,
      ← starRingEnd_apply, map_add, map_mul,
      Complex.conj_I, Complex.conj_ofReal, heightC, smul_eq_mul]
    ring_nf
""",
        """    simp [HalfWeightCompactCoordinateGreen.rpowScale, upperLift,
      Function.comp_def, hw, dif_pos,
      UpperHalfPlane.ofComplex_apply_of_im_pos, z,
      euclideanRaiseGauge, map_add, map_mul,
      Complex.conj_I, Complex.conj_ofReal, heightC, smul_eq_mul]
    rw [← dx_conj hf z, ← dy_conj hf z]
    norm_num
    ring
""",
        "FunctionalAnalysis orient the raising conjugate derivatives",
    )
    text = replace_exact(
        text,
        """    simp [HalfWeightCompactCoordinateGreen.rpowScale, upperLift,
      Function.comp_def, hw, dif_pos,
      UpperHalfPlane.ofComplex_apply_of_im_pos, z,
      euclideanLowerFromSuccGauge, dx_conj hf z, dy_conj hf z,
      ← starRingEnd_apply, map_add, map_sub, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal, heightC, smul_eq_mul]
    ring_nf
""",
        """    simp [HalfWeightCompactCoordinateGreen.rpowScale, upperLift,
      Function.comp_def, hw, dif_pos,
      UpperHalfPlane.ofComplex_apply_of_im_pos, z,
      euclideanLowerFromSuccGauge, map_add, map_sub, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal, heightC, smul_eq_mul]
    rw [← dx_conj hf z, ← dy_conj hf z]
    norm_num
    ring
""",
        "FunctionalAnalysis orient the lowering conjugate derivatives",
    )
    text = replace_exact(
        text,
        """  all_goals try exact hf
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring_nf
""",
        """  all_goals try exact hf
  push_cast
  ring_nf
""",
        "FunctionalAnalysis remove the exhausted formal-adjoint simplifier",
        expected=2,
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass354 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass354] FunctionalAnalysis zero norm, gauge, localization, and formal-adjoint roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
