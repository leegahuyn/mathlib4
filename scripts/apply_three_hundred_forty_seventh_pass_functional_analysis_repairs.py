from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "fd80630d62f9fb72c101c83ced4b19f47256e0601595642ed93cd7b4d058b464"
EXPECTED_OUTPUT_SHA256 = "3f8e5343e30ab2ce324fbde38e21cdd4289b8faf527a04c8529f28b06e6012f0"


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
        print("[pass347] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass347 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        """theorem hyperbolicDensity_ne_zero (z : ℍ) :
    (hyperbolicDensity z : ℝ≥0∞) ≠ 0 :=
  ENNReal.coe_ne_zero.mpr <| pow_ne_zero 2 <|
    div_ne_zero one_ne_zero
      (NNReal.ne_iff.mp z.im_ne_zero)
""",
        """theorem hyperbolicDensity_ne_zero (z : ℍ) :
    (hyperbolicDensity z : ℝ≥0∞) ≠ 0 := by
  apply ENNReal.coe_ne_zero.mpr
  apply pow_ne_zero
  exact div_ne_zero one_ne_zero <| by
    intro h
    apply z.im_ne_zero
    exact congrArg (fun r : NNReal => (r : ℝ)) h
""",
        "FunctionalAnalysis prove the hyperbolic density is nonzero through coercion",
    )
    text = replace_once(
        text,
        """  have hnot : ∀ᵐ z ∂upperEuclideanMeasure,
      z ∉ chosenGammaTwoFundamentalDomain.carrier \\
        gammaTwoOpenCarrier := by
    rw [ae_iff]
    simpa only [not_not, Set.mem_setOf_eq] using
      chosenCarrier_diff_open_null_upperEuclidean
""",
        """  have hnot : ∀ᵐ z ∂upperEuclideanMeasure,
      z ∉ chosenGammaTwoFundamentalDomain.carrier \\
        gammaTwoOpenCarrier := by
    rw [ae_iff]
    convert chosenCarrier_diff_open_null_upperEuclidean using 1
    ext z
    simp
""",
        "FunctionalAnalysis identify the null carrier difference extensionally",
    )

    standalone_conj = re.compile(
        r"(?<![A-Za-z0-9_])Complex\.conj(?![A-Za-z0-9_])"
    )
    count = len(standalone_conj.findall(text))
    print(f"FunctionalAnalysis standalone Complex.conj: expected=25 actual={count}")
    if count != 25:
        raise RuntimeError(
            f"expected 25 standalone Complex.conj occurrences, found {count}"
        )
    text = standalone_conj.sub("star", text)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass347 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass347] FunctionalAnalysis density, ae-set, and star API roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
