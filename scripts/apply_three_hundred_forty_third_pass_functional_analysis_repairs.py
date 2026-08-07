from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "b0d4f65b829992910bddf838ddaeb179a32da57c1f306b623fed0086d511add5"
EXPECTED_OUTPUT_SHA256 = "b08f67384828a0bbbd8621552a7feb92462271eaba83b2db6eaa4eaf8f7c8f1f"


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
        print("[pass343] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass343 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_required(
        text,
        """  have hCov :=
    SmoothCompactWeightCore.covariance
      compactInverseEtaOrbitZeroWeightCore γ z
  simpa [compactInverseEtaOrbitZeroSmoothQuotient,""",
        """  have hCov :=
    SmoothCompactWeightCore.covariance
      compactInverseEtaOrbitZeroWeightCore γ z
  rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov
  simpa [compactInverseEtaOrbitZeroSmoothQuotient,""",
        "FunctionalAnalysis restore orbit-zero covariance transport",
    )
    text = replace_required(
        text,
        """  have hCov := SmoothCompactWeightCore.covariance u γ z
  simpa [rawOfSmoothCompactWeightCore,""",
        """  have hCov := SmoothCompactWeightCore.covariance u γ z
  rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov
  simpa [rawOfSmoothCompactWeightCore,""",
        "FunctionalAnalysis restore raw covariance transport",
    )
    text = replace_required(
        text,
        """    _ = 0 := by
      simp

end ExactTail""",
        """    _ = 0 :=
      (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)

end ExactTail""",
        "FunctionalAnalysis restore typed zero sesquilinear norm",
    )
    text = replace_required(
        text,
        "simp only [map_add, Pi.add_apply, mul_add]",
        "simp only [map_add, WeightSection.add_apply, mul_add]",
        "FunctionalAnalysis use WeightSection addition evaluation",
        expected=2,
    )
    text = replace_required(
        text,
        "simp only [map_smul, Pi.smul_apply, smul_eq_mul]",
        "simp only [map_smul, WeightSection.smul_apply, smul_eq_mul]",
        "FunctionalAnalysis use WeightSection scalar evaluation",
        expected=2,
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass343 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass343] FunctionalAnalysis covariance, typed zero norm, "
        "and WeightSection pointwise roots repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
