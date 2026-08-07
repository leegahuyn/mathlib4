from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "674037f3e75131b8b64d583fc2d8210f264ddc814324ee84ea276166ccaeddf5"
EXPECTED_OUTPUT_SHA256 = "b6bbe2d8a656573150b4dbaf8ecbe8f640b10e13cccd834dacc8b0404223e6bf"


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
        print("[pass332] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass332 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    # PASS331's direct compiler run no longer reports the earlier fixed-phase
    # algebra-instance failure, so do not reintroduce local instances here.
    # Keep PASS332 limited to four independently observed first-frontier errors.
    replacements = [
        (
            """  simpa only [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance
        compactInverseEtaOrbitZeroWeightCore γ z
""",
            """  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance
        compactInverseEtaOrbitZeroWeightCore γ z
""",
            "FunctionalAnalysis orbit-zero covariance bridge",
        ),
        (
            """  simpa only [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance u γ z
""",
            """  simpa [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance u γ z
""",
            "FunctionalAnalysis raw covariance bridge",
        ),
        (
            """theorem constantCompactCuspTail_tail_norm_eq_zero
    (C : ContinuousSesquilinearForm H) (hC : IsCompactOperator C) (n : ℕ) :
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  have hNorm := congrArg norm
    (constantCompactCuspTail_tail_eq_zero C hC n)
  simpa only [norm_zero] using hNorm
""",
            """theorem constantCompactCuspTail_tail_norm_eq_zero
    (C : ContinuousSesquilinearForm H) (hC : IsCompactOperator C) (n : ℕ) :
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  calc
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = ‖(0 : ContinuousSesquilinearForm H)‖ :=
      congrArg norm (constantCompactCuspTail_tail_eq_zero C hC n)
    _ = 0 := norm_zero
""",
            "FunctionalAnalysis exact-tail norm explicit calc",
        ),
        (
            """      simpa only [sub_eq_add_neg] using
        (upstairsCuspCutoff_quotientCompact (N + 1)).add
          ((upstairsCuspCutoff_quotientCompact N).smul (-1))
""",
            """      simpa only [sub_eq_add_neg, neg_smul, one_smul] using
        (upstairsCuspCutoff_quotientCompact (N + 1)).add
          ((upstairsCuspCutoff_quotientCompact N).smul (-1))
""",
            "FunctionalAnalysis partition compact support scalar normalization",
        ),
    ]

    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass332 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass332] FunctionalAnalysis first observed type frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
