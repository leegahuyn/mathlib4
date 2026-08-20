from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "b6bbe2d8a656573150b4dbaf8ecbe8f640b10e13cccd834dacc8b0404223e6bf"
EXPECTED_OUTPUT_SHA256 = "8c0b0797155d3ae4f8f05b2d38d36552a629c900b8e990aba1ff44b666b72e45"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def operator_block(name: str, cutoff: str, invariant: str, repaired: bool) -> str:
    if not repaired:
        proof = """  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    rfl
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    rfl
"""
    else:
        proof = """  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    simp [invariantCutoffTimesOrbitSection_apply,
      InverseEtaFixedPhaseCore.toWeightSection_apply, mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    simp [invariantCutoffTimesOrbitSection_apply,
      InverseEtaFixedPhaseCore.toWeightSection_apply]
    ring
"""
    return f"""noncomputable def {name} (N : ℕ) (n : ℤ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ] InverseEtaFixedPhaseCore n where
  toFun u :=
    invariantCutoffTimesOrbitSection n
      ({cutoff})
      ({invariant})
      (InverseEtaFixedPhaseCore.toWeightSection n u)
      (u : SmoothQuotientCompactFunction).1.2
{proof}"""


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass333] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass333 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    specs = [
        (
            "cuspCutoffOperator",
            "cuspCutoffSmoothQuotient N",
            "cuspCutoffSmoothQuotient_invariant N",
            "FunctionalAnalysis cusp cutoff operator linearity",
        ),
        (
            "cuspPartitionPieceOperator",
            "cuspPartitionPieceSmoothQuotient N",
            "cuspPartitionPieceSmoothQuotient_invariant N",
            "FunctionalAnalysis cusp partition operator linearity",
        ),
    ]
    for name, cutoff, invariant, label in specs:
        text = replace_once(
            text,
            operator_block(name, cutoff, invariant, False),
            operator_block(name, cutoff, invariant, True),
            label,
        )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass333 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass333] FunctionalAnalysis cutoff-operator linearity frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
