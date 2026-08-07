from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "c562c864be74e94e618ad3ad54dd7ee6442f81d17bc748754782718f4f7ca0e0"
EXPECTED_OUTPUT_SHA256 = "d597cae94651c8224a500663c8ea4adea412fb0c970a1053f16f9edf525cefc4"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass342b] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342b input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    old = """    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    simpa only [neg_one_smul] using h
"""
    new = """    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    have hNeg : (-1 : ℂ) • x = -x := by
      apply Subtype.ext
      apply Subtype.ext
      funext z
      simp
    rw [← hNeg]
    exact h
"""
    count = text.count(old)
    print(f"stable-core negation extensionality: expected=2 actual={count}")
    if count != 2:
        raise RuntimeError(
            f"stable-core negation extensionality: expected 2, found {count}"
        )
    text = text.replace(old, new)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342b output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass342b] stable-core scalar negation bridged extensionally")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
