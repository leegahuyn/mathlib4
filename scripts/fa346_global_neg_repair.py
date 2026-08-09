from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "a847847aa1ed548a69e3b76e061f4ebfebfeb99cb0538ca491f83ca867d42479"
EXPECTED_OUTPUT_SHA256 = "be21e702089c0de8f9a5a4e5c1af8eb0963869cf93271c469d0516e55caa6fd5"

OLD = """  neg_mem' := by
    intro x hx
    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    simpa only [neg_one_smul] using h
"""

NEW = """  neg_mem' := by
    intro x hx
    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    have hneg :
        (-x : SmoothQuotientCompactFunction) = (-1 : ℂ) • x := by
      apply Subtype.ext
      apply Subtype.ext
      funext z
      simp
    rw [hneg]
    exact h
"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass346-global] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass346-global input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    count = text.count(OLD)
    print(f"global stable-core negation membership: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(
            f"global stable-core negation membership: expected one occurrence, found {count}"
        )
    text = text.replace(OLD, NEW, 1)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass346-global output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass346-global] coherent global negation membership repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
