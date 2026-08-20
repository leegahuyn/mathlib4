from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "21a7329098ae02d52b09749d60ba382b3721b65a423094c79d1e16806eabacd1"
EXPECTED_OUTPUT_SHA256 = "04c17e889dcbd0283ed7c2a7c7aa7a888dbe42b20a50d8dbf1db51d6568a6f62"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass357-r2] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass357-r2 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    old = """  rw [show (Complex.normSq j : ℂ) = star j * j by
    exact Complex.normSq_eq_conj_mul_self]
  simp only [zpow_negSucc, zpow_ofNat]
  field_simp [hj, hjc]
"""
    new = """  rw [show (Complex.normSq j : ℂ) = star j * j by
    exact Complex.normSq_eq_conj_mul_self]
  field_simp [hj, hjc]
"""
    count = text.count(old)
    print(f"FunctionalAnalysis remove exhausted zpow simplifier: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(
            f"expected exactly one exhausted zpow simplifier block, found {count}"
        )
    text = text.replace(old, new)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass357-r2 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass357-r2] FunctionalAnalysis height-square algebra normalized")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
