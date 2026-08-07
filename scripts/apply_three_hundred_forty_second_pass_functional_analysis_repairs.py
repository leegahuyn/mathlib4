from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "df78d684944e2963d4fce2169f281192836c101d2fe8b22669fd11c069539fa5"
EXPECTED_OUTPUT_SHA256 = "b0d4f65b829992910bddf838ddaeb179a32da57c1f306b623fed0086d511add5"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_required(text: str, old: str, new: str, label: str, expected: int) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_required(
        text,
        "simp only [map_add, add_apply, mul_add]",
        "simp only [map_add, Pi.add_apply, mul_add]",
        "FunctionalAnalysis evaluate section addition pointwise",
        2,
    )
    text = replace_required(
        text,
        "simp only [map_smul, smul_eq_mul]\n    ring",
        "simp only [map_smul, Pi.smul_apply, smul_eq_mul]\n    ring",
        "FunctionalAnalysis evaluate section scalar multiplication pointwise",
        2,
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass342] FunctionalAnalysis pointwise linear-map laws repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
