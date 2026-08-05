from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(
            f"{label}: expected exactly {expected} match(es), found {count}"
        )
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """    _ = (denominatorUnit γ τ)⁻¹ *
        (etaRatioUnit γ τ ^ 2 * (etaRatioUnit γ τ ^ 2)⁻¹) := by
      rw [mul_inv_rev]
      ac_rfl
""",
        """    _ = (denominatorUnit γ τ)⁻¹ *
        (etaRatioUnit γ τ ^ 2 * (etaRatioUnit γ τ ^ 2)⁻¹) := by
      rw [_root_.mul_inv_rev]
      ac_rfl
""",
        "Mock2 disambiguate the group inverse multiplication lemma",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
