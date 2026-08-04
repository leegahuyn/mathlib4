from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock2.lean")


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    old = """  norm_num only [Int.cast_natCast]
  simpa only [Nat.cast_mul, Nat.cast_pow] using h
"""
    new = """  change
    (((p ^ shiftExponent M p k) *
        (p ^ thicknessExponent M p k) : ℕ) : ZMod (Pk p k)) = 0
  exact h
"""

    count = text.count(old)
    if count == 1:
        PATH.write_text(text.replace(old, new, 1), encoding="utf-8", newline="\n")
        print("Mock2 normalize the power-shift modulus goal to the natural cast: applied")
        return 0
    if new in text:
        print("Mock2 power-shift modulus normalization: already applied")
        return 0

    raise RuntimeError(
        "Mock2 power-shift modulus proof did not match the expected repaired source"
    )


if __name__ == "__main__":
    raise SystemExit(main())
