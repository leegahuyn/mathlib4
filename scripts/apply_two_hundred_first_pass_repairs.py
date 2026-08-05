from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    text = M2A.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  have hcoeff :
      (-(1 : ℝ) / 2) * (-(1 : ℝ) / 2) = (1 : ℝ) / 4 := by
    norm_num
  simpa [firstDerivative, secondDerivative, mul_assoc, hcoeff] using
    (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2)
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1 <;>
    ring
""",
        "Mock2 Advanced normalize the Whittaker second derivative definitionally",
    )
    M2A.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
