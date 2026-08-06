from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """/-- Underlying Type-valued morphism of the left overlap map. -/
def equation613LeftType : LocalFamily C ⟶ OverlapFamily C :=
  fun s => equation613Left C s

/-- Underlying Type-valued morphism of the right overlap map. -/
def equation613RightType : LocalFamily C ⟶ OverlapFamily C :=
  fun s => equation613Right C s
""",
        """/-- Underlying Type-valued morphism of the left overlap map. -/
def equation613LeftType : LocalFamily C ⟶ OverlapFamily C := by
  change LocalFamily C → OverlapFamily C
  exact fun s => equation613Left C s

/-- Underlying Type-valued morphism of the right overlap map. -/
def equation613RightType : LocalFamily C ⟶ OverlapFamily C := by
  change LocalFamily C → OverlapFamily C
  exact fun s => equation613Right C s
""",
        "Mock2 force equation 6.13 maps into the Type category",
    )
    m2 = replace_exact(
        m2,
        "equation613LeftType C",
        "(equation613LeftType C)",
        "Mock2 parenthesize the left Type morphism at every categorical use",
        expected=14,
    )
    m2 = replace_exact(
        m2,
        "equation613RightType C",
        "(equation613RightType C)",
        "Mock2 parenthesize the right Type morphism at every categorical use",
        expected=14,
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
