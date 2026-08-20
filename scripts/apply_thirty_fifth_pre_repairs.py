from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")

OLD = """  rademacher_link := by
    intro n
    rfl
"""

FIRST = """  rademacher_link := by
    intro n
    exact referenceNormalizedArchRademacher.coeff_eq n
"""

SECOND = """  rademacher_link := by
    intro n
    exact referenceNormalizedCoefficientFormula.rademacher.coeff_eq n
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(OLD)
    if count == 2:
        text = text.replace(OLD, FIRST, 1)
        text = text.replace(OLD, SECOND, 1)
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1Advanced disambiguate normalized Rademacher links: applied 2")
        return 0
    if count == 0 and FIRST in text and SECOND in text:
        print("Mock1Advanced disambiguate normalized Rademacher links: already applied")
        return 0
    raise RuntimeError(
        f"Mock1Advanced disambiguate normalized Rademacher links: expected two old blocks, found {count}")


if __name__ == "__main__":
    raise SystemExit(main())
