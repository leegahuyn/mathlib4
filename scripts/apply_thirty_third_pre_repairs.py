from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")

OLD = """  rademacher_link := by
    intro n
    simp [referenceNormalizedArchCoeff, referenceNormalizedArchRademacher]
"""

NEW = """  rademacher_link := by
    intro n
    rfl
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(OLD)
    if count == 0:
        if NEW in text:
            print("Mock1Advanced normalized Rademacher links: already applied")
            return 0
        print("Mock1Advanced normalized Rademacher links: source changed; skipped")
        return 0
    if count != 2:
        raise RuntimeError(
            f"Mock1Advanced normalized Rademacher links: expected two matches, found {count}")
    PATH.write_text(text.replace(OLD, NEW), encoding="utf-8", newline="\n")
    print("Mock1Advanced normalized Rademacher links: applied 2")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
