from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")

OLD = """  m_mem := by
    simp [referenceMock1MList]
  r_mem := by
    simp [referenceMock1RPhases]
"""

REPLACEMENTS = [
    """  m_mem := List.Mem.head _
  r_mem := List.Mem.head _
""",
    """  m_mem :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  r_mem := List.Mem.head _
""",
    """  m_mem :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  r_mem := List.Mem.head _
""",
    """  m_mem :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  r_mem := List.Mem.tail _ (List.Mem.head _)
""",
]


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(OLD)
    if count == 4:
        for replacement in REPLACEMENTS:
            text = text.replace(OLD, replacement, 1)
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1Advanced disambiguate four Appell-Lerch parameter blocks: applied 4")
        return 0
    if count == 0 and all(replacement in text for replacement in REPLACEMENTS):
        print("Mock1Advanced disambiguate four Appell-Lerch parameter blocks: already applied")
        return 0
    raise RuntimeError(
        f"Mock1Advanced Appell-Lerch parameter blocks: expected four matches, found {count}")


if __name__ == "__main__":
    raise SystemExit(main())
