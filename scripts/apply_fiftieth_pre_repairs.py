from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock2_Advanced.lean")

OLD = """    DenseRange (coreToTrial M) := by
  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  simp [-SetLike.coe_sort_coe]
"""

NEW = """    DenseRange (coreToTrial M) := by
  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  rw [denseRange_inclusion_iff]
  intro x hx
  exact hx
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(OLD)
    if count == 2:
        text = text.replace(OLD, NEW)
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock2Advanced replace both dense core inclusions: applied 2")
        return 0
    if count == 0 and text.count(NEW) >= 2:
        print("Mock2Advanced dense core inclusions: already applied")
        return 0
    raise RuntimeError(
        f"Mock2Advanced dense core inclusions: expected two old blocks, found {count}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
