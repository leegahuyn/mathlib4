from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock2_Advanced.lean")

OLD = """    simpa [forward, backward, Function.comp_def] using hcomp.symm
"""

FORWARD_BACKWARD = """    change
      (Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm)
          ((Lp.compMeasurePreserving (⇑chart.coord) hcoord) F) = F
    simpa [Function.comp_def] using hcomp.symm
"""

BACKWARD_FORWARD = """    change
      (Lp.compMeasurePreserving (⇑chart.coord) hcoord)
          ((Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm) u) = u
    simpa [Function.comp_def] using hcomp.symm
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(OLD)
    if count == 2:
        text = text.replace(OLD, FORWARD_BACKWARD, 1)
        text = text.replace(OLD, BACKWARD_FORWARD, 1)
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock2Advanced disambiguate the two Lp composition proofs: applied 2")
        return 0
    if count == 0 and FORWARD_BACKWARD in text and BACKWARD_FORWARD in text:
        print("Mock2Advanced disambiguate the two Lp composition proofs: already applied")
        return 0
    raise RuntimeError(
        f"Mock2Advanced Lp composition proofs: expected two old blocks, found {count}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
