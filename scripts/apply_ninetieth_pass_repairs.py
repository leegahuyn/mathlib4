from __future__ import annotations

from pathlib import Path

import apply_eighty_ninth_pass_repairs as pass89
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  have hfirst :
      matrixWedge (matrixDifferential g.inverse) g.forward =
        -matrixWedge g.inverse (matrixDifferential g.forward) := by
    abel
""",
        """  have hfirst :
      matrixWedge (matrixDifferential g.inverse) g.forward =
        -matrixWedge g.inverse (matrixDifferential g.forward) := by
    abel_nf at hsum ⊢
    exact hsum
""",
        1,
        "Mock2 derive the inverse differential summand from the zero sum",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass89.main()
    repair_mock2()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
