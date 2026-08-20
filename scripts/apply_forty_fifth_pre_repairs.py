from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")

OLD = """  exact norm_nonneg _
"""

NEW = """  exact norm_nonneg
    (d.canonicalSolutionOperator : A.range →L[ℂ] V)
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(OLD)
    if count == 2:
        text = text.replace(OLD, NEW)
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("FunctionalAnalysis type both canonical norm nonnegativity proofs: applied 2")
        return 0
    if count == 0 and text.count(NEW) >= 2:
        print("FunctionalAnalysis canonical norm nonnegativity proofs: already applied")
        return 0
    raise RuntimeError(
        f"FunctionalAnalysis canonical norm nonnegativity proofs: expected two old blocks, found {count}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
