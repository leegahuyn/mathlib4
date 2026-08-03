from __future__ import annotations

from pathlib import Path
import sys

PATH = Path("PrimalitySheafVerification/Spt1.lean")

REPLACEMENTS = [
    (
        "padicValRat.pow (p := p) (q := (-1 : ℚ)) hm1,",
        "padicValRat.pow (p := p) (-1 : ℚ),",
        "Update padicValRat.pow to its current API: the theorem no longer takes a nonzero proof.",
    ),
    (
        "padicValRat.pow (p := p) (q := (u : ℚ)) huq,",
        "padicValRat.pow (p := p) (u : ℚ),",
        "Update the integer-cast p-adic valuation power rewrite to the current API.",
    ),
    (
        "padicValRat.pow (p := p) (q := u) hu0,",
        "padicValRat.pow (p := p) u,",
        "Update the rational p-adic valuation power rewrite to the current API.",
    ),
    (
        "≤ X.minFac * (X / X.minFac) := mul_le_mul_left' h _",
        "≤ X.minFac * (X / X.minFac) := Nat.mul_le_mul_left X.minFac h",
        "Replace the removed generic lemma with the current Nat lemma.",
    ),
]


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    for old, new, reason in REPLACEMENTS:
        old_count = text.count(old)
        new_count = text.count(new)

        if old_count == 1:
            text = text.replace(old, new, 1)
            changed = True
            print(f"APPLIED: {reason}")
        elif old_count == 0 and new_count == 1:
            print(f"ALREADY APPLIED: {reason}")
        else:
            print(
                f"REFUSING: expected exactly one old or one new occurrence; "
                f"old={old_count}, new={new_count}: {reason}",
                file=sys.stderr,
            )
            return 1

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print(f"Updated {PATH}")
    else:
        print("No changes needed.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
