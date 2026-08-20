from __future__ import annotations

from pathlib import Path

import apply_one_hundred_third_pass_repairs as pass103

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass103.replace_exact


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """      _ ≤ a + b := add_le_add_left hb a
""",
            """      _ ≤ a + b := add_le_add_right hb a
""",
            "Mock2 orient the first nonnegative-summand inequality",
        ),
        (
            """      _ ≤ a + b := add_le_add_right ha b
""",
            """      _ ≤ a + b := add_le_add_left ha b
""",
            "Mock2 orient the second nonnegative-summand inequality",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass103.main()
    repair_mock2()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
