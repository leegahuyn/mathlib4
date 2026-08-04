from __future__ import annotations

import apply_seventy_first_pass_repairs as pass71


_original_replace_exact = pass71.replace_exact


def _replace_exact_with_corrected_sqrt_count(
    text: str,
    old: str,
    new: str,
    expected: int,
    label: str,
) -> tuple[str, bool]:
    """Correct the pass-71 count for the remaining sqrt-factor calls.

    The retained repair chain leaves seven occurrences of
    `a.sqrtFactor_ne_zero`, not three.  All seven are the same obsolete
    field-notation call targeted by pass 71.
    """
    if (
        label == "Mock2Advanced replace three remaining square-root field-notation calls"
        and old == "a.sqrtFactor_ne_zero"
        and expected == 3
    ):
        expected = 7
    return _original_replace_exact(text, old, new, expected, label)


def main() -> int:
    pass71.replace_exact = _replace_exact_with_corrected_sqrt_count
    try:
        return pass71.main()
    finally:
        pass71.replace_exact = _original_replace_exact


if __name__ == "__main__":
    raise SystemExit(main())
