from __future__ import annotations

import apply_ninety_first_pass_repairs as pass91


_original_replace_exact = pass91._original_replace_exact


def _replace_exact_with_vertical_line_scope(
    text: str,
    old: str,
    new: str,
    expected: int,
    label: str,
) -> tuple[str, bool]:
    if label == "FunctionalAnalysis expose product Lebesgue measure on a vertical line":
        start = text.index("theorem complex_verticalLine_null")
        end = text.index("\n\n/-- The part of the closed modular tile", start)
        block = text[start:end]
        count = block.count(old)
        if count == 1:
            block = block.replace(old, new, 1)
            print(f"{label}: applied 1")
            return text[:start] + block + text[end:], True
        if count == 0 and new in block:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(
            f"{label}: expected one match in complex_verticalLine_null, found {count}"
        )
    return _original_replace_exact(text, old, new, expected, label)


def main() -> int:
    pass91._original_replace_exact = _replace_exact_with_vertical_line_scope
    try:
        return pass91.main()
    finally:
        pass91._original_replace_exact = _original_replace_exact


if __name__ == "__main__":
    raise SystemExit(main())
