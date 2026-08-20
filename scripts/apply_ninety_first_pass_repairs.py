from __future__ import annotations

import apply_eighty_ninth_pass_repairs as pass89


_original_replace_exact = pass89.replace_exact


def _replace_exact_with_half_weight_scope(
    text: str,
    old: str,
    new: str,
    expected: int,
    label: str,
) -> tuple[str, bool]:
    if label == "Mock2Advanced keep the measure implicit for half-weight automorphy":
        start = text.index("namespace GenuineWeightedSobolev")
        end = text.index("end GenuineWeightedSobolev", start)
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
            f"{label}: expected one match in GenuineWeightedSobolev, found {count}"
        )
    return _original_replace_exact(text, old, new, expected, label)


def main() -> int:
    pass89.replace_exact = _replace_exact_with_half_weight_scope
    try:
        return pass89.main()
    finally:
        pass89.replace_exact = _original_replace_exact


if __name__ == "__main__":
    raise SystemExit(main())
