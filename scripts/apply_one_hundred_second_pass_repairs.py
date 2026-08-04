from __future__ import annotations

import apply_one_hundred_first_pass_repairs as pass101


_original_replace_exact = pass101.replace_exact


def _replace_exact_scoped(
    text: str,
    old: str,
    new: str,
    expected: int,
    label: str,
) -> tuple[str, bool]:
    if label == "FunctionalAnalysis qualify eventual-order antisymmetry":
        start = text.index("theorem gammaTwoOpenCarrier_closure_ae_eq")
        end = text.index("\n\n/-- The closed carrier is still", start)
        block = text[start:end]
        count = block.count(old)
        if count == 1:
            block = block.replace(old, new, 1)
            print(f"{label}: applied 1")
            return text[:start] + block + text[end:], True
        if count == 0 and new in block:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(f"{label}: expected one scoped match, found {count}")

    if label == "FunctionalAnalysis qualify transport of a.e.-equal sets under smul":
        count = text.count(old)
        if count == 2:
            print(f"{label}: applied 2")
            return text.replace(old, new), True
        if count == 0 and text.count(new) == 2:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(f"{label}: expected two matches, found {count}")

    return _original_replace_exact(text, old, new, expected, label)


def main() -> int:
    pass101.replace_exact = _replace_exact_scoped
    try:
        return pass101.main()
    finally:
        pass101.replace_exact = _original_replace_exact


if __name__ == "__main__":
    raise SystemExit(main())
