from __future__ import annotations

import apply_forty_fourth_pass_repairs as pass44


def main() -> int:
    original_replace_once = pass44.replace_once

    def replace_once_targeting_canonical_norm(
        text: str,
        old: str,
        new: str,
        label: str,
    ) -> tuple[str, bool]:
        if label == (
            "FunctionalAnalysis specify the operator type in canonical norm nonnegativity"
        ):
            count = text.count(old)
            if count == 2:
                print(f"{label}: applied first of two contextual occurrences")
                return text.replace(old, new, 1), True
        return original_replace_once(text, old, new, label)

    pass44.replace_once = replace_once_targeting_canonical_norm
    try:
        pass44.main()
    finally:
        pass44.replace_once = original_replace_once
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
