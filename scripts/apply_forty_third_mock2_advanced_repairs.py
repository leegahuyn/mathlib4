from __future__ import annotations

import apply_forty_first_pass_repairs as pass41


def main() -> int:
    original_replace_once = pass41.replace_once

    def replace_once_allowing_first_of_pair(
        text: str,
        old: str,
        new: str,
        label: str,
    ) -> tuple[str, bool]:
        if label == "Mock2Advanced expose the forward-backward Lp composition":
            count = text.count(old)
            if count == 2:
                print(f"{label}: applied first of pair")
                return text.replace(old, new, 1), True
        return original_replace_once(text, old, new, label)

    pass41.replace_once = replace_once_allowing_first_of_pair
    try:
        pass41.repair_mock2_advanced()
    finally:
        pass41.replace_once = original_replace_once
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
