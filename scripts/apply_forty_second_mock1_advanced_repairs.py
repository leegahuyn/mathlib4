from __future__ import annotations

import apply_forty_first_pass_repairs as pass41


def main() -> int:
    original_replace_all = pass41.replace_all

    def replace_all_with_current_group_count(
        text: str,
        old: str,
        new: str,
        expected: int,
        label: str,
    ) -> tuple[str, bool]:
        if (
            label.startswith("Mock1Advanced prove both ")
            and label.endswith(" section maps from membership")
        ):
            expected = 1
        return original_replace_all(text, old, new, expected, label)

    pass41.replace_all = replace_all_with_current_group_count
    try:
        pass41.repair_mock1_advanced()
    finally:
        pass41.replace_all = original_replace_all
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
