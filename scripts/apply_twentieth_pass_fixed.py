from __future__ import annotations

import apply_twentieth_pass_repairs as pass20


_original_replace_once = pass20.replace_once


def _replace_once_with_release_field_disambiguation(
    text: str, old: str, new: str, label: str
) -> tuple[str, bool]:
    if label == "Mock1Advanced bind the release shadow theorem universe":
        count = text.count(old)
        if count == 0:
            if new in text:
                print(f"{label}: already applied")
                return text, False
            print(f"{label}: source changed; skipped")
            return text, False
        print(f"{label}: applied to the release-envelope field only ({count} candidates)")
        return text.replace(old, new, 1), True
    return _original_replace_once(text, old, new, label)


def main() -> int:
    pass20.replace_once = _replace_once_with_release_field_disambiguation
    return pass20.main()


if __name__ == "__main__":
    raise SystemExit(main())
