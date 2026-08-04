from __future__ import annotations

import importlib
from pathlib import Path


def normalize_pass59_duplicate_targets() -> None:
    path = Path("scripts/apply_fifty_ninth_pass_repairs.py")
    text = path.read_text(encoding="utf-8")
    replacements = [
        (
            '''        1,
        "Mock1Advanced qualify requirement registry in mem_all_aux",
''',
            '''        2,
        "Mock1Advanced qualify requirement registry in mem_all_aux",
''',
            "mem_all_aux",
        ),
        (
            '''        1,
        "Mock2 normalize the zero image in resolution exactness",
''',
            '''        2,
        "Mock2 normalize the zero image in resolution exactness",
''',
            "Mock2 zero-image",
        ),
    ]
    changed = False
    for old, new, label in replacements:
        if old in text:
            text = text.replace(old, new, 1)
            changed = True
            print(f"Pass 59 duplicate {label} target count normalized")
        elif new in text:
            print(f"Pass 59 duplicate {label} target count already normalized")
        else:
            raise RuntimeError(f"Pass 59 {label} target shape changed unexpectedly")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    """Apply only the next unmaterialized Lean repair wave."""
    normalize_pass59_duplicate_targets()
    pass59 = importlib.import_module("apply_fifty_ninth_pass_repairs")
    return pass59.main()


if __name__ == "__main__":
    raise SystemExit(main())
