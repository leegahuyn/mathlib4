from __future__ import annotations

import importlib
from pathlib import Path


def normalize_pass59_duplicate_target() -> None:
    path = Path("scripts/apply_fifty_ninth_pass_repairs.py")
    text = path.read_text(encoding="utf-8")
    old = '''        1,
        "Mock1Advanced qualify requirement registry in mem_all_aux",
'''
    new = '''        2,
        "Mock1Advanced qualify requirement registry in mem_all_aux",
'''
    if old in text:
        path.write_text(text.replace(old, new, 1), encoding="utf-8", newline="\n")
        print("Pass 59 duplicate mem_all_aux target count normalized")
    elif new in text:
        print("Pass 59 duplicate mem_all_aux target count already normalized")
    else:
        raise RuntimeError("Pass 59 mem_all_aux target shape changed unexpectedly")


def main() -> int:
    """Apply only the next unmaterialized Lean repair wave."""
    normalize_pass59_duplicate_target()
    pass59 = importlib.import_module("apply_fifty_ninth_pass_repairs")
    return pass59.main()


if __name__ == "__main__":
    raise SystemExit(main())
