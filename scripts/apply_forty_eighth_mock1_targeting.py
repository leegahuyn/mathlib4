from __future__ import annotations

from pathlib import Path

from apply_forty_seventh_pass_repairs import repair_mock1_advanced

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")
ORIGINAL = "theorem sectionOf_objectSchema_at\n"
TEMPORARY = "theorem __repair47_first_sectionOf_objectSchema_at\n"


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(ORIGINAL)
    if count == 2:
        text = text.replace(ORIGINAL, TEMPORARY, 1)
        PATH.write_text(text, encoding="utf-8", newline="\n")
        try:
            repair_mock1_advanced()
        finally:
            restored = PATH.read_text(encoding="utf-8")
            if TEMPORARY not in restored:
                raise RuntimeError(
                    "Mock1Advanced temporary targeting marker disappeared"
                )
            restored = restored.replace(TEMPORARY, ORIGINAL, 1)
            PATH.write_text(restored, encoding="utf-8", newline="\n")
        print("Mock1Advanced targeted the second stage-II registry block")
        return 0
    if count == 1 and "private theorem mem_all_aux" in text:
        print("Mock1Advanced stage-II registry block: already repaired")
        return 0
    raise RuntimeError(
        f"Mock1Advanced stage-II targeting expected two theorem names, found {count}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
