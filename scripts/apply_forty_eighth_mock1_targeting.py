from __future__ import annotations

from pathlib import Path

from apply_forty_seventh_pass_repairs import repair_mock1_advanced

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")
THEOREM_ORIGINAL = "theorem sectionOf_objectSchema_at\n"
THEOREM_TEMPORARY = "theorem __repair47_first_sectionOf_objectSchema_at\n"
FIELD_ORIGINAL = "  paper_object_data_instance :\n"
FIELD_TEMPORARY = "  __repair47_pre_audit_paper_object_data_instance :\n"


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    theorem_count = text.count(THEOREM_ORIGINAL)
    field_count = text.count(FIELD_ORIGINAL)

    if theorem_count == 2 and field_count == 4:
        text = text.replace(THEOREM_ORIGINAL, THEOREM_TEMPORARY, 1)
        text = text.replace(FIELD_ORIGINAL, FIELD_TEMPORARY, 3)
        PATH.write_text(text, encoding="utf-8", newline="\n")
        try:
            repair_mock1_advanced()
        finally:
            restored = PATH.read_text(encoding="utf-8")
            if THEOREM_TEMPORARY not in restored:
                raise RuntimeError(
                    "Mock1Advanced temporary theorem targeting marker disappeared"
                )
            if restored.count(FIELD_TEMPORARY) != 3:
                raise RuntimeError(
                    "Mock1Advanced temporary audit-field targeting markers disappeared"
                )
            restored = restored.replace(THEOREM_TEMPORARY, THEOREM_ORIGINAL, 1)
            restored = restored.replace(FIELD_TEMPORARY, FIELD_ORIGINAL)
            PATH.write_text(restored, encoding="utf-8", newline="\n")
        print("Mock1Advanced targeted the second registry and fourth audit block")
        return 0

    if theorem_count == 1 and "private theorem mem_all_aux" in text:
        print("Mock1Advanced stage-II registry and audit blocks: already repaired")
        return 0

    raise RuntimeError(
        "Mock1Advanced targeting expected two theorem names and four audit fields, "
        f"found {theorem_count}/{field_count}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
