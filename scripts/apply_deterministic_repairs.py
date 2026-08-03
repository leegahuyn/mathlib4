from __future__ import annotations

import re
from pathlib import Path


ROOT = Path("PrimalitySheafVerification")
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+\S")


def repair_spt1() -> bool:
    path = ROOT / "Spt1.lean"
    text = path.read_text(encoding="utf-8")
    original = text

    replacements = (
        (
            "padicValRat.pow (p := p) (q := (-1 : ℚ)) hm1,",
            "padicValRat.pow (p := p) (-1 : ℚ),",
        ),
        (
            "padicValRat.pow (p := p) (q := (u : ℚ)) huq,",
            "padicValRat.pow (p := p) (u : ℚ),",
        ),
        (
            "padicValRat.pow (p := p) (q := u) hu0,",
            "padicValRat.pow (p := p) u,",
        ),
        (
            "≤ X.minFac * (X / X.minFac) := mul_le_mul_left' h _",
            "≤ X.minFac * (X / X.minFac) := Nat.mul_le_mul_left X.minFac h",
        ),
    )

    for old, new in replacements:
        count = text.count(old)
        if count:
            print(f"Spt1: replacing {count} occurrence(s): {old}")
            text = text.replace(old, new)

    if text != original:
        path.write_text(text, encoding="utf-8", newline="\n")
        return True

    print("Spt1: deterministic API repairs already applied")
    return False


def repair_qym_import() -> bool:
    path = ROOT / "QYM.lean"
    text = path.read_text(encoding="utf-8-sig")
    lines = text.splitlines()

    import_indices = [
        index for index, line in enumerate(lines)
        if IMPORT_RE.match(line)
    ]
    if not import_indices:
        print("QYM: no import command found; source left unchanged")
        return False

    first_nonempty_index = next(
        (index for index, line in enumerate(lines) if line.strip()),
        len(lines),
    )
    leading_imports = list(range(first_nonempty_index, first_nonempty_index + len(import_indices)))
    if import_indices == leading_imports:
        print("QYM: all imports are already the first commands")
        return False

    import_index_set = set(import_indices)
    imports = [lines[index].strip() for index in import_indices]
    remaining = [
        line for index, line in enumerate(lines)
        if index not in import_index_set
    ]
    while remaining and not remaining[0].strip():
        remaining.pop(0)

    repaired = "\n".join(imports) + "\n\n" + "\n".join(remaining).rstrip() + "\n"
    path.write_text(repaired, encoding="utf-8", newline="\n")
    locations = ", ".join(str(index + 1) for index in import_indices)
    print(f"QYM: moved import command(s) from line(s) {locations} to the beginning")
    return True


def main() -> int:
    changed = repair_spt1()
    changed = repair_qym_import() or changed
    print("Deterministic repairs changed sources." if changed else "No source changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
