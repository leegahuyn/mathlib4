from __future__ import annotations

from pathlib import Path


ROOT = Path("PrimalitySheafVerification")


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
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    import_indices = [
        index for index, line in enumerate(lines)
        if line.strip() == "import Mathlib"
    ]
    if not import_indices:
        raise RuntimeError("QYM.lean has no exact `import Mathlib` command")

    first_nonempty = next((line.strip() for line in lines if line.strip()), "")
    if first_nonempty == "import Mathlib":
        print("QYM: import is already the first command")
        return False

    import_index = import_indices[0]
    del lines[import_index]
    while lines and not lines[0].strip():
        del lines[0]

    repaired = "import Mathlib\n\n" + "\n".join(lines) + "\n"
    path.write_text(repaired, encoding="utf-8", newline="\n")
    print(f"QYM: moved import Mathlib from line {import_index + 1} to line 1")
    return True


def main() -> int:
    changed = repair_spt1()
    changed = repair_qym_import() or changed
    print("Deterministic repairs changed sources." if changed else "No source changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
