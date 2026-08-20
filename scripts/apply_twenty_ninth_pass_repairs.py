from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock2.lean")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    old = """    intro x
    simp [Prop21StandardSequence.zeroToIntersection]
"""
    new = """    intro x
    change 0 = 0
    rfl
"""
    text, did = replace_once(text, old, new,
        "Mock2 reduce the left zero-square evaluation definitionally")
    changed |= did

    old = """    intro x
    simp [Prop21StandardSequence.gcdToZero]
"""
    new = """    intro x
    change 0 = 0
    rfl
"""
    text, did = replace_once(text, old, new,
        "Mock2 reduce the standard right zero-square evaluation definitionally")
    changed |= did

    old = """    intro x
    simp [PhiCokernel.rightEndpoint, PhiCokernel.toZero]
"""
    new = """    intro x
    change 0 = 0
    rfl
"""
    text, did = replace_once(text, old, new,
        "Mock2 reduce the actual right zero-square evaluation definitionally")
    changed |= did

    old = """  simpa only [Nat.cast_mul, coe_unitFactorUnit, mul_comm] using h
"""
    new = """  simpa only [Nat.cast_mul, Nat.cast_pow, coe_unitFactorUnit, mul_comm] using h
"""
    text, did = replace_once(text, old, new,
        "Mock2 normalize the cast of the p-power")
    changed |= did

    old = """  rw [M_cast_eq_unit_mul_padicPower M p k hM hp, mul_assoc,
    Units.mul_left_eq_zero]
"""
    new = """  rw [M_cast_eq_unit_mul_padicPower M p k hM hp, mul_assoc,
    Units.mul_right_eq_zero]
"""
    text, did = replace_once(text, old, new,
        "Mock2 cancel the left unit with the correctly oriented lemma")
    changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
