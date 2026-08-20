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

    old = """  norm_num only [Int.cast_natCast]
  simpa only [Nat.cast_mul, Nat.cast_pow] using h
"""
    new = """  change
    (((p ^ shiftExponent M p k) *
        (p ^ thicknessExponent M p k) : ℕ) : ZMod (Pk p k)) = 0
  exact h
"""
    text, did = replace_once(
        text, old, new,
        "Mock2 normalize the power-shift modulus goal to the natural cast")
    changed |= did

    old = """  change powerShiftIntegerHom M p k z = _
  exact powerShiftIntegerHom_apply M p k z
"""
    new = """  simpa only [powerShiftHom] using
    (ZMod.lift_coe (p ^ thicknessExponent M p k)
      ⟨powerShiftIntegerHom M p k,
        powerShiftIntegerHom_modulus_eq_zero M p k⟩ z)
"""
    text, did = replace_once(
        text, old, new,
        "Mock2 compute the lifted map on an integer representative")
    changed |= did

    old = """    rw [← Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff _ _).2
      (Pk_dvd_M_mul_shift M p k hM hp)
"""
    new = """    have hcast :
        ((M * p ^ shiftExponent M p k : ℕ) : ZMod (Pk p k)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2
        (Pk_dvd_M_mul_shift M p k hM hp)
    simpa only [Nat.cast_mul, Nat.cast_pow] using hcast
"""
    text, did = replace_once(
        text, old, new,
        "Mock2 normalize kernel divisibility through a natural cast")
    changed |= did

    old = """    norm_num only [Int.cast_natCast] at *
    simpa only [Int.cast_mul, Nat.cast_pow] using hz
"""
    new = """    simpa only [Int.cast_mul, Int.cast_natCast,
      Nat.cast_pow] using hz
"""
    text, did = replace_once(
        text, old, new,
        "Mock2 normalize the injectivity integer product cast")
    changed |= did

    old = """    have hpz' :
        ((((p ^ valuationExponent M p : ℕ) : ℤ) * z : ℤ) :
          ZMod (Pk p k)) = 0 := by
      norm_num only [Int.cast_natCast] at *
    simpa only [Int.cast_mul, Nat.cast_pow] using hpz
"""
    new = """    have hpz' :
        ((((p ^ valuationExponent M p : ℕ) : ℤ) * z : ℤ) :
          ZMod (Pk p k)) = 0 := by
      simpa only [Int.cast_mul, Int.cast_natCast,
        Nat.cast_pow] using hpz
"""
    text, did = replace_once(
        text, old, new,
        "Mock2 restore the surjectivity cast proof inside its branch")
    changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
