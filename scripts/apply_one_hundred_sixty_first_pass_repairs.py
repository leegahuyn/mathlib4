from __future__ import annotations

import apply_one_hundred_sixtieth_pass_repairs as pass160

ROOT = pass160.ROOT


def repair_mock2_advanced() -> None:
    pass160.apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """    have hzero :
        ((za - zb : ℤ) : ZMod (Nat.gcd M N)) = 0 := by
      simpa [crtObstructionMap, ZMod.castHom_apply,
        ZMod.cast_intCast] using h
""",
            """    have hzero :
        ((za - zb : ℤ) : ZMod (Nat.gcd M N)) = 0 := by
      change
        (ZMod.cast (za : ZMod M) : ZMod (Nat.gcd M N)) -
          (ZMod.cast (zb : ZMod N) : ZMod (Nat.gcd M N)) = 0 at h
      rw [ZMod.cast_intCast (Nat.gcd_dvd_left M N),
        ZMod.cast_intCast (Nat.gcd_dvd_right M N)] at h
      rw [Int.cast_sub]
      exact h
""",
            1,
            "Mock2Advanced transport CRT integer casts explicitly",
        ),
        (
            "open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory\n",
            "open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory\nopen scoped ZeroObject\n",
            1,
            "Mock2Advanced enable the chosen categorical zero object",
        ),
        (
            "  simp [cyclicFreeComplex, ChainComplex.mk'_d, cyclicFreeSuccessor]\n",
            "  simp [cyclicFreeComplex, ChainComplex.mk'_d, cyclicFreeSuccessor] <;> rfl\n",
            1,
            "Mock2Advanced close the definitionally zero successor differential",
        ),
    ])


def main() -> int:
    pass160.repair_mock2()
    repair_mock2_advanced()
    pass160.repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
