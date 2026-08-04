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

    replacements = [
        ("""  τ₁ := 𝟙 Prop21StandardSequence.zeroObject
  τ₂ := AddCommGrpCat.ofHom (intersectionRestriction hM hN)
  τ₃ := 𝟙 Prop21StandardSequence.integerObject
  comm₁₂ := by
    exact (zero_comp _).symm
""",
         """  τ₁ := 0
  τ₂ := AddCommGrpCat.ofHom (intersectionRestriction hM hN)
  τ₃ := 𝟙 Prop21StandardSequence.integerObject
  comm₁₂ := by simp
""",
         "Mock2 use the unique zero morphism at the left endpoint"),
        ("""  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)
  τ₂ := AddCommGrpCat.ofHom (gcdRestriction hM hN)
  τ₃ := 𝟙 Prop21StandardSequence.zeroObject
""",
         """  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)
  τ₂ := AddCommGrpCat.ofHom (gcdRestriction hM hN)
  τ₃ := 0
""",
         "Mock2 use the unique zero morphism at the standard right endpoint"),
        ("""  comm₂₃ := by
    exact comp_zero _

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         """  comm₂₃ := by simp

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         "Mock2 close the standard right zero square definitionally"),
        ("""  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)
  τ₂ := AddCommGrpCat.ofHom (cokernelMap hM hN)
  τ₃ := 𝟙 Prop21StandardSequence.zeroObject
""",
         """  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)
  τ₂ := AddCommGrpCat.ofHom (cokernelMap hM hN)
  τ₃ := 0
""",
         "Mock2 use the unique zero morphism at the actual right endpoint"),
        ("""  comm₂₃ := by
    exact comp_zero _

/-- Auditable statement of the proven naturality range. -/
""",
         """  comm₂₃ := by simp

/-- Auditable statement of the proven naturality range. -/
""",
         "Mock2 close the actual right zero square definitionally"),
        ("""  rw [quotientToAmbientHom_intCast]
  simpa only [Int.cast_mul] using
    congrArg (fun t : ℤ => (t : ZMod N)) hq.symm
""",
         """  rw [quotientToAmbientHom_intCast]
  simpa only [Int.cast_mul, Int.cast_natCast] using
    congrArg (fun t : ℤ => (t : ZMod N)) hq.symm
""",
         "Mock2 normalize the natural quotient step inside the integer cast"),
        ("""theorem M_cast_eq_unit_mul_padicPower
    (M p k : ℕ) (hM : 1 ≤ M) (hp : Nat.Prime p) :
    (M : ZMod (Pk p k)) =
      (unitFactorUnit M p k hM hp : ZMod (Pk p k)) *
        (p ^ valuationExponent M p : ZMod (Pk p k)) := by
  rw [unitFactor_decomposition M p hp, Nat.cast_mul,
    coe_unitFactorUnit, mul_comm]
""",
         """theorem M_cast_eq_unit_mul_padicPower
    (M p k : ℕ) (hM : 1 ≤ M) (hp : Nat.Prime p) :
    (M : ZMod (Pk p k)) =
      (unitFactorUnit M p k hM hp : ZMod (Pk p k)) *
        (p ^ valuationExponent M p : ZMod (Pk p k)) := by
  have h := congrArg (fun n : ℕ => (n : ZMod (Pk p k)))
    (unitFactor_decomposition M p hp).symm
  simpa only [Nat.cast_mul, coe_unitFactorUnit, mul_comm] using h
""",
         "Mock2 transport the unit-factor decomposition without dependent rewriting"),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
