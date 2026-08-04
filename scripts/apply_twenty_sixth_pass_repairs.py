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
        ("""  comm₁₂ := by simp
  comm₂₃ := by
""",
         """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    simp [Prop21StandardSequence.zeroToIntersection]
  comm₂₃ := by
""",
         "Mock2 compute the left zero square on underlying elements"),
        ("""  comm₂₃ := by simp

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         """  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    simp [Prop21StandardSequence.gcdToZero]

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         "Mock2 compute the standard right zero square on underlying elements"),
        ("""  comm₂₃ := by simp

/-- Auditable statement of the proven naturality range. -/
""",
         """  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    simp [PhiCokernel.rightEndpoint, PhiCokernel.toZero]

/-- Auditable statement of the proven naturality range. -/
""",
         "Mock2 compute the actual right zero square on underlying elements"),
        ("""  have h := congrArg (fun n : ℕ => (n : ZMod (Pk p k)))
    (unitFactor_decomposition M p hp).symm
  simpa only [Nat.cast_mul, coe_unitFactorUnit, mul_comm] using h
""",
         """  have h := congrArg (fun n : ℕ => (n : ZMod (Pk p k)))
    (unitFactor_decomposition M p hp)
  simpa only [Nat.cast_mul, coe_unitFactorUnit, mul_comm] using h
""",
         "Mock2 orient the unit-factor decomposition toward the theorem target"),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
