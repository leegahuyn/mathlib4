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

    old = """def gcdToKernelHom (M N : ℕ) :
    ZMod (Nat.gcd M N) →+ Tor1CyclicModel M N where
  toFun x := ⟨quotientToAmbientHom M N x,
    quotientToAmbientHom_mem_kernel M N x⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
"""
    new = """def gcdToKernelHom (M N : ℕ) :
    ZMod (Nat.gcd M N) →+ Tor1CyclicModel M N where
  toFun x := ⟨quotientToAmbientHom M N x,
    quotientToAmbientHom_mem_kernel M N x⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    exact map_add (quotientToAmbientHom M N) x y
"""
    text, did = replace_once(text, old, new,
        "Mock2 target canonical quotient-map additivity")
    changed |= did

    old = """def powerShiftKernelHom
    (M p k : ℕ) (hM : 1 ≤ M) (hp : Nat.Prime p) :
    ZMod (p ^ thicknessExponent M p k) →+
      Tor1CyclicModel M (Pk p k) where
  toFun x := ⟨powerShiftHom M p k x,
    powerShiftHom_mem_kernel M p k hM hp x⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
"""
    new = """def powerShiftKernelHom
    (M p k : ℕ) (hM : 1 ≤ M) (hp : Nat.Prime p) :
    ZMod (p ^ thicknessExponent M p k) →+
      Tor1CyclicModel M (Pk p k) where
  toFun x := ⟨powerShiftHom M p k x,
    powerShiftHom_mem_kernel M p k hM hp x⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simpa using map_add (powerShiftHom M p k) x y
"""
    text, did = replace_once(text, old, new,
        "Mock2 distinguish the power-shift subtype additivity block")
    changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
