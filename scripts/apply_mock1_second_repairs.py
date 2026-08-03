from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1.lean")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    text, c = replace_once(
        text,
        """def TorProxy (M N : ℕ) [NeZero N] : Type :=
  (AddMonoidHom.mulLeft (M : ZMod N)).ker

instance torProxyCoe (M N : ℕ) [NeZero N] : Coe (TorProxy M N) (ZMod N) where
  coe x := x.1

@[ext] theorem torProxy_ext {M N : ℕ} [NeZero N] {x y : TorProxy M N}
    (h : (x : ZMod N) = (y : ZMod N)) : x = y := by
  apply Subtype.ext
  exact h

/-- The carrier subgroup underlying `TorProxy`. -/
""",
        """abbrev TorProxy (M N : ℕ) [NeZero N] : Type :=
  (AddMonoidHom.mulLeft (M : ZMod N)).ker

/-- The carrier subgroup underlying `TorProxy`. -/
""",
        "Mock1 expose TorProxy as its kernel subtype",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem zmodGcdToTorProxyHom_one (M N : ℕ) [NeZero N] :
    zmodGcdToTorProxyHom M N 1 = torProxyExplicitGenerator M N := by
  apply torProxy_ext
  simp [zmodGcdToTorProxyHom, torProxyGeneratorIntHom]
""",
        """theorem zmodGcdToTorProxyHom_one (M N : ℕ) [NeZero N] :
    zmodGcdToTorProxyHom M N 1 = torProxyExplicitGenerator M N := by
  apply Subtype.ext
  simp [zmodGcdToTorProxyHom, torProxyGeneratorIntHom]
""",
        "Mock1 compare TorProxy generators through subtype values",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem mem_ker_pairResidueMap_iff (M N : ℕ) (a : ℤ) :
    a ∈ (PairResidueMap M N).ker ↔ (Nat.lcm M N : ℤ) ∣ a := by
  rw [AddMonoidHom.mem_ker, PairResidueMap_apply]
  constructor
  · intro h
    have hM : (M : ℤ) ∣ a :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a M).mp (Prod.ext_iff.mp h).1
    have hN : (N : ℤ) ∣ a :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a N).mp (Prod.ext_iff.mp h).2
    exact coe_lcm_dvd_iff.mpr ⟨hM, hN⟩
  · intro h
    exact Prod.ext
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a M).mpr (coe_lcm_dvd_iff.mp h).1)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a N).mpr (coe_lcm_dvd_iff.mp h).2)
""",
        """theorem mem_ker_pairResidueMap_iff (M N : ℕ) (a : ℤ) :
    a ∈ (PairResidueMap M N).ker ↔ (Nat.lcm M N : ℤ) ∣ a := by
  rw [AddMonoidHom.mem_ker, PairResidueMap_apply]
  constructor
  · intro h
    have hM : (M : ℤ) ∣ a :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a M).mp (Prod.ext_iff.mp h).1
    have hN : (N : ℤ) ∣ a :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a N).mp (Prod.ext_iff.mp h).2
    change (lcm (M : ℤ) (N : ℤ) : ℤ) ∣ a
    exact (lcm_dvd_iff).2 ⟨hM, hN⟩
  · intro h
    change (lcm (M : ℤ) (N : ℤ) : ℤ) ∣ a at h
    exact Prod.ext
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a M).mpr (lcm_dvd_iff.mp h).1)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a N).mpr (lcm_dvd_iff.mp h).2)
""",
        "Mock1 use the integer GCDMonoid lcm API",
    )
    changed |= c

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1 second-pass repairs changed source.")
    else:
        print("No Mock1 second-pass changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
