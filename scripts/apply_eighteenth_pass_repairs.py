from __future__ import annotations

from pathlib import Path


ROOT = Path("PrimalitySheafVerification")


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


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = "List.mem_filter.mpr ⟨h, by simp⟩"
    new = "List.mem_filter.mpr ⟨h, rfl⟩"
    count = text.count(old)
    if count:
        text = text.replace(old, new)
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock1Advanced concrete requested-definition layers: applied {count}")
    else:
        print("Mock1Advanced concrete requested-definition layers: already applied/source changed")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """def gcdRestriction
    {M N M' N' : ℕ} (hM : M' ∣ M) (hN : N' ∣ N) :
    ZMod (Nat.gcd M N) →+ ZMod (Nat.gcd M' N') :=
  (ZMod.castHom (gcd_dvd_gcd_of_dvd hM hN)
    (ZMod (Nat.gcd M' N'))).toAddMonoidHom
"""
    new = """def gcdRestriction
    {M N M' N' : ℕ} (hM : M' ∣ M) (hN : N' ∣ N) :
    ZMod (Nat.gcd M N) →+ ZMod (Nat.gcd M' N') :=
  (ZMod.castHom (gcd_dvd_gcd_of_dvd hM hN)
    (ZMod (Nat.gcd M' N'))).toAddMonoidHom

@[simp] theorem gcdRestriction_apply
    {M N M' N' : ℕ} (hM : M' ∣ M) (hN : N' ∣ N)
    (x : ZMod (Nat.gcd M N)) :
    gcdRestriction hM hN x =
      ZMod.castHom (gcd_dvd_gcd_of_dvd hM hN)
        (ZMod (Nat.gcd M' N')) x :=
  rfl
"""
    text, did = replace_once(text, old, new, "Mock2 expose gcd restriction application")
    changed |= did

    old = """  simp only [AddMonoidHom.comp_apply, gcdRestriction, psi_representatives_apply,
    residueRestriction_apply, map_intCast]
"""
    new = """  simp only [AddMonoidHom.comp_apply, gcdRestriction_apply,
    psi_representatives_apply, residueRestriction_apply, map_intCast]
"""
    text, did = replace_once(text, old, new, "Mock2 use cast-preserving gcd restriction lemma")
    changed |= did

    identities = [
        ("  τ₁ := 𝟙 _\n  τ₂ := AddCommGrpCat.ofHom (intersectionRestriction hM hN)\n  τ₃ := 𝟙 _\n",
         "  τ₁ := 𝟙 Prop21StandardSequence.zeroObject\n  τ₂ := AddCommGrpCat.ofHom (intersectionRestriction hM hN)\n  τ₃ := 𝟙 Prop21StandardSequence.integerObject\n",
         "Mock2 type left-endpoint identities"),
        ("  τ₁ := AddCommGrpCat.ofHom (intersectionRestriction hM hN)\n  τ₂ := 𝟙 _\n  τ₃ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n",
         "  τ₁ := AddCommGrpCat.ofHom (intersectionRestriction hM hN)\n  τ₂ := 𝟙 Prop21StandardSequence.integerObject\n  τ₃ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n",
         "Mock2 type integer-square identity"),
        ("  τ₁ := 𝟙 _\n  τ₂ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₃ := AddCommGrpCat.ofHom (gcdRestriction hM hN)\n",
         "  τ₁ := 𝟙 Prop21StandardSequence.integerObject\n  τ₂ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₃ := AddCommGrpCat.ofHom (gcdRestriction hM hN)\n",
         "Mock2 type residue-square identity"),
        ("  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₂ := AddCommGrpCat.ofHom (gcdRestriction hM hN)\n  τ₃ := 𝟙 _\n",
         "  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₂ := AddCommGrpCat.ofHom (gcdRestriction hM hN)\n  τ₃ := 𝟙 Prop21StandardSequence.zeroObject\n",
         "Mock2 type right-endpoint identity"),
        ("  τ₁ := 𝟙 _\n  τ₂ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₃ := AddCommGrpCat.ofHom (cokernelMap hM hN)\n",
         "  τ₁ := 𝟙 Prop21StandardSequence.integerObject\n  τ₂ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₃ := AddCommGrpCat.ofHom (cokernelMap hM hN)\n",
         "Mock2 type actual-cokernel identity"),
        ("  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₂ := AddCommGrpCat.ofHom (cokernelMap hM hN)\n  τ₃ := 𝟙 _\n",
         "  τ₁ := AddCommGrpCat.ofHom (residueRestriction hM hN)\n  τ₂ := AddCommGrpCat.ofHom (cokernelMap hM hN)\n  τ₃ := 𝟙 Prop21StandardSequence.zeroObject\n",
         "Mock2 type actual right-endpoint identity"),
    ]
    for old, new, label in identities:
        text, did = replace_once(text, old, new, label)
        changed |= did

    text2 = text.replace(
        "  comm₁₂ := by\n    simp only [Category.id_comp, Category.zero_comp]\n",
        "  comm₁₂ := by simp\n", 1)
    if text2 != text:
        text = text2
        changed = True
        print("Mock2 simplify left zero square: applied")

    old_zero = """  comm₂₃ := by
    simp only [Category.comp_zero, Category.zero_comp, Category.comp_id]
"""
    count = text.count(old_zero)
    if count:
        text = text.replace(old_zero, "  comm₂₃ := by simp\n")
        changed = True
        print(f"Mock2 simplify right zero squares: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ((↑(1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) : ENNReal) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, changed = replace_once(text, old, new, "Mock2Advanced cast density before exponentiation")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
