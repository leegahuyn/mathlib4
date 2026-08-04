from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact_count(text: str, old: str, new: str, count: int, label: str) -> tuple[str, bool]:
    found = text.count(old)
    if found == count:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if found == 0 and text.count(new) >= count:
        print(f"{label}: already applied")
        return text, False
    raise RuntimeError(f"{label}: expected {count} matches, found {found}")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False
    for group in ["objectSchema", "t1t5", "spt", "kernel", "exactCoefficient", "pAdic", "entropyRepro", "finalInstance"]:
        old = f"""  have hm :
      List.Mem (sectionOf r) ({group}Requirements.map sectionOf) :=
    List.mem_map_of_mem h
  simpa [{group}Requirements, sectionOf] using hm
"""
        new = f"""  cases r <;>
    simp [{group}Requirements, sectionOf] at h ⊢
"""
        text, did = replace_exact_count(
            text, old, new, 2,
            f"Mock1Advanced prove both {group} section classifiers by cases")
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """        simp only [PkReduction, AddMonoidHom.coe_comp,
          Function.comp_apply, map_mul, map_natCast, map_intCast,
          Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
        rw [← mul_assoc, ← pow_add,
          Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
"""
    new = """        simp only [PkReduction, map_mul, map_natCast, map_intCast,
          Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
        change
          (p : ZMod (Pk p k')) ^ shiftExponent M p k *
              (z : ZMod (Pk p k')) =
            (p : ZMod (Pk p k')) ^ shiftExponent M p k' *
              (p : ZMod (Pk p k')) ^
                (shiftExponent M p k - shiftExponent M p k') *
              (z : ZMod (Pk p k'))
        rw [← mul_assoc, ← pow_add,
          Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
"""
    text, did = replace_exact_count(text, old, new, 1,
        "Mock2 normalize the right naturality square in one residue ring")
    changed |= did

    old = """      rw [rightThicknessMap_intCast_as_intCast]
"""
    new = """      rw [rightThicknessMap_intCast_as_intCast]
      congr 1
      simp only [Int.cast_mul]
"""
    text, did = replace_exact_count(text, old, new, 1,
        "Mock2 identify the integer product after right-thickness transport")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  rw [denseRange_inclusion_iff]
  intro x hx
  exact hx
"""
    new = """  rw [denseRange_inclusion_iff]
  exact M.core.subset_closure
"""
    text, did = replace_exact_count(text, old, new, 2,
        "Mock2Advanced prove both core inclusions via subset_closure")
    changed |= did

    old = """  have hstar :
      (starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)) =
        (J.factor γ τ : ℂ) := star_star _
  rw [hstar]
"""
    new = """  have hstarInv :
      ((starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)))⁻¹ =
        ((J.factor γ τ : ℂ))⁻¹ :=
    congrArg Inv.inv (star_star (J.factor γ τ : ℂ))
  rw [hstarInv]
"""
    text, did = replace_exact_count(text, old, new, 1,
        "Mock2Advanced rewrite double conjugation underneath inversion")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [gammaTwoHyperbolic]
"""
    new = """  rw [CongruenceSubgroup.Gamma_mem]
  change
    ((3 : ZMod 2) = 1 ∧ (2 : ZMod 2) = 0 ∧
      (4 : ZMod 2) = 0 ∧ (3 : ZMod 2) = 1)
  norm_num
"""
    text, did = replace_exact_count(text, old, new, 1,
        "FunctionalAnalysis compute Gamma(2) membership in ZMod 2")
    changed |= did

    old = """  rw [ModularGroup.im_smul_eq_div_normSq]
  norm_num [ModularGroup.denom_apply, gammaTwoHyperbolic,
    Complex.normSq_apply]
"""
    new = """  rw [ModularGroup.im_smul_eq_div_normSq]
  change (((3 : ℝ) * 3 + (4 : ℝ) * 4)⁻¹) = (1 : ℝ) / 25
  norm_num
"""
    text, did = replace_exact_count(text, old, new, 1,
        "FunctionalAnalysis compute the hyperbolic imaginary part explicitly")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
