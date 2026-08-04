from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(
    text: str, old: str, new: str, expected: int, label: str
) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    for name in (
        "objectSchema",
        "t1t5",
        "spt",
        "kernel",
        "exactCoefficient",
        "pAdic",
        "entropyRepro",
        "finalInstance",
    ):
        old = f"""  cases r <;>
    simp [{name}Requirements, sectionOf] at h ⊢
"""
        new = f"""  cases r <;>
    simp_all [{name}Requirements, sectionOf]
"""
        text, did = replace_exact(
            text,
            old,
            new,
            2,
            f"Mock1Advanced use membership contradictions in {name} section proof",
        )
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """    _ =
      (p ^ shiftExponent M p k' : ZMod (Pk p k')) *
        ((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ) :
          ZMod (Pk p k')) := by
        simp only [PkReduction, map_mul, map_natCast, map_intCast,
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
    new = """    _ =
      (p ^ shiftExponent M p k' : ZMod (Pk p k')) *
        ((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ) :
          ZMod (Pk p k')) := by
        calc
          PkReduction p k k' hkk
              ((p ^ shiftExponent M p k : ZMod (Pk p k)) *
                (z : ZMod (Pk p k))) =
            (((((p ^ shiftExponent M p k : ℕ) : ℤ) * z : ℤ)) :
              ZMod (Pk p k')) := by
                convert PkReduction_intCast p k k' hkk
                  (((p ^ shiftExponent M p k : ℕ) : ℤ) * z) using 1 <;>
                  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
          _ =
              (p ^ shiftExponent M p k' : ZMod (Pk p k')) *
                ((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ) :
                  ZMod (Pk p k')) := by
            simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
            rw [← mul_assoc, ← pow_add,
              Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2 transport right naturality through the integer representative lemma",
    )
    changed |= did

    old = """  apply ModuleCat.hom_ext
  ext z
  change (((M : ℤ) * z : ℤ) : ZMod M) = 0
"""
    new = """  apply ModuleCat.hom_ext
  intro z
  change (((M : ℤ) * z : ℤ) : ZMod M) = 0
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2 introduce the underlying integer after ModuleCat hom extensionality",
    )
    changed |= did

    old = """  change (z : ZMod M) = 0 at hz
"""
    new = """  change (((z : ℤ) : ZMod M) = 0) at hz
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2 expose the resolution middle object as the underlying integer",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  rw [denseRange_inclusion_iff]
  exact M.core.subset_closure
"""
    new = """  rw [denseRange_inclusion_iff]
  exact AddSubmonoid.subset_closure M.core.toAddSubmonoid
"""
    text, did = replace_exact(
        text, old, new, 2,
        "Mock2Advanced apply subset_closure with its explicit add-submonoid argument",
    )
    changed |= did

    old = """  have hstarInv :
      ((starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)))⁻¹ =
        ((J.factor γ τ : ℂ))⁻¹ :=
    congrArg Inv.inv (star_star (J.factor γ τ : ℂ))
  rw [hstarInv]
"""
    new = """  rw [map_inv₀, star_star]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced move conjugation through the inverse before star-star",
    )
    changed |= did

    old = """    simpa only [Function.comp_def,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    first = """    simpa only [Function.comp_def, chart.coord.apply_symm_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    second = """    simpa only [Function.comp_def, chart.coord.symm_apply_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    count = text.count(old)
    if count == 0 and first in text and second in text:
        print("Mock2Advanced simplify both chart inverse compositions: already applied")
    elif count == 2:
        text = text.replace(old, first, 1).replace(old, second, 1)
        changed = True
        print("Mock2Advanced simplify both chart inverse compositions: applied 2")
    else:
        raise RuntimeError(
            f"Mock2Advanced chart composition blocks: expected 2, found {count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  norm_num

/-- This element sends `Im(i) = 1` to `1/25`. -/
"""
    new = """  decide

/-- This element sends `Im(i) = 1` to `1/25`. -/
"""
    text, did = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis decide the closed Gamma(2) residue equalities",
    )
    changed |= did

    old = """  rw [ModularGroup.im_smul_eq_div_normSq]
  change (((3 : ℝ) * 3 + (4 : ℝ) * 4)⁻¹) = (1 : ℝ) / 25
  norm_num
"""
    new = """  rw [ModularGroup.im_smul_eq_div_normSq]
  norm_num [gammaTwoHyperbolic, UpperHalfPlane.denom,
    Matrix.SpecialLinearGroup.toGL, Complex.normSq]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis unfold the concrete modular denominator before normalization",
    )
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
