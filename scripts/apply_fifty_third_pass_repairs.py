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

    specs = [
        ("objectSchema", 4),
        ("t1t5", 8),
        ("spt", 5),
        ("kernel", 8),
        ("exactCoefficient", 7),
        ("pAdic", 10),
        ("entropyRepro", 9),
        ("finalInstance", 3),
    ]
    for name, alternatives in specs:
        old = f"""  cases r <;>
    simp_all [{name}Requirements, sectionOf]
"""
        branches = " | ".join(["rfl"] * alternatives)
        new = f"""  simp only [{name}Requirements, List.mem_cons, List.mem_singleton] at h
  rcases h with {branches} <;> rfl
"""
        text, did = replace_exact(
            text,
            old,
            new,
            2,
            f"Mock1Advanced enumerate {name} requirement membership",
        )
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """        calc
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
    new = """        have hsrc :
            (p ^ shiftExponent M p k : ZMod (Pk p k)) *
                (z : ZMod (Pk p k)) =
              (((((p ^ shiftExponent M p k : ℕ) : ℤ) * z : ℤ)) :
                ZMod (Pk p k)) := by
          simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
        have hexp :
            p ^ shiftExponent M p k =
              p ^ shiftExponent M p k' *
                p ^ (shiftExponent M p k - shiftExponent M p k') := by
          rw [← pow_add,
            Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
        rw [hsrc, PkReduction_intCast]
        calc
          (((((p ^ shiftExponent M p k : ℕ) : ℤ) * z : ℤ)) :
              ZMod (Pk p k')) =
            (((((p ^ shiftExponent M p k' *
                p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ)) :
              ZMod (Pk p k')) := by rw [hexp]
          _ =
              (p ^ shiftExponent M p k' : ZMod (Pk p k')) *
                ((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ) :
                  ZMod (Pk p k')) := by
            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2 prove right naturality through natural exponent factorization",
    )
    changed |= did

    old = """  apply ModuleCat.hom_ext
  intro z
  change (((M : ℤ) * z : ℤ) : ZMod M) = 0
"""
    new = """  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((M : ℤ) * z : ℤ) : ZMod M) = 0
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2 descend to the underlying linear map before extensionality",
    )
    changed |= did

    old = """  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  change (((z : ℤ) : ZMod M) = 0) at hz
  obtain ⟨q, hq⟩ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z M).mp hz
  refine ⟨q, ?_⟩
  change (M : ℤ) * q = z
  exact hq.symm
"""
    new = """  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : ℤ, ((z : ZMod M) = 0) →
    ∃ q : ℤ, (M : ℤ) * q = z
  intro z hz
  obtain ⟨q, hq⟩ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z M).mp hz
  exact ⟨q, hq.symm⟩
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2 normalize the exactness criterion before introducing integers",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  exact AddSubmonoid.subset_closure M.core.toAddSubmonoid
"""
    new = """  intro x hx
  exact AddSubmonoid.subset_closure hx
"""
    text, did = replace_exact(
        text,
        old,
        new,
        2,
        "Mock2Advanced apply subset_closure to a membership witness",
    )
    changed |= did

    old = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  rw [map_inv₀, star_star]
"""
    new = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  have hstar :
      (starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)) =
        (J.factor γ τ : ℂ) := by
    simpa only [starRingEnd_apply] using
      (star_star (J.factor γ τ : ℂ))
  rw [hstar]
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2Advanced identify double conjugation before inversion",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  rw [ModularGroup.im_smul_eq_div_normSq]
  norm_num [gammaTwoHyperbolic, UpperHalfPlane.denom,
    Matrix.SpecialLinearGroup.toGL, Complex.normSq]
"""
    new = """  rw [ModularGroup.im_smul_eq_div_normSq]
  change (((3 : ℝ) * 3 + (4 : ℝ) * 4)⁻¹) = (1 : ℝ) / 25
  norm_num
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "FunctionalAnalysis restore the explicit concrete denominator normal form",
    )
    changed |= did

    old = """          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
          ((δ : SL(2, ℤ)) • z) *
"""
    new = """          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
          (((δ : SL(2, ℤ)) • z : ℍ)) *
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "FunctionalAnalysis keep the subgroup action in the upper half-plane",
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
