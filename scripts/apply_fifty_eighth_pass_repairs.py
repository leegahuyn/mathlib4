from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(
    text: str, old: str, new: str, expected: int, label: str
) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        print(f"{label}: source changed; skipped")
        return text, False
    raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """namespace AdvancedClaimsIIRequirementLeafLedger

theorem object_claim_registry_at
"""
    new = """namespace AdvancedClaimsIIRequirementLeafLedger

/-- Generated accessor declarations sometimes name an already proved theorem
where Lean expects its underlying proposition.  This local coercion sends a
proof of `P` only to the original proposition `P`; all fields still require a
kernel-checked proof of exactly that proposition. -/
local instance proofTermCoeSort (P : Prop) : CoeSort P Prop where
  coe _ := P

theorem object_claim_registry_at
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock1Advanced restore proposition types in leaf-ledger accessors",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ac_rfl
""",
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring_nf
""",
        1,
        "Mock2 normalize the remaining commutative power-factor cast",
    )
    changed |= did

    old = """theorem resolutionAtOne_exact (M : ℕ) (hM : M ≠ 0) :
    (resolutionAtOne M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa using hz
  subst z
  exact ⟨0, by simp [resolutionAtOne]⟩
"""
    new = """theorem resolutionAtOne_exact (M : ℕ) (hM : M ≠ 0) :
    (resolutionAtOne M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  change integerMul M z = 0 at hz
  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa using hz
  subst z
  refine ⟨0, ?_⟩
  rfl
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2 expose the literal multiplication differential in exactness",
    )
    changed |= did

    old = """theorem freeResolutionD_comp (M : ℕ) (n : ℕ) :
    freeResolutionD M (n + 1) ≫ freeResolutionD M n = 0 := by
  cases n <;> simp [freeResolutionD]
"""
    new = """theorem freeResolutionD_comp (M : ℕ) (n : ℕ) :
    freeResolutionD M (n + 1) ≫ freeResolutionD M n = 0 := by
  cases n with
  | zero => exact zero_comp _ _
  | succ n => exact zero_comp _ _
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2 prove the resolution square by the categorical zero law",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """@[simp] theorem freeResolutionComplex_d_one_zero (M : ℕ) :
    (freeResolutionComplex M).d 1 0 = integerMul M := by
  simp [freeResolutionComplex, freeResolutionD]
""",
        """@[simp] theorem freeResolutionComplex_d_one_zero (M : ℕ) :
    (freeResolutionComplex M).d 1 0 = integerMul M := by
  change freeResolutionD M 0 = integerMul M
  rfl
""",
        1,
        "Mock2 compute the degree-one differential definitionally",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """@[simp] theorem freeResolutionComplex_d_two_one (M : ℕ) :
    (freeResolutionComplex M).d 2 1 = 0 := by
  simp [freeResolutionComplex, freeResolutionD]
""",
        """@[simp] theorem freeResolutionComplex_d_two_one (M : ℕ) :
    (freeResolutionComplex M).d 2 1 = 0 := by
  change freeResolutionD M 1 = 0
  rfl
""",
        1,
        "Mock2 compute the degree-two differential definitionally",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  simp [freeResolutionComplex, freeResolutionD]
""",
        """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  change freeResolutionD M (n + 2) = 0
  rfl
""",
        1,
        "Mock2 compute all higher differentials definitionally",
    )
    changed |= did

    normalized = text.rstrip() + "\n"
    if normalized != text:
        text = normalized
        changed = True
        print("Mock2 normalize final newline")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  rw [denseRange_inclusion_iff]
  exact M.core.le_topologicalClosure
""",
        """  rw [denseRange_inclusion_iff]
  · exact M.core.le_topologicalClosure
  · intro x hx
    exact hx
""",
        2,
        "Mock2Advanced discharge both closure inclusions",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    simpa only [Function.comp_def, chart.coord.apply_symm_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        """    conv_rhs => rw [← Lp.compMeasurePreserving_id_apply F]
    exact hcomp.symm
""",
        1,
        "Mock2Advanced rewrite only the endpoint of the forward-backward Lp identity",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    simpa only [Function.comp_def, chart.coord.symm_apply_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
""",
        """    conv_rhs => rw [← Lp.compMeasurePreserving_id_apply u]
    exact hcomp.symm
""",
        1,
        "Mock2Advanced rewrite only the endpoint of the backward-forward Lp identity",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem gammaTwoHyperbolic_smul_I_im :
    (gammaTwoHyperbolic • UpperHalfPlane.I).im = (1 : ℝ) / 25 := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have h11 :
      (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
          gammaTwoHyperbolic : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 3 := by
    rfl
  have h10 :
      (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
          gammaTwoHyperbolic : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 4 := by
    rfl
  rw [h11, h10]
  norm_num
"""
    new = """theorem gammaTwoHyperbolic_smul_I_im :
    (gammaTwoHyperbolic • UpperHalfPlane.I).im = (1 : ℝ) / 25 := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  change (1 : ℝ) / Complex.normSq ((4 : ℂ) * Complex.I + 3) =
    (1 : ℝ) / 25
  norm_num [Complex.normSq]
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "FunctionalAnalysis reduce the concrete Gamma(2) denominator definitionally",
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
