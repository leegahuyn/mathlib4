from __future__ import annotations

from pathlib import Path

import apply_ninety_eighth_pass_repairs as pass98
import apply_ninety_ninth_pass_repairs as pass99
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  Countable.of_injective
    (fun γ : SL(2, ℤ) =>
      ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
       (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
       (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
       (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1))
    (by
      intro a b h
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all)
""",
        """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  (show Function.Injective
      (fun γ : SL(2, ℤ) =>
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) from by
      intro a b h
      apply Subtype.ext
      exact h).countable
""",
        1,
        "FunctionalAnalysis derive SL2Z countability from matrix coercion",
    )
    changed |= did

    old_hcancel = """  have hcancel :
      ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z =
        gammaTwoCosetRep q • (g • z) := by
    calc
      ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z =
          ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) •
            (g⁻¹ • (g • z)) := by simp
      _ = ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) •
            (((γ : GammaTwo) : SL(2, ℤ)) *
              gammaTwoCosetRep q) • (g • z) := by
        rw [hdecomp']
      _ = gammaTwoCosetRep q • (g • z) := by
        simp only [mul_smul]
        rw [inv_smul_smul]
"""
    new_hcancel = """  have hcancel :
      ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z =
        gammaTwoCosetRep q • (g • z) := by
    have hg :
        g = (gammaTwoCosetRep q)⁻¹ *
          ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) := by
      have h := congrArg Inv.inv hdecomp'
      simpa [mul_inv_rev] using h
    have hγ :
        ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) =
          gammaTwoCosetRep q * g := by
      rw [hg]
      simp [mul_assoc]
    rw [hγ, mul_smul]
"""
    count = text.count(old_hcancel)
    if count == 3:
        text = text.replace(old_hcancel, new_hcancel)
        changed = True
        print("FunctionalAnalysis derive all three coset cancellations by group inversion: applied 3")
    elif count == 0 and text.count(new_hcancel) == 3:
        print("FunctionalAnalysis derive all three coset cancellations by group inversion: already applied")
    else:
        raise RuntimeError(
            f"FunctionalAnalysis expected three coset cancellation blocks, found {count}"
        )

    old_finish = """  simpa only [gammaTwoEffectiveElement_smul, hcancel] using htile
"""
    new_finish = """  change ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z ∈
    gammaTwoOpenCarrier
  rw [hcancel]
  exact htile
"""
    count = text.count(old_finish)
    if count == 3:
        text = text.replace(old_finish, new_finish)
        changed = True
        print("FunctionalAnalysis finish all three carrier-cover proofs explicitly: applied 3")
    elif count == 0 and text.count(new_finish) == 3:
        print("FunctionalAnalysis finish all three carrier-cover proofs explicitly: already applied")
    else:
        raise RuntimeError(
            f"FunctionalAnalysis expected three carrier-cover finishes, found {count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass98.main()
    pass99.repair_mock1_advanced()
    pass99.repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
