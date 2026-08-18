#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import sys

PRELUDE = r'''import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open Matrix Function Set Topology
open scoped MatrixGroups UpperHalfPlane

lemma qym_tinv00 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 0 = (1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 0)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two] at h
  exact h

lemma qym_tinvS_upper_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T⁻¹).val 0 k * ModularGroup.S.val k 1) = -1
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.S, qym_tinv00]

lemma qym_neg_tinvS_upper_entry :
    (-(ModularGroup.T⁻¹ * ModularGroup.S) : SL(2, ℤ)) 0 1 = (1 : ℤ) := by
  simp [qym_tinvS_upper_entry]

theorem qym_tinvS_not_mem_gammaTwo :
    ModularGroup.T⁻¹ * ModularGroup.S ∉
      CongruenceSubgroup.Gamma 2 := by
  intro hmem
  have hUpper := (CongruenceSubgroup.Gamma_mem.mp hmem).2.1
  rw [qym_tinvS_upper_entry] at hUpper
  norm_num at hUpper

theorem qym_neg_tinvS_not_mem_gammaTwo :
    -(ModularGroup.T⁻¹ * ModularGroup.S) ∉
      CongruenceSubgroup.Gamma 2 := by
  intro hmem
  have hUpper := (CongruenceSubgroup.Gamma_mem.mp hmem).2.1
  rw [qym_neg_tinvS_upper_entry] at hUpper
  norm_num at hUpper

__BODY__
'''

OBSTRUCTION = r'''example :
    ModularGroup.T⁻¹ * ModularGroup.S ∉
      CongruenceSubgroup.Gamma 2 :=
  qym_tinvS_not_mem_gammaTwo

example :
    -(ModularGroup.T⁻¹ * ModularGroup.S) ∉
      CongruenceSubgroup.Gamma 2 :=
  qym_neg_tinvS_not_mem_gammaTwo
'''

FULL_PATH = Path(".github/qym_fastlane_full.lean")

OLD_TINV01 = r'''lemma qym_tinv01 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 1)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two, qym_tinv00] at h
  exact h
'''

NEW_TINV01 = r'''lemma qym_tinv01 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 1)
    (inv_mul_cancel ModularGroup.T)
  change
    (∑ k : Fin 2,
      (ModularGroup.T⁻¹).val 0 k * ModularGroup.T.val k 1) = 0 at h
  simp only [Fin.sum_univ_two] at h
  norm_num [ModularGroup.T, qym_tinv00] at h
  exact h
'''

OLD_TST = r'''lemma qym_TST_lower_entry :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 =
      (1 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T * ModularGroup.S).val 1 k * ModularGroup.T.val k 0) = 1
  simp only [Fin.sum_univ_two]
  norm_num [qym_TS_lower_entry, qym_TS_11_entry, ModularGroup.T]
'''

NEW_TST = r'''lemma qym_TST_lower_entry :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 =
      (1 : ℤ) := by
  change
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 *
        ModularGroup.T 0 0 +
      (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 *
        ModularGroup.T 1 0 = 1
  rw [qym_TS_lower_entry, qym_TS_11_entry]
  norm_num [ModularGroup.T]
'''


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_fastlane_local.py VARIANT OUTPUT.lean")
    variant = sys.argv[1]
    output = Path(sys.argv[2])
    if variant == "obstruction":
        body = OBSTRUCTION
    elif variant == "full":
        body = FULL_PATH.read_text(encoding="utf-8")
        assert body.count(OLD_TINV01) == 1
        assert body.count(OLD_TST) == 1
        body = body.replace(OLD_TINV01, NEW_TINV01, 1)
        body = body.replace(OLD_TST, NEW_TST, 1)
    else:
        raise SystemExit(f"unknown variant: {variant}")
    output.write_text(PRELUDE.replace("__BODY__", body) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
