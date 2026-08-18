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

FULL = r'''theorem qym_gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
  have hUpper : (((gamma 0 1 : ℤ) : ZMod 2)) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have hLower : (((gamma 1 0 : ℤ) : ZMod 2)) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvSCase
  · exact hcentral
  · rcases hT.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.T] at hUpper
  · rcases hTinv.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.T, ← zpow_neg_one,
        ModularGroup.coe_T_zpow] at hUpper
  · rcases hS.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.S] at hUpper
  · rcases hTS.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.T, ModularGroup.S,
        Matrix.mul_fin_two] at hUpper
  · rcases hTinvSTinv.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.T, ModularGroup.S, ← zpow_neg_one,
        ModularGroup.coe_T_zpow, Matrix.mul_fin_two] at hLower
  · rcases hSTinv.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.T, ModularGroup.S, ← zpow_neg_one,
        ModularGroup.coe_T_zpow, Matrix.mul_fin_two] at hUpper
  · rcases hST.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.T, ModularGroup.S,
        Matrix.mul_fin_two] at hUpper
  · rcases hTST.1 with rfl | rfl <;> exfalso
    all_goals
      norm_num [ModularGroup.T, ModularGroup.S,
        Matrix.mul_fin_two] at hLower
  · rcases hTinvSCase.1 with hpos | hneg
    · subst gamma
      exact (qym_tinvS_not_mem_gammaTwo hGamma).elim
    · subst gamma
      exact (qym_neg_tinvS_not_mem_gammaTwo hGamma).elim
'''

BODIES = {
    "obstruction": OBSTRUCTION,
    "full": FULL,
}


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_fastlane_local.py VARIANT OUTPUT.lean")
    variant = sys.argv[1]
    output = Path(sys.argv[2])
    if variant not in BODIES:
        raise SystemExit(f"unknown variant: {variant}")
    output.write_text(PRELUDE.replace("__BODY__", BODIES[variant]) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
