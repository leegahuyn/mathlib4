from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(path: Path, old: str, new: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    path.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def repair_spt2() -> bool:
    path = ROOT / "Spt2.lean"
    changed = False

    # Keep the checked-in kernel-witness transport proof.  Replacing it by y.2
    # is ill-typed because the two kernels are equivalent, not definitionally equal.

    changed = replace_once(
        path,
        """      rw [SetLike.mem_coe, LinearMap.mem_ker, KaehlerDifferential.mapBaseChange_tmul,
        one_smul, KaehlerDifferential.map_D, Ideal.Quotient.algebraMap_eq, hf0, map_zero]
""",
        """      simp only [SetLike.mem_coe, LinearMap.mem_ker,
        KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.map_D, Ideal.Quotient.algebraMap_eq, hf0, map_zero]
      simp
""",
        "Spt2 close final one-smul-zero kernel goal",
    ) or changed

    changed = replace_once(
        path,
        """    simp only [LinearEquiv.coe_coe]
    rw [htau]
    rfl
""",
        """    simp only [LinearEquiv.coe_coe]
    rw [htau]
""",
        "Spt2 remove proof command after rw closes hmap",
    ) or changed

    return changed


def repair_spt3() -> bool:
    path = ROOT / "Spt3.lean"
    changed = False

    # Keep amalgam_section_unique and RepointedConst.map in their checked-in
    # forms.  Earlier automated rewrites introduced the concrete-map/PLift cascade.

    changed = replace_once(
        path,
        """theorem resC_d10 (N : ℕ) : (resC N).d 1 0 = mulN N :=
  ChainComplex.of_d Xf (df N) (resC_sq N) 0
""",
        """theorem resC_d10 (N : ℕ) : (resC N).d 1 0 = mulN N := by
  dsimp [resC, df]
  rfl
""",
        "Spt3 compute resC differential 1-to-0 definitionally",
    ) or changed

    changed = replace_once(
        path,
        """theorem resC_d21 (N : ℕ) : (resC N).d 2 1 = 0 :=
  ChainComplex.of_d Xf (df N) (resC_sq N) 1
""",
        """theorem resC_d21 (N : ℕ) : (resC N).d 2 1 = 0 := by
  dsimp [resC, df]
  rfl
""",
        "Spt3 compute resC differential 2-to-1 definitionally",
    ) or changed

    changed = replace_once(
        path,
        """      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by
        gcongr
        exact hp1
""",
        """      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by
        gcongr
""",
        "Spt3 remove tactic after gcongr closes the goal",
    ) or changed

    return changed


def main() -> int:
    changed = repair_spt2()
    changed = repair_spt3() or changed
    print("Spt2/Spt3 repairs changed sources." if changed else "No Spt2/Spt3 changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
