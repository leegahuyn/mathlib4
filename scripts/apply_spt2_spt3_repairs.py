from __future__ import annotations

import re
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


def replace_regex_once(path: Path, pattern: str, replacement: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    repaired, count = re.subn(pattern, replacement, text, count=1, flags=re.MULTILINE)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return False
    path.write_text(repaired, encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def repair_spt1() -> bool:
    path = ROOT / "Spt1.lean"
    return replace_regex_once(
        path,
        r"(have h2 : \(p : ℝ\) \^ padicValNat p n ≤ \(p : ℝ\) \^ \(n - 1\) := by\n\s+gcongr)\n\s+exact hp1",
        r"\1",
        "Spt1 remove command after gcongr closes h2",
    )


def repair_spt2() -> bool:
    path = ROOT / "Spt2.lean"
    changed = False

    changed |= replace_once(
        path,
        """  invFun y :=
    ⟨(PrincipalUnivariateAQ.quotientConormalEquivForward f hf).symm y.1, by
      rw [LinearMap.mem_ker]
      rw [← principalAQH1Model_cotangentComplex_kernel_iff f hf]
      simp⟩
""",
        """  invFun y :=
    ⟨(PrincipalUnivariateAQ.quotientConormalEquivForward f hf).symm y.1, y.2⟩
""",
        "Spt2 use the stored H1Cotangent kernel witness",
    )

    changed |= replace_once(
        path,
        """      rw [SetLike.mem_coe, LinearMap.mem_ker, KaehlerDifferential.mapBaseChange_tmul,
        one_smul, KaehlerDifferential.map_D, Ideal.Quotient.algebraMap_eq, hf0, map_zero]
""",
        """      rw [SetLike.mem_coe, LinearMap.mem_ker, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.map_D, Ideal.Quotient.algebraMap_eq, hf0, map_zero]
""",
        "Spt2 remove obsolete one_smul rewrite",
    )

    changed |= replace_once(
        path,
        """    simp only [LinearEquiv.coe_coe]
    rw [htau]
    rfl
""",
        """    simp only [LinearEquiv.coe_coe]
    rw [htau]
""",
        "Spt2 remove proof command after rw closes hmap",
    )

    return changed


def repair_spt3() -> bool:
    path = ROOT / "Spt3.lean"
    changed = False

    changed |= replace_once(
        path,
        """    s = t := by
  simpa using h (𝟙 U)
""",
        """    s = t := by
  have hId := h (𝟙 U)
  rw [Functor.map_id] at hId
  exact hId
""",
        "Spt3 section uniqueness through functor map_id",
    )

    changed |= replace_once(
        path,
        """theorem resC_d10 (N : ℕ) : (resC N).d 1 0 = mulN N :=
  ChainComplex.of_d Xf (df N) (resC_sq N) 0

 theorem resC_d21""",
        """theorem resC_d10 (N : ℕ) : (resC N).d 1 0 = mulN N := by
  dsimp [resC, df]
  rfl

 theorem resC_d21""",
        "Spt3 adapt resC degree 1-to-0 computation",
    )

    changed |= replace_once(
        path,
        """theorem resC_d21 (N : ℕ) : (resC N).d 2 1 = 0 :=
  ChainComplex.of_d Xf (df N) (resC_sq N) 1
""",
        """theorem resC_d21 (N : ℕ) : (resC N).d 2 1 = 0 := by
  dsimp [resC, df]
  rfl
""",
        "Spt3 adapt resC degree 2-to-1 computation",
    )

    changed |= replace_once(
        path,
        """      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by
        gcongr
        exact hp1
""",
        """      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by
        gcongr
""",
        "Spt3 remove tactic after gcongr closes the goal",
    )

    changed |= replace_once(
        path,
        """def RepointedConst (A : Type) : (Opens S)ᵒᵖ ⥤ Type where
  obj U := PLift (U.unop : Set S).Nonempty → A
  map i := fun g => g ∘ liftNE (leOfHom i.unop)
""",
        """def RepointedConst (A : Type) : (Opens S)ᵒᵖ ⥤ Type where
  obj U := PLift (U.unop : Set S).Nonempty → A
  map i := fun g q => g (liftNE (leOfHom i.unop) q)
""",
        "Spt3 use explicit function composition in RepointedConst.map",
    )

    return changed


def main() -> int:
    changed = repair_spt1()
    changed = repair_spt2() or changed
    changed = repair_spt3() or changed
    print("Spt1/Spt2/Spt3 repairs changed sources." if changed else "No Spt1/Spt2/Spt3 changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
