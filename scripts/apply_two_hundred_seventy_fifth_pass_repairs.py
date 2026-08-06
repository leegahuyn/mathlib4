from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(m2, 'as_hom ', '↾', 'Mock2 as_hom', expected=10)
    m2 = replace_exact(m2, ' := by\n  funext e\n  exact e.2\n\n/-- The explicit subtype equalizer', ' := by\n  apply ConcreteCategory.hom_ext\n  intro e\n  simpa [equation613LeftType, equation613RightType] using e.2\n\n/-- The explicit subtype equalizer', 'Mock2 incl-proof', expected=1)
    m2 = replace_exact(m2, '    (x : S.pt) : equation613Left C (S.ι x) = equation613Right C (S.ι x) := by\n  have h := congrArg (fun k : S.pt ⟶ OverlapFamily C => k x) S.condition\n  simpa only [Function.comp_apply] using h\n', '    (x : S.pt) : equation613Left C (S.ι x) = equation613Right C (S.ι x) := by\n  have h := ConcreteCategory.congr_hom S.condition x\n  simpa [equation613LeftType, equation613RightType] using h\n', 'Mock2 competing', expected=1)
    m2 = replace_exact(m2, '    categoricalLift C S ≫ (categoricalEqualizerFork C).ι = S.ι := by\n  funext x\n  rfl\n', '    categoricalLift C S ≫ (categoricalEqualizerFork C).ι = S.ι := by\n  apply ConcreteCategory.hom_ext\n  intro x\n  rfl\n', 'Mock2 lift-fac', expected=1)
    m2 = replace_exact(m2, '    m = categoricalLift C S := by\n  funext x\n  apply Subtype.ext\n  have h := congrArg (fun k : S.pt ⟶ LocalFamily C => k x) hm\n  simpa only [Function.comp_apply] using h\n', '    m = categoricalLift C S := by\n  apply ConcreteCategory.hom_ext\n  intro x\n  apply Subtype.ext\n  have h := ConcreteCategory.congr_hom hm x\n  simpa [categoricalEqualizerFork] using h\n', 'Mock2 lift-unique', expected=1)
    m2 = replace_exact(m2, '  IsLimit.conePointUniqueUpToIso (categoricalEqualizerForkIsLimit C)\n    (limit.isLimit (parallelPair\n      (equation613LeftType C)\n      (equation613RightType C)))\n', '  (IsLimit.conePointUniqueUpToIso (categoricalEqualizerForkIsLimit C)\n    (limit.isLimit (parallelPair\n      (equation613LeftType C)\n      (equation613RightType C)))).toEquiv\n', 'Mock2 iso', expected=1)
    m2 = replace_exact(m2, '        (equation613RightType C) := by\n  funext A\n  exact (AqPresheaf.overlapRestrictions_eq_iff_compatible C.openCover _).mpr\n    (AqPresheaf.restrictToCover_compatible C.openCover A)\n', '        (equation613RightType C) := by\n  apply ConcreteCategory.hom_ext\n  intro A\n  exact (AqPresheaf.overlapRestrictions_eq_iff_compatible C.openCover _).mpr\n    (AqPresheaf.restrictToCover_compatible C.openCover A)\n', 'Mock2 global-cond', expected=1)
    m2 = replace_exact(m2, '    globalCategoricalLift C S ≫ (globalRestrictionFork C).ι = S.ι := by\n  funext x\n  exact globalEquiv_symm_restrict C (categoricalLift C S x)\n', '    globalCategoricalLift C S ≫ (globalRestrictionFork C).ι = S.ι := by\n  apply ConcreteCategory.hom_ext\n  intro x\n  exact globalEquiv_symm_restrict C (categoricalLift C S x)\n', 'Mock2 global-fac', expected=1)
    m2 = replace_exact(m2, "    m = globalCategoricalLift C S := by\n  funext x\n  apply (proposition16_supplies_hAq).locality C.openCover\n  intro i\n  have hm' := congrArg (fun k : S.pt ⟶ LocalFamily C => k x) hm\n  have hmi :\n      AqPresheaf.res (C.openCover.piece_le_target i) (m x) = S.ι x i := by\n    simpa only [Function.comp_apply] using\n      congrArg (fun t : LocalFamily C => t i) hm'\n  have hli := congrFun\n    (globalEquiv_symm_restrict C (categoricalLift C S x)) i\n  exact hmi.trans hli.symm\n", "    m = globalCategoricalLift C S := by\n  apply ConcreteCategory.hom_ext\n  intro x\n  apply (proposition16_supplies_hAq).locality C.openCover\n  intro i\n  have hm' := ConcreteCategory.congr_hom hm x\n  have hmi :\n      AqPresheaf.res (C.openCover.piece_le_target i) (m x) = S.ι x i := by\n    exact congrArg (fun t : LocalFamily C => t i) hm'\n  have hli := congrFun\n    (globalEquiv_symm_restrict C (categoricalLift C S x)) i\n  exact hmi.trans hli.symm\n", 'Mock2 global-unique', expected=1)
    m2 = replace_exact(m2, 'structure ActualProposition20Certificate : Prop where\n', 'structure ActualProposition20Certificate : Type where\n', 'Mock2 cert-sort', expected=1)
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
