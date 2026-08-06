from __future__ import annotations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    actual = text.count(old)
    if actual != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {actual}")
    print(f"{label}: applied {actual}")
    return text.replace(old, new)


def main() -> int:
    text = FA.read_text(encoding="utf-8")
    text = replace_exact(text, 'open DefinitionOneSobolev.WeightCorePetersson\nopen MeasureTheory\nopen scoped ModularForm\n', 'open DefinitionOneSobolev.WeightCorePetersson\nopen MeasureTheory\nopen scoped ModularForm ContDiff\n', 'FunctionalAnalysis open ContDiff scope for explicit potential', expected=1)
    text = replace_exact(text, "theorem upstairsPotential_SL_invariant (g : SL(2, ℤ)) (z : ℍ) :\n    upstairsPotential (g • z) = upstairsPotential z := by\n  have hg : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=\n    ⟨g, rfl⟩\n  simpa only [upstairsPotential] using\n    (SlashInvariantFormClass.norm_petersson_smul\n      (k := (12 : ℤ)) (f := ModularForm.discriminantCuspForm)\n      (f' := ModularForm.discriminantCuspForm) (τ := z) hg)\n", "theorem upstairsPotential_SL_invariant (g : SL(2, ℤ)) (z : ℍ) :\n    upstairsPotential (g • z) = upstairsPotential z := by\n  have hg : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=\n    ⟨g, rfl⟩\n  let gReal : SL(2, ℝ) :=\n    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g\n  have hAction : g • z = gReal • z := by\n    apply UpperHalfPlane.ext\n    simp [gReal, UpperHalfPlane.coe_specialLinearGroup_apply]\n  unfold upstairsPotential\n  rw [hAction]\n  exact SlashInvariantFormClass.norm_petersson_smul\n    (k := (12 : ℤ)) (f := ModularForm.discriminantCuspForm)\n    (f' := ModularForm.discriminantCuspForm) (τ := z) hg\n", 'FunctionalAnalysis bridge integral SL action', expected=1)
    text = replace_exact(text, "theorem potential_pos (q : GammaTwoQuotient) : 0 < potential q := by\n  induction q using Quotient.inductionOn'\n  simpa only [potential_mk] using upstairsPotential_pos _\n", "theorem potential_pos (q : GammaTwoQuotient) : 0 < potential q := by\n  induction q using Quotient.inductionOn'\n  change 0 < upstairsPotential _\n  exact upstairsPotential_pos _\n", 'FunctionalAnalysis reduce quotient positivity definitionally', expected=1)
    text = replace_exact(text, "theorem potential_le_uniformBound (q : GammaTwoQuotient) :\n    potential q ≤ uniformBound := by\n  induction q using Quotient.inductionOn'\n  simpa only [potential_mk] using upstairsPotential_le_uniformBound _\n", "theorem potential_le_uniformBound (q : GammaTwoQuotient) :\n    potential q ≤ uniformBound := by\n  induction q using Quotient.inductionOn'\n  change upstairsPotential _ ≤ uniformBound\n  exact upstairsPotential_le_uniformBound _\n", 'FunctionalAnalysis reduce quotient bound definitionally', expected=1)
    text = replace_exact(text, '  have hPet : UpperHalfPlane.IsZeroAtImInfty\n      (UpperHalfPlane.petersson 12 ModularForm.discriminantCuspForm\n        ModularForm.discriminantCuspForm) :=\n    (CuspFormClass.zero_at_infty ModularForm.discriminantCuspForm)\n      .petersson_isZeroAtImInfty_left 12 𝒮ℒ\n        ModularForm.discriminantCuspForm\n', '  have hPet : UpperHalfPlane.IsZeroAtImInfty\n      (UpperHalfPlane.petersson 12 ModularForm.discriminantCuspForm\n        ModularForm.discriminantCuspForm) :=\n    UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_left\n      12 𝒮ℒ\n      (CuspFormClass.zero_at_infty ModularForm.discriminantCuspForm)\n      ModularForm.discriminantCuspForm\n', 'FunctionalAnalysis use explicit Petersson decay theorem', expected=1)
    text = replace_exact(text, '  simpa only [upperLift, Function.comp_def, Complex.conjCLE_apply] using\n    Complex.conjCLE.contDiff.comp_contDiffOn\n      hDelta\n', '  simpa [upperLift, Function.comp_def] using\n    Complex.conjCLE.contDiff.comp_contDiffOn hDelta\n', 'FunctionalAnalysis normalize complex conjugation', expected=1)
    text = replace_exact(text, '  have hProduct :=\n    (discriminant_conj_realSmooth.mul discriminant_realSmooth).mul\n      (HalfWeightDifferentialOperators.realSmooth_heightC.pow 12)\n  simpa only [UpperHalfPlane.petersson,\n    HalfWeightDifferentialOperators.heightC, zpow_natCast,\n    Pi.mul_apply] using hProduct\n', '  have hProduct :=\n    (discriminant_conj_realSmooth.mul discriminant_realSmooth).mul\n      (HalfWeightDifferentialOperators.realSmooth_heightC.pow 12)\n  unfold RealSmooth\n  simpa [UpperHalfPlane.petersson, upperLift, Function.comp_def,\n    HalfWeightDifferentialOperators.heightC, zpow_natCast,\n    Pi.mul_apply] using hProduct\n', 'FunctionalAnalysis expose Petersson RealSmooth target', expected=1)
    text = replace_exact(text, 'expNegInvGlue.contDiff.continuous', '(expNegInvGlue.contDiff (n := 1)).continuous', 'FunctionalAnalysis instantiate glue continuity order', expected=4)
    FA.write_text(text, encoding="utf-8")
    print("[pass314] FunctionalAnalysis explicit-potential frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
