from __future__ import annotations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification/Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification/Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"


def rep(s: str, old: str, new: str, label: str, n: int = 1) -> str:
    count = s.count(old)
    if count != n:
        raise RuntimeError(f"{label}: expected {n}, found {count}")
    print(f"{label}: applied {n}")
    return s.replace(old, new, n)


def main() -> int:
    s = M2.read_text(encoding="utf-8")
    marker = "def resOut : QGaugePresheaf.Morphism (Aq D K A) (Bq A) :=\n  mapMorphism (outsideBoundaryDatum D K A)\n"
    lift = marker + """

/-- Universe-lifted boundary sheaf used only by the Mathlib categorical bridge. -/
def liftedBq : QGaugePresheaf.{0, v} Opens :=
  locallyConstantQGaugePresheaf (ULift.{v} (BoundaryDatum A))

theorem liftedBq_isSheaf :
    IsSheafLike (QGaugePresheaf.toPresheafLike (liftedBq (v := v) A)) :=
  locallyConstantQGaugePresheaf_isSheaf (ULift.{v} (BoundaryDatum A))

def liftedResIn :
    QGaugePresheaf.Morphism (Aq D K A) (liftedBq (v := v) A) :=
  mapMorphism (fun x =>
    (ULift.up (insideBoundaryDatum D K A x) : ULift.{v} (BoundaryDatum A)))

def liftedResOut :
    QGaugePresheaf.Morphism (Aq D K A) (liftedBq (v := v) A) :=
  mapMorphism (fun x =>
    (ULift.up (outsideBoundaryDatum D K A x) : ULift.{v} (BoundaryDatum A)))
"""
    s = rep(s, marker, lift, "add lifted boundary bridge")
    for old, new, label in (
        ("def mathlibBq : ActualSheafCategory.{v} :=\n  toMathlibSheaf (Bq A) (Bq_isSheaf A)\n",
         "def mathlibBq : ActualSheafCategory.{v} :=\n  toMathlibSheaf (liftedBq (v := v) A) (liftedBq_isSheaf (v := v) A)\n",
         "lift mathlibBq"),
        ("def mathlibResIn : mathlibAq D K A ⟶ mathlibBq A :=\n  toMathlibSheafMorphism (resIn D K A)\n    (Aq_isSheaf D K A) (Bq_isSheaf A)\n",
         "def mathlibResIn : mathlibAq D K A ⟶ mathlibBq A :=\n  toMathlibSheafMorphism (liftedResIn D K A)\n    (Aq_isSheaf D K A) (liftedBq_isSheaf (v := v) A)\n",
         "lift mathlibResIn"),
        ("def mathlibResOut : mathlibAq D K A ⟶ mathlibBq A :=\n  toMathlibSheafMorphism (resOut D K A)\n    (Aq_isSheaf D K A) (Bq_isSheaf A)\n",
         "def mathlibResOut : mathlibAq D K A ⟶ mathlibBq A :=\n  toMathlibSheafMorphism (liftedResOut D K A)\n    (Aq_isSheaf D K A) (liftedBq_isSheaf (v := v) A)\n",
         "lift mathlibResOut")):
        s = rep(s, old, new, label)
    s = rep(s,
        "theorem mathlibEqualizerInclusion_condition :\n    mathlibEqualizerInclusion D K A ≫ mathlibResIn D K A =\n      mathlibEqualizerInclusion D K A ≫ mathlibResOut D K A := by\n  apply CategoryTheory.Sheaf.hom_ext\n  apply NatTrans.ext\n  funext U\n  funext s\n  exact s.2\n",
        "theorem mathlibEqualizerInclusion_condition :\n    mathlibEqualizerInclusion D K A ≫ mathlibResIn D K A =\n      mathlibEqualizerInclusion D K A ≫ mathlibResOut D K A := by\n  apply CategoryTheory.Sheaf.hom_ext\n  apply NatTrans.ext\n  funext U\n  funext s\n  change (liftedResIn D K A).app U.unop s.1 =\n    (liftedResOut D K A).app U.unop s.1\n  apply LocallyConstant.ext\n  intro x\n  exact congrArg ULift.up\n    (congrArg (fun t : (Bq A).Field U.unop => t.toFun x) s.2)\n",
        "transport equalizer through ULift")
    M2.write_text(s, encoding="utf-8")

    s = M2A.read_text(encoding="utf-8")
    s = rep(s, "{R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]",
        "{R : Type*} [CommField R] [LinearOrder R] [IsStrictOrderedRing R]",
        "restore commutative ordered fields", 2)
    s = rep(s, "    rw [mode, integral_exp_mul_complex hc]",
        "    unfold mode\n    rw [integral_exp_mul_complex hc]", "unfold mode")
    for x, n in (("k", 7), ("n", 11), ("m", 11)):
        s = rep(s, f"∑ {x} in s,", f"∑ {x} ∈ s,", f"update {x}-sum syntax", n)
    s = rep(s, "Complex.conj (", "star (", "update complex conjugation", 19)
    M2A.write_text(s, encoding="utf-8")

    s = FA.read_text(encoding="utf-8")
    s = rep(s, "  simp only [fderiv_const, ContinuousLinearMap.zero_apply]\n",
        "  rw [(hasFDerivAt_const\n    ((inverseEtaMultiplier\n      GammaTwoQuotientGeometry.GammaTwo).nu γ)\n    (z : ℂ)).fderiv]\n  rfl\n", "constant fderiv")
    s = rep(s,
        "    have hEtaTarget : DifferentiableAt ℂ\n        (fun u : ℂ ↦ ModularForm.eta\n          ((g • UpperHalfPlane.ofComplex u : ℍ) : ℂ)) w :=\n      by\n        simpa only [Function.comp_apply] using\n          (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n            (g • (⟨w, hw⟩ : ℍ)).im_pos).comp w hAction\n",
        "    have hTargetMem :\n        (((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ) ∈\n          UpperHalfPlane.upperHalfPlaneSet) :=\n      (g • UpperHalfPlane.ofComplex w : ℍ).im_pos\n    have hEtaTarget : DifferentiableAt ℂ\n        (fun u : ℂ ↦ ModularForm.eta\n          ((g • UpperHalfPlane.ofComplex u : ℍ) : ℂ)) w := by\n      simpa only [Function.comp_apply] using\n        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n          hTargetMem).comp w hAction\n",
        "align eta target")
    s = rep(s,
        "    exact ((hEtaSource.div hEtaTarget\n      (ModularForm.eta_ne_zero\n        (g • (⟨w, hw⟩ : ℍ)).im_pos)).mul\n",
        "    exact ((hEtaSource.div hEtaTarget\n      (ModularForm.eta_ne_zero hTargetMem)).mul\n", "align eta nonzero")
    s = rep(s,
        "  exact hSmooth.congr (fun w hw ↦ by\n    rw [upperLift, Function.comp_apply,\n      UpperHalfPlane.ofComplex_apply_of_im_pos hw]\n    simpa [explicitFactor, g] using\n      inverseEtaPaperOrbitFactor_eq_eta n γ (⟨w, hw⟩ : ℍ))\n",
        "  exact hSmooth.congr (fun w hw ↦ by\n    rw [upperLift, Function.comp_apply,\n      UpperHalfPlane.ofComplex_apply_of_im_pos hw]\n    rw [inverseEtaPaperOrbitFactor_eq_eta]\n    simp only [explicitFactor, inverseEtaPaperOrbitDenom, g])\n",
        "preserve factor theorem")
    s = rep(s,
        "  have hAffine : HasDerivAt\n      (fun w : ℂ ↦ UpperHalfPlane.denom g w)\n      (g 1 0 : ℂ) (z : ℂ) := by\n    simpa [UpperHalfPlane.denom] using\n      (((hasDerivAt_id (z : ℂ)).const_mul (g 1 0)).add_const (g 1 1))\n  have hPower : HasDerivAt\n      (fun w : ℂ ↦ UpperHalfPlane.denom g w ^ m)\n      ((m : ℂ) * UpperHalfPlane.denom g z ^ (m - 1) *\n        (g 1 0 : ℂ)) (z : ℂ) := by\n    simpa [mul_comm, mul_left_comm, mul_assoc] using\n      (hasDerivAt_zpow m (UpperHalfPlane.denom g z)\n        (Or.inl (UpperHalfPlane.denom_ne_zero g z))).scomp (z : ℂ) hAffine\n",
        "  have hPower : HasDerivAt\n      (fun w : ℂ ↦ UpperHalfPlane.denom g w ^ m)\n      ((m : ℂ) * UpperHalfPlane.denom g z ^ (m - 1) *\n        (g 1 0 : ℂ)) (z : ℂ) := by\n    simpa [mul_comm, mul_left_comm, mul_assoc] using\n      UpperHalfPlane.hasDerivAt_denom_zpow g m z\n",
        "reuse denom derivative")
    s = rep(s,
        "  simpa [inverseEtaPaperOrbitLowerLeft, g, smul_eq_mul,\n    mul_assoc] using hApply\n",
        "  simpa [inverseEtaPaperOrbitDenom, inverseEtaPaperOrbitLowerLeft,\n    g, smul_eq_mul, mul_assoc] using hApply\n", "unfold denom in d1")
    FA.write_text(s, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
