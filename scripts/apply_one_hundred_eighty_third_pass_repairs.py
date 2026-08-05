from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """theorem fork_condition_apply
    (S : Fork (mathlibResIn D K A) (mathlibResOut D K A))
    (U : Opensᵒᵖ) (s : S.pt.obj.obj U) :
    (mathlibResIn D K A).hom.app U (S.ι.hom.app U s) =
      (mathlibResOut D K A).hom.app U (S.ι.hom.app U s) := by
  have h := congrArg
    (fun k : S.pt ⟶ mathlibBq A => k.hom.app U s) S.condition
  simpa only [CategoryTheory.comp_apply] using h
""",
        """theorem fork_condition_apply
    (S : Fork (mathlibResIn D K A) (mathlibResOut D K A))
    (U : Opensᵒᵖ) (s : S.pt.obj.obj U) :
    (resIn D K A).app U.unop (S.ι.hom.app U s) =
      (resOut D K A).app U.unop (S.ι.hom.app U s) := by
  have hLift :
      (liftedResIn D K A).app U.unop (S.ι.hom.app U s) =
        (liftedResOut D K A).app U.unop (S.ι.hom.app U s) := by
    have h := congrArg
      (fun k : S.pt ⟶ mathlibBq A => k.hom.app U s) S.condition
    simpa only [TopCat.Sheaf.comp_app, CategoryTheory.comp_apply] using h
  apply LocallyConstant.ext
  intro x
  simpa using congrArg
    (fun u : ULift.{v} (BoundaryDatum A) => u.down)
    (congrArg (fun t => t.toFun x) hLift)
""",
        "Mock2 descend the lifted fork condition to the original boundary sheaf",
    )
    m2 = replace_exact(
        m2,
        "simpa only [CategoryTheory.comp_apply] using h",
        "simpa only [TopCat.Sheaf.comp_app, CategoryTheory.comp_apply] using h",
        "Mock2 unfold sheaf composition in uniqueness",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  have harg :
      star ((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) =
        -((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) := by
    change Complex.conj
      ((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) =
        -((n : ℂ) * Real.pi * Complex.I * (x : ℂ))
    simp only [map_mul, ← Complex.ofReal_intCast, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring
  rw [hstar, harg, ← Complex.exp_add]
  congr 1
  ring
""",
        """  have harg :
      star ((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) =
        -((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) := by
    change (starRingEnd ℂ)
      ((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) =
        -((n : ℂ) * Real.pi * Complex.I * (x : ℂ))
    rw [map_mul, map_mul]
    simp <;> ring
  rw [hstar, harg, ← Complex.exp_add]
  congr 1
  push_cast
  ring
""",
        "Mock2 Advanced normalize complex conjugation through starRingEnd",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  exact hSmooth.congr (fun w hw ↦ by
    rw [upperLift, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rw [inverseEtaPaperOrbitFactor_eq_eta]
    simp only [explicitFactor, inverseEtaPaperOrbitDenom, g,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw])
""",
        """  exact hSmooth.congr (fun w hw ↦ by
    have hAction :
        g • (⟨w, hw⟩ : ℍ) =
          ((γ : SL(2, ℤ)) • (⟨w, hw⟩ : ℍ)) := by
      simpa [g, GammaTwoQuotientGeometry.gammaTwoToSL2Real] using
        (GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul
          γ (⟨w, hw⟩ : ℍ))
    rw [upperLift, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rw [inverseEtaPaperOrbitFactor_eq_eta]
    simp only [explicitFactor, inverseEtaPaperOrbitDenom,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rw [hAction])
""",
        "FunctionalAnalysis identify the integral and real GammaTwo actions",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
