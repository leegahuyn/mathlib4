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
    simpa only [TopCat.Sheaf.comp_app, CategoryTheory.comp_apply,
      toMathlibSheafMorphism_app] using h
  apply LocallyConstant.ext
  intro x
  have hx := congrArg (fun t => t.toFun x) hLift
  change ULift.up
      (insideBoundaryDatum D K A ((S.ι.hom.app U s).toFun x)) =
    ULift.up
      (outsideBoundaryDatum D K A ((S.ι.hom.app U s).toFun x)) at hx
  change insideBoundaryDatum D K A ((S.ι.hom.app U s).toFun x) =
    outsideBoundaryDatum D K A ((S.ι.hom.app U s).toFun x)
  exact congrArg (fun u : ULift.{v} (BoundaryDatum A) => u.down) hx
""",
        "Mock2 normalize the lifted fork condition with application lemmas",
    )
    m2 = replace_exact(
        m2,
        """        apply Subtype.ext
        simpa only [CategoryTheory.comp_apply] using
          CategoryTheory.ConcreteCategory.congr_hom
            (S.ι.hom.naturality f) s }
""",
        """        apply Subtype.ext
        change S.ι.hom.app W (S.pt.obj.map f s) =
          (mathlibAq D K A).obj.map f (S.ι.hom.app U s)
        exact CategoryTheory.ConcreteCategory.congr_hom
          (S.ι.hom.naturality f) s }
""",
        "Mock2 state subtype-lift naturality at the ambient sheaf level",
    )
    m2 = replace_exact(
        m2,
        """  have h := congrArg
    (fun k : S.pt ⟶ mathlibAq D K A => k.hom.app U s) hm
  simpa only [TopCat.Sheaf.comp_app, CategoryTheory.comp_apply] using h
""",
        """  have h := congrArg
    (fun k : S.pt ⟶ mathlibAq D K A => k.hom.app U s) hm
  have hval :
      (m.hom.app U s).1 = S.ι.hom.app U s := by
    simpa only [TopCat.Sheaf.comp_app, CategoryTheory.comp_apply,
      toMathlibSheafMorphism_app, equalizerInclusion_apply] using h
  simpa only [mathlibSubtypeLift_app_val] using hval
""",
        "Mock2 normalize the unique factorization through the inclusion",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  simp only [finitePolynomial, map_sum, map_mul]
  rw [Finset.sum_mul]
""",
        """  unfold finitePolynomial
  change
    (starRingEnd ℂ) (∑ k ∈ s, a k * mode k x) *
        (∑ k ∈ s, a k * mode k x) = _
  rw [map_sum]
  simp only [map_mul]
  rw [Finset.sum_mul]
""",
        "Mock2 Advanced expand the conjugated finite sum through starRingEnd",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  simpa [inverseEtaPaperOrbitFactor, inverseEtaPaperOrbitDenom] using
    (HalfIntegralMultiplier.factor_sq
      (inverseEtaPaperOrbitMultiplier
        GammaTwoQuotientGeometry.GammaTwo n) γ z)
""",
        """  simpa [inverseEtaPaperOrbitFactor, inverseEtaPaperOrbitDenom,
    paperOrbitExponent, paperDisplayedExponentIndex] using
    (HalfIntegralMultiplier.factor_sq
      (inverseEtaPaperOrbitMultiplier
        GammaTwoQuotientGeometry.GammaTwo n) γ z)
""",
        "FunctionalAnalysis unfold the paper orbit exponent in factor_sq",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
