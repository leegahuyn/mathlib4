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
        """  have hLift :
      (liftedResIn D K A).app U.unop (S.ι.hom.app U s) =
        (liftedResOut D K A).app U.unop (S.ι.hom.app U s) := by
    have h := congrArg
      (fun k : S.pt ⟶ mathlibBq A => k.hom.app U s) S.condition
    simpa only [TopCat.Sheaf.comp_app, CategoryTheory.comp_apply,
      toMathlibSheafMorphism_app] using h
  apply LocallyConstant.ext
  intro x
  have hx := congrArg (fun t => t.toFun x) hLift
""",
        """  have h := congrArg
    (fun k : S.pt ⟶ mathlibBq A => k.hom.app U s) S.condition
  change
    (liftedResIn D K A).app U.unop (S.ι.hom.app U s) =
      (liftedResOut D K A).app U.unop (S.ι.hom.app U s) at h
  apply LocallyConstant.ext
  intro x
  have hx := congrArg (fun t => t.toFun x) h
""",
        "Mock2 expose the lifted fork equality definitionally",
    )
    m2 = replace_exact(
        m2,
        """  have hval :
      (m.hom.app U s).1 = S.ι.hom.app U s := by
    simpa only [TopCat.Sheaf.comp_app, CategoryTheory.comp_apply,
      toMathlibSheafMorphism_app, equalizerInclusion_apply] using h
  simpa only [mathlibSubtypeLift_app_val] using hval
""",
        """  change (m.hom.app U s).1 = S.ι.hom.app U s at h
  simpa only [mathlibSubtypeLift_app_val] using h
""",
        "Mock2 expose the inclusion equality definitionally",
    )
    limit_marker = """def mathlibSubtypeForkIsLimit :
    IsLimit (mathlibSubtypeFork D K A) := by
  refine Fork.IsLimit.mk' _ fun S => ?_
  refine ⟨mathlibSubtypeLift D K A S,
    mathlibSubtypeLift_fac D K A S, ?_⟩
  intro m hm
  exact mathlibSubtypeLift_unique D K A S m hm
"""
    m2 = replace_exact(
        m2,
        limit_marker,
        limit_marker + """

/-- The explicit subtype fork installs the required categorical equalizer. -/
noncomputable instance mathlibHasEqualizer :
    HasEqualizer (mathlibResIn D K A) (mathlibResOut D K A) :=
  HasLimit.mk
    { cone := mathlibSubtypeFork D K A
      isLimit := mathlibSubtypeForkIsLimit D K A }
""",
        "Mock2 install the explicit equalizer instance",
    )
    m2 = replace_exact(
        m2,
        """  inside_component :
    ∀ (U : Opens) (s : (Aq D K A).Field U) (x : U),
      (resIn D K A).app U s x = insideBoundaryDatum D K A (s x)
  outside_component :
    ∀ (U : Opens) (s : (Aq D K A).Field U) (x : U),
      (resOut D K A).app U s x = outsideBoundaryDatum D K A (s x)
  outside_components_agree :
    ∀ (U : Opens) (s : (Aq D K A).Field U) (x : U)
      (q : BoundaryPoint A),
      ((resOut D K A).app U s x).inside q =
        ((resOut D K A).app U s x).outside q
""",
        """  inside_component :
    ∀ (U : Opens) (s : (Aq D K A).Field U) (x : U),
      ((resIn D K A).app U s).toFun x =
        insideBoundaryDatum D K A (s.toFun x)
  outside_component :
    ∀ (U : Opens) (s : (Aq D K A).Field U) (x : U),
      ((resOut D K A).app U s).toFun x =
        outsideBoundaryDatum D K A (s.toFun x)
  outside_components_agree :
    ∀ (U : Opens) (s : (Aq D K A).Field U) (x : U)
      (q : BoundaryPoint A),
      (((resOut D K A).app U s).toFun x).inside q =
        (((resOut D K A).app U s).toFun x).outside q
""",
        "Mock2 evaluate certificate fields through LocallyConstant.toFun",
    )
    m2 = replace_exact(
        m2,
        "noncomputable def certificate : Certificate D K A where",
        "noncomputable def certificate : Certificate (D := D) (K := K) (A := A) where",
        "Mock2 name every certificate parameter",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """    _ = (2 : ℂ) * (Complex.normSq (a n) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      ring
""",
        """    _ = (2 : ℂ) * (Complex.normSq (a n) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      change star (a n) * a n * 2 = a n * star (a n) * 2
      rw [mul_comm (star (a n)) (a n)]
""",
        "Mock2 Advanced commute the conjugate factor explicitly",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hα : α = α.re • (1 : ℂ) + α.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hα, map_add, map_smul, map_smul]
  simp only [Complex.real_smul, one_mul]
""",
        """  have hα : α = α.re • (1 : ℂ) + α.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    D α = D (α.re • (1 : ℂ) + α.im • Complex.I) := congrArg D hα
    _ = (α.re : ℂ) * D 1 + (α.im : ℂ) * D Complex.I := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.real_smul]
""",
        "FunctionalAnalysis avoid rewriting the target coefficients",
    )
    fa = replace_exact(
        fa,
        """  rw [realCLM_apply_complex_decomposition D α,
    realCLM_apply_complex_decomposition D (α * Complex.I)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
  ring_nf
  simp [Complex.I_sq]
  <;> ring
""",
        """  rw [realCLM_apply_complex_decomposition D α,
    realCLM_apply_complex_decomposition D (α * Complex.I)]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.I_sq] <;> ring
""",
        "FunctionalAnalysis prove the holomorphic Wirtinger identity componentwise",
    )
    fa = replace_exact(
        fa,
        """  have hConj : star α =
      (α.re : ℂ) - (α.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [realCLM_apply_complex_decomposition D α,
    realCLM_apply_complex_decomposition D (α * Complex.I), hConj]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero,
    zero_mul, add_zero]
  ring_nf
  simp [Complex.I_sq]
  <;> ring
""",
        """  rw [realCLM_apply_complex_decomposition D α,
    realCLM_apply_complex_decomposition D (α * Complex.I)]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.I_sq] <;> ring
""",
        "FunctionalAnalysis prove the antiholomorphic Wirtinger identity componentwise",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
