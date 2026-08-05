from pathlib import Path
import apply_seventy_first_pass_repairs as p

M = Path("PrimalitySheafVerification/Mock2.lean")
A = Path("PrimalitySheafVerification/Mock2_Advanced.lean")
F = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")


def edit(path, edits):
    s = path.read_text(encoding="utf-8")
    for old, new, label in edits:
        s, _ = p.replace_exact(s, old, new, 1, label)
    path.write_text(s, encoding="utf-8", newline="\n")


def main():
    edit(M, [
        ("noncomputable noncomputable def AqPresheaf\n",
         "noncomputable def AqPresheaf\n", "restore one noncomputable modifier"),
        ("    { predicate_restriction_stable := fun hUV hA =>\n        modularCovariance_restrict (Aq := Aq) (MC := MC) hMC hUV hA\n",
         "    { predicate_restriction_stable := fun hUV hA =>\n        hMC hUV hA\n", "use covariance stability proof directly"),
    ])
    edit(A, [
        ("""theorem tensorCyclicShortComplex_g_eq_zsmul_id (M N : ℕ) :
    (tensorCyclicShortComplex M N).g =
      (N : ℤ) • 𝟙 ((tensorCyclicShortComplex M N).X₂) := by
  change
    (cyclicTensorFunctor M).map ((cyclicFreeComplex N).d 1 0) = _
  rw [cyclicFreeComplex_d_one_zero,
    cyclicResolutionDifferential_morphism_eq_zsmul_id,
    Functor.map_zsmul, Functor.map_id]
""",
         """theorem tensorCyclicShortComplex_g_eq_zsmul_id (M N : ℕ) :
    (tensorCyclicShortComplex M N).g =
      (N : ℤ) • 𝟙 ((tensorCyclicShortComplex M N).X₂) := by
  change
    (cyclicTensorFunctor M).map ((cyclicFreeComplex N).d 1 0) = _
  rw [cyclicFreeComplex_d_one_zero,
    cyclicResolutionDifferential_morphism_eq_zsmul_id]
  change
    (cyclicTensorFunctor M).map
        ((N : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) =
      (N : ℤ) • 𝟙 ((cyclicTensorFunctor M).obj (ModuleCat.of ℤ ℤ))
  rw [Functor.map_zsmul, Functor.map_id]
""", "expose tensor functor zsmul target"),
        ("""theorem tensorCyclicShortComplex_g_unitor_comm (M N : ℕ) :
    (tensorCyclicShortComplex M N).g ≫
        (tensorCyclicRightUnitor M).hom =
      (tensorCyclicRightUnitor M).hom ≫
        ModuleCat.ofHom (cyclicNsmulLinearMap N M) := by
  rw [tensorCyclicShortComplex_g_eq_zsmul_id,
    cyclicNsmul_morphism_eq_zsmul_id,
    Preadditive.zsmul_comp, Category.id_comp,
    Preadditive.comp_zsmul, Category.comp_id]
""",
         """theorem tensorCyclicShortComplex_g_unitor_comm (M N : ℕ) :
    (tensorCyclicShortComplex M N).g ≫
        (tensorCyclicRightUnitor M).hom =
      (tensorCyclicRightUnitor M).hom ≫
        ModuleCat.ofHom (cyclicNsmulLinearMap N M) := by
  rw [tensorCyclicShortComplex_g_eq_zsmul_id,
    cyclicNsmul_morphism_eq_zsmul_id]
  change
    ((N : ℤ) • 𝟙 ((cyclicTensorFunctor M).obj (ModuleCat.of ℤ ℤ))) ≫
        (tensorCyclicRightUnitor M).hom =
      (tensorCyclicRightUnitor M).hom ≫
        ((N : ℤ) • 𝟙 (ModuleCat.of ℤ (ZMod M)))
  rw [Preadditive.zsmul_comp, Category.id_comp,
    Preadditive.comp_zsmul, Category.comp_id]
""", "expose unitor zsmul objects"),
        ("""def cyclicNsmulKernelLinearEquiv (N M : ℕ) :
    LinearMap.ker (cyclicNsmulLinearMap N M) ≃ₗ[ℤ]
      CyclicTorOneModel N M where
  toFun x := ⟨x, by
    simpa [cyclicNsmulLinearMap, CyclicTorOneModel] using x.property⟩
  invFun x := ⟨x, by
    simpa [cyclicNsmulLinearMap, CyclicTorOneModel] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
""",
         """def cyclicNsmulKernelLinearEquiv (N M : ℕ) :
    LinearMap.ker (cyclicNsmulLinearMap N M) ≃ₗ[ℤ]
      CyclicTorOneModel N M where
  toFun x := ⟨x, by
    change N • (x : ZMod M) = 0
    change cyclicNsmulLinearMap N M x = 0 at x.property
    exact x.property⟩
  invFun x := ⟨x, by
    change cyclicNsmulLinearMap N M x = 0
    change N • (x : ZMod M) = 0 at x.property
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
""", "identify both cyclic kernel predicates"),
    ])
    edit(F, [
        ("""  simp only [raiseRaw, lowerRaw, star_add, star_mul', star_div,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  field_simp [hh]
  ring
""",
         """  have hI : star (Complex.I) = -Complex.I := by simp
  have hweight :
      star (physicalExponent a / heightC z) =
        physicalExponent a / heightC z := by
    simp only [star_div, conj_physicalExponent, conj_heightC]
  simp only [raiseRaw, lowerRaw, star_add, star_mul']
  rw [hI, hweight]
  field_simp [hh]
  ring
""", "match Green conjugation in division form"),
        ("""  filter_upwards [hz] with w hw
  exact hw
""",
         """  filter_upwards [hz] with w hw
  simpa only [upperLift_apply, Pi.zero_apply] using hw
""", "evaluate upperLift on upper-half-plane points"),
    ])
    return 0

if __name__ == "__main__": raise SystemExit(main())
