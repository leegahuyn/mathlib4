from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / 'PrimalitySheafVerification' / 'Mock2.lean'
M2A = ROOT / 'PrimalitySheafVerification' / 'Mock2_Advanced.lean'
FA = ROOT / 'PrimalitySheafVerification' / 'Mock2_FunctionalAnalysis.lean'


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'{label}: expected exactly one match, found {count}')
    print(f'{label}: applied 1')
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding='utf-8')
    m2 = replace_once(m2, '''def toMathlibPresheaf
    (P : QGaugePresheaf (TopologicalSpace.Opens X)) :
    TopCat.Presheaf (Type v) (TopCat.of X) where
  obj U := P.Field U.unop
  map f := P.res f.unop.le
  map_id U := by
    funext s
    exact P.res_id U.unop s
  map_comp f g := by
    funext s
    exact (P.res_comp g.unop.le f.unop.le s).symm
''', '''def toMathlibPresheaf
    (P : QGaugePresheaf (TopologicalSpace.Opens X)) :
    TopCat.Presheaf (Type v) (TopCat.of X) where
  obj U := P.Field U.unop
  map f := ConcreteCategory.ofHom (P.res f.unop.le)
  map_id U := by
    apply ConcreteCategory.ext_apply
    intro s
    exact P.res_id U.unop s
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    intro s
    exact (P.res_comp g.unop.le f.unop.le s).symm
''', 'm2 presheaf morphisms')
    m2 = replace_once(m2, '''    (toMathlibPresheaf P).map f s = P.res f.unop.le s :=
  rfl
''', '''    (toMathlibPresheaf P).map f s = P.res f.unop.le s := by
  change ConcreteCategory.hom
      (ConcreteCategory.ofHom (P.res f.unop.le)) s = _
  rw [ConcreteCategory.hom_ofHom]
''', 'm2 map apply')
    m2 = replace_once(m2, '''def toMathlibNatTrans
    {P Q : QGaugePresheaf (TopologicalSpace.Opens X)}
    (φ : QGaugePresheaf.Morphism P Q) :
    toMathlibPresheaf P ⟶ toMathlibPresheaf Q where
  app U := φ.app U.unop
  naturality := by
    intro U W f
    funext s
    exact (φ.naturality f.unop.le s).symm
''', '''def toMathlibNatTrans
    {P Q : QGaugePresheaf (TopologicalSpace.Opens X)}
    (φ : QGaugePresheaf.Morphism P Q) :
    toMathlibPresheaf P ⟶ toMathlibPresheaf Q where
  app U := ConcreteCategory.ofHom (φ.app U.unop)
  naturality := by
    intro U W f
    apply ConcreteCategory.ext_apply
    intro s
    exact (φ.naturality f.unop.le s).symm
''', 'm2 nattrans morphisms')
    m2 = replace_once(m2, '''    (toMathlibNatTrans φ).app U s = φ.app U.unop s :=
  rfl
''', '''    (toMathlibNatTrans φ).app U s = φ.app U.unop s := by
  change ConcreteCategory.hom
      (ConcreteCategory.ofHom (φ.app U.unop)) s = _
  rw [ConcreteCategory.hom_ofHom]
''', 'm2 nattrans apply')
    m2 = replace_once(m2, '''  have hcompat :
      (QGaugePresheaf.toPresheafLike P).CompatibleFamily C sf := by
    intro i j
    exact hsf i j
  obtain ⟨s, hs, huniq⟩ := hP.existsUnique_gluing C sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    change P.res (le_iSup U i) s = sf i
    exact hs i
  · intro t ht
    apply huniq t
    intro i
    change P.res (le_iSup U i) t = sf i
    exact ht i
''', '''  have hcompat :
      (QGaugePresheaf.toPresheafLike P).CompatibleFamily C sf := by
    intro i j
    simpa only [toMathlibPresheaf_map_apply] using hsf i j
  obtain ⟨s, hs, huniq⟩ := hP.existsUnique_gluing C sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa only [toMathlibPresheaf_map_apply] using hs i
  · intro t ht
    apply huniq t
    intro i
    simpa only [toMathlibPresheaf_map_apply] using ht i
''', 'm2 sheaf gluing bridge')
    m2 = replace_once(m2, '''    (toMathlibSheafMorphism φ hP hQ).hom.app U s = φ.app U.unop s :=
  rfl
''', '''    (toMathlibSheafMorphism φ hP hQ).hom.app U s = φ.app U.unop s := by
  change (toMathlibNatTrans φ).app U s = _
  exact toMathlibNatTrans_app φ U s
''', 'm2 sheaf morphism apply')
    m2 = replace_once(m2, '''abbrev ActualSheafCategory :=
  TopCat.Sheaf (Type v) (TopCat.of RadiusBase)
''', '''abbrev ActualSheafCategory :=
  TopCat.Sheaf (Type 0) (TopCat.of RadiusBase)
''', 'm2 actual sheaf universe')
    M2.write_text(m2, encoding='utf-8')

    m2a = M2A.read_text(encoding='utf-8')
    m2a = replace_once(m2a, '''  spectral_identification := by
    intro n m
    rw [truncatedMass_eq_three_mul T hT n m]
    simp [symmetricRealExhaustion, Gamma2Cusp.card_eq, nsmul_eq_mul]
''', '''  spectral_identification := by
    intro n m
    rw [truncatedMass_eq_three_mul T hT n m]
    simp [rankinSelbergFamily, symmetricRealExhaustion,
      Gamma2Cusp.card_eq, nsmul_eq_mul]
''', 'm2a finite spectral measure')
    m2a = replace_once(m2a, '''  geometric_sFinite := inferInstance
  spectral_sFinite := fun _ => inferInstance
''', '''  geometric_sFinite := by
    change SFinite (volume : Measure ℝ)
    infer_instance
  spectral_sFinite := by
    intro k
    change SFinite (volume : Measure ℝ)
    infer_instance
''', 'm2a explicit sfinite')
    m2a = replace_once(m2a, '''  geometric_identification := by
    intro n m
    rw [geometricStage_eq_three_mul T hT n m]
    simp [productKernel_iterated_geometric, Gamma2Cusp.card_eq,
      nsmul_eq_mul]
  spectral_identification := by
    intro n m
    rw [truncatedMass_eq_three_mul T hT n m]
    simp [productKernel_iterated_spectral, Gamma2Cusp.card_eq,
      nsmul_eq_mul]
''', '''  geometric_identification := by
    intro n m
    rw [geometricStage_eq_three_mul T hT n m]
    simp [rankinSelbergFamily, spectralData,
      productKernel_iterated_geometric, Gamma2Cusp.card_eq,
      nsmul_eq_mul]
  spectral_identification := by
    intro n m
    rw [truncatedMass_eq_three_mul T hT n m]
    simp [rankinSelbergFamily, spectralData,
      productKernel_iterated_spectral, Gamma2Cusp.card_eq,
      nsmul_eq_mul]
''', 'm2a product identifications')
    M2A.write_text(m2a, encoding='utf-8')

    fa = FA.read_text(encoding='utf-8')
    fa = replace_once(fa, '''noncomputable def inverseEtaPaperOrbitMultiplier
    (Γ : Subgroup SL(2, ℤ)) (n : ℤ) :
    HalfIntegralMultiplier Γ (-paperOrbitExponent n) := by
  simpa only [neg_paperOrbitExponent] using
    inverseEtaHalfOrbitMultiplier Γ n
''', '''noncomputable def inverseEtaPaperOrbitMultiplier
    (Γ : Subgroup SL(2, ℤ)) (n : ℤ) :
    HalfIntegralMultiplier Γ (-paperOrbitExponent n) where
  nu := (inverseEtaHalfOrbitMultiplier Γ n).nu
  nu_one := (inverseEtaHalfOrbitMultiplier Γ n).nu_one
  nu_norm := (inverseEtaHalfOrbitMultiplier Γ n).nu_norm
  sqrtFactor := (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor
  sqrtFactor_one := (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor_one
  sqrtFactor_sq := (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor_sq
  factor_cocycle := by
    intro γ δ z
    have h := (inverseEtaHalfOrbitMultiplier Γ n).factor_cocycle γ δ z
    convert h using 1 <;> ring
''', 'fa orbit multiplier direct structure')
    fa = replace_once(fa, '''  simpa only [inverseEtaPaperOrbitMultiplier, neg_paperOrbitExponent] using
    inverseEtaHalfOrbitMultiplier_factor Γ n γ z
''', '''  change
    (inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          (-(-paperOrbitExponent n)) = _
  have h := inverseEtaHalfOrbitMultiplier_factor Γ n γ z
  unfold HalfIntegralMultiplier.factor at h
  convert h using 1 <;> ring
''', 'fa orbit factor')
    fa = replace_once(fa, '''  simpa only [inverseEtaPaperOrbitMultiplier, neg_paperOrbitExponent] using
    inverseEtaHalfOrbitMultiplier_factor_add_one Γ n γ z
''', '''  change
    (inverseEtaHalfOrbitMultiplier Γ (n + 1)).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ (n + 1)).sqrtFactor γ z ^
          (-(-paperOrbitExponent (n + 1))) =
      ((inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          (-(-paperOrbitExponent n))) *
        UpperHalfPlane.denom
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z ^ (2 : ℕ)
  have h := inverseEtaHalfOrbitMultiplier_factor_add_one Γ n γ z
  unfold HalfIntegralMultiplier.factor at h
  convert h using 1 <;> ring
''', 'fa orbit factor add one')
    fa = replace_once(fa, '''  simpa only [inverseEtaPaperOrbitMultiplier, neg_paperOrbitExponent]
''', '''  change (inverseEtaHalfOrbitMultiplier Γ n).nu γ = _
  rfl
''', 'fa orbit nu')
    FA.write_text(fa, encoding='utf-8')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
