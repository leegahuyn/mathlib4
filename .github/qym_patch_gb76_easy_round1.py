#!/usr/bin/env python3
import argparse, pathlib

def span(s, a, b, r):
    i=s.index(a); j=s.index(b,i)
    return s[:i]+r+s[j:]

def once(s,a,b):
    assert s.count(a)==1,(a[:80],s.count(a)); return s.replace(a,b,1)

p=argparse.ArgumentParser(); p.add_argument('src'); p.add_argument('dst'); p.add_argument('variant',choices=['convert','change','norm_num']); a=p.parse_args()
s=pathlib.Path(a.src).read_text()

# A: explicit hypotheses are supplied with letI, never registered as uninferable instances.
s=span(s,'local instance conditionalHasGroupoidH :','/-- Compose the all-sheets atlas', '''noncomputable def conditionalHasGroupoidH
    (hSmooth : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth

''')
s=span(s,'local instance conditionalHasGroupoidComplex :','/-- Conditional construction of the genuine smooth quotient manifold.', '''noncomputable def conditionalHasGroupoidComplex
    (hSmooth : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he

''')
s=span(s,'theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :','/-! ## 5. Open stage interiors -/', '''theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

noncomputable def conditionalIsManifold
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth

/-! ## 5. Open stage interiors -/
''')
s=span(s,'theorem interiorStageInclusion_contMDiff','end ConditionalSmoothAtlas', '''theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := conditionalIsManifold hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas''')

# B: fixed-fibre topology and explicit transported-coordinate proofs.
needle='''noncomputable abbrev InverseEtaFibre (x : InverseEtaBase) :=
  QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.EtaAutomorphicLineBundle.Fibre x
'''
s=once(s,needle,needle+'''
noncomputable instance inverseEtaFibreTopologicalSpace (x : InverseEtaBase) :
    TopologicalSpace (InverseEtaFibre x) := by
  change TopologicalSpace {z : InverseEtaTotal // inverseEtaProjection z = x}
  infer_instance
''')
s=span(s,'@[simp] theorem inverseEtaFibreOfCoordinate_coordinate','/-- Every actual quotient fibre is canonically equivalent', '''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  change totalOfBaseScalar x (etaTrivializedCoordinate u.1) = u.1
  calc
    _ = totalOfBaseScalar (inverseEtaProjection u.1)
          (etaTrivializedCoordinate u.1) :=
      congrArg (fun y : InverseEtaBase =>
        totalOfBaseScalar y (etaTrivializedCoordinate u.1)) u.2.symm
    _ = u.1 := totalOfBaseScalar_projection_coordinate u.1

/-- Every actual quotient fibre is canonically equivalent''')
cont={
'convert':'''  have hPair : Continuous (fun c : ℂ => (x, c)) := continuous_const.prodMk continuous_id
  have hTotal : Continuous (fun c : ℂ => totalOfBaseScalar x c) := by
    convert totalOfBaseScalar_continuous.comp hPair using 1
''',
'change':'''  have hPair : Continuous (fun c : ℂ => (x, c)) := continuous_const.prodMk continuous_id
  have hTotal := totalOfBaseScalar_continuous.comp hPair
  change Continuous (fun c : ℂ => totalOfBaseScalar x c) at hTotal
''',
'norm_num':'''  have hPair : Continuous (fun c : ℂ => (x, c)) := continuous_const.prodMk continuous_id
  have hTotal : Continuous (fun c : ℂ => totalOfBaseScalar x c) := by
    exact (show Continuous ((fun p : InverseEtaBase × ℂ =>
      totalOfBaseScalar p.1 p.2) ∘ fun c : ℂ => (x, c)) from
      totalOfBaseScalar_continuous.comp hPair)
'''}[a.variant]
s=span(s,'theorem inverseEtaFibreOfCoordinate_continuous','/-- Each actual quotient fibre is homeomorphic', '''theorem inverseEtaFibreOfCoordinate_continuous (x : InverseEtaBase) :
    Continuous (inverseEtaFibreOfCoordinate x) := by
'''+cont+'''  change Continuous (fun c : ℂ =>
    (⟨totalOfBaseScalar x c, inverseEtaProjection_totalOfBaseScalar x c⟩ :
      {z : InverseEtaTotal // inverseEtaProjection z = x}))
  exact hTotal.subtype_mk (fun c => inverseEtaProjection_totalOfBaseScalar x c)

/-- Each actual quotient fibre is homeomorphic''')
s=span(s,'@[simp] theorem inverseEtaFibreCoordinate_smul','/-- A local coordinate represented', '''@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) = c * inverseEtaFibreCoordinate u := by
  change (inverseEtaFibreCoordinateLinearEquiv x) (c • u) =
    c * (inverseEtaFibreCoordinateLinearEquiv x) u
  simpa only [smul_eq_mul] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u

/-- A local coordinate represented''')
s=span(s,'@[simp] theorem inverseEtaFibreMk_zero','/-! ## 6. Descent of the exact inverse-eta Hermitian metric -/', '''@[simp] theorem inverseEtaFibreMk_zero (tau : H) :
    inverseEtaFibreMk tau 0 =
      (0 : InverseEtaFibre (Mock2.Definition15Geometry.quotientMap tau)) := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change inverseEtaFibreCoordinate (inverseEtaFibreMk tau 0) =
    inverseEtaFibreCoordinate
      (0 : InverseEtaFibre (Mock2.Definition15Geometry.quotientMap tau))
  rw [inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_zero]
  simp

@[simp] theorem inverseEtaFibreMk_add (tau : H) (z w : ℂ) :
    inverseEtaFibreMk tau (z + w) =
      inverseEtaFibreMk tau z + inverseEtaFibreMk tau w := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change inverseEtaFibreCoordinate (inverseEtaFibreMk tau (z + w)) =
    inverseEtaFibreCoordinate (inverseEtaFibreMk tau z + inverseEtaFibreMk tau w)
  rw [inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_add,
    inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_mk, mul_add]

@[simp] theorem inverseEtaFibreMk_smul (tau : H) (c z : ℂ) :
    inverseEtaFibreMk tau (c * z) = c • inverseEtaFibreMk tau z := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change inverseEtaFibreCoordinate (inverseEtaFibreMk tau (c * z)) =
    inverseEtaFibreCoordinate (c • inverseEtaFibreMk tau z)
  rw [inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_smul,
    inverseEtaFibreCoordinate_mk]
  ring

/-! ## 6. Descent of the exact inverse-eta Hermitian metric -/''')
s=span(s,'theorem inverseEtaFibreHermitian_smul_right','/-- The real part on the diagonal', '''theorem inverseEtaFibreHermitian_smul_right
    {x : InverseEtaBase} (c : ℂ) (u v : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (c • v) = c * inverseEtaFibreHermitian u v := by
  unfold inverseEtaFibreHermitian
  rw [inverseEtaFibreCoordinate_smul]
  change ⟪inverseEtaFibreCoordinate u, c • inverseEtaFibreCoordinate v⟫_ℂ =
    c • ⟪inverseEtaFibreCoordinate u, inverseEtaFibreCoordinate v⟫_ℂ
  exact inner_smul_right _ _ _

/-- The real part on the diagonal''')
s=span(s,'theorem inverseEtaFibreHermitian_self_pos','/-- The Hermitian norm on the actual quotient total space.', '''theorem inverseEtaFibreHermitian_self_pos
    {x : InverseEtaBase} {u : InverseEtaFibre x} (hu : u ≠ 0) :
    0 < (inverseEtaFibreHermitian u u).re := by
  rw [inverseEtaFibreHermitian_self_re]
  have hc : inverseEtaFibreCoordinate u ≠ 0 := by
    intro hz; apply hu; apply (inverseEtaFibreCoordinateEquiv x).injective
    change inverseEtaFibreCoordinate u =
      inverseEtaFibreCoordinate (0 : InverseEtaFibre x)
    simpa only [inverseEtaFibreCoordinate_zero] using hz
  exact sq_pos_of_pos (norm_pos_iff.mpr hc)

/-- The Hermitian norm on the actual quotient total space.''')
s=once(s,'  inverseEtaTotalMk tau (f : H -> ℂ) tau\n','  inverseEtaTotalMk tau ((f : H -> ℂ) tau)\n')

# C: finite increase only.
s=once(s,'set_option maxHeartbeats 2000000 in\n/-- A concrete smooth-core constant also controls','set_option maxHeartbeats 8000000 in\n/-- A concrete smooth-core constant also controls')

# G: explicit pointwise and indicator reductions.
s=span(s,'  by_cases hx : x ∈ naturalStageSet n\n  · simp only [globalStageProjectionRepresentative, hx,\n      Set.indicator_of_mem, huv]','/-- Complex homogeneity', '''  by_cases hx : x ∈ naturalStageSet n
  · rw [globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx, Pi.add_apply]
  · rw [globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx, add_zero]

/-- Complex homogeneity''')
s=span(s,'  by_cases hx : x ∈ naturalStageSet n\n  · simp only [globalStageProjectionRepresentative, hx,\n      Set.indicator_of_mem, hcu]','/-! ## 4. The bounded global projection operator -/', '''  by_cases hx : x ∈ naturalStageSet n
  · rw [globalStageProjectionRepresentative, Set.indicator_of_mem hx,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx, Pi.smul_apply]
  · rw [globalStageProjectionRepresentative, Set.indicator_of_notMem hx,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx, smul_zero]

/-! ## 4. The bounded global projection operator -/''')
s=span(s,'  by_cases hx : x ∈ naturalStageSet n\n  · simp [globalStageProjectionErrorDensity,','/-- The global dominating density', '''  by_cases hx : x ∈ naturalStageSet n
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]

/-- The global dominating density''')
s=once(s,'''  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hn]
''','''  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
    ((n : ℝ) + 2) at hn
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hn]
''')
s=once(s,'''  have hx : x ∈ naturalStageSet n :=
    naturalStageSet_monotone hn hN
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hx]
''','''  have hx : x ∈ naturalStageSet n := naturalStageSet_monotone hn hN
  change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
    ((n : ℝ) + 2) at hx
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hx]
''')

# H variants.
h={'convert':'  norm_cast\n','change':'''  simp only [map_add, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
''','norm_num':'  norm_num\n'}[a.variant]
s=once(s,'''  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
''','''  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
'''+h)
pathlib.Path(a.dst).write_text(s)
print(a.variant, len(s))
