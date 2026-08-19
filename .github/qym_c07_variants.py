#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,sys

BASELINE_SHA256='830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217'
BASELINE_BLOB='e796aa6ae9f01965116902a9345ed69f81bcfc42'
VARIANTS={'change_infer','explicit_induced','explicit_covariant'}

FIBRE='''noncomputable abbrev InverseEtaFibre (x : InverseEtaBase) :=
  QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.EtaAutomorphicLineBundle.Fibre x
'''
TOPO_CHANGE=FIBRE+'''\n/-- The fixed quotient fibre carries the literal subtype topology inherited
from the already topologized quotient total space. -/
noncomputable instance inverseEtaFibreTopologicalSpace (x : InverseEtaBase) :
    TopologicalSpace (InverseEtaFibre x) := by
  change TopologicalSpace
    {u : InverseEtaTotal // inverseEtaProjection u = x}
  infer_instance
'''
TOPO_INDUCED=FIBRE+'''\n/-- The fixed quotient fibre carries the literal subtype topology inherited
from the already topologized quotient total space. -/
noncomputable instance inverseEtaFibreTopologicalSpace (x : InverseEtaBase) :
    TopologicalSpace (InverseEtaFibre x) :=
  TopologicalSpace.induced
    (fun u : InverseEtaFibre x => u.1)
    inverseEtaTotalTopologicalSpace
'''

OLD_DEP='''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  change
    totalOfBaseScalar x (etaTrivializedCoordinate u.1) = u.1
  rw [← u.2]
  exact totalOfBaseScalar_projection_coordinate u.1
'''
NEW_DEP='''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  change
    totalOfBaseScalar x (etaTrivializedCoordinate u.1) = u.1
  simpa only [u.2] using
    totalOfBaseScalar_projection_coordinate u.1
'''

OLD_CONT='''theorem inverseEtaFibreOfCoordinate_continuous (x : InverseEtaBase) :
    Continuous (inverseEtaFibreOfCoordinate x) := by
  have hTotal : Continuous
      (fun c : ℂ => totalOfBaseScalar x c) := by
    simpa only [Function.comp_apply] using
      totalOfBaseScalar_continuous.comp
        (continuous_const.prodMk continuous_id)
  exact hTotal.subtype_mk
    (fun c => inverseEtaProjection_totalOfBaseScalar x c)
'''
NEW_CONT='''theorem inverseEtaFibreOfCoordinate_continuous (x : InverseEtaBase) :
    Continuous (inverseEtaFibreOfCoordinate x) := by
  have hTotal : Continuous
      (fun c : ℂ => totalOfBaseScalar x c) := by
    simpa only [Function.comp_apply, id_eq] using
      totalOfBaseScalar_continuous.comp
        (continuous_const.prodMk continuous_id)
  refine hTotal.subtype_mk ?_
  intro c
  exact inverseEtaProjection_totalOfBaseScalar x c
'''

LINEAR='''noncomputable def inverseEtaFibreCoordinateLinearEquiv
    (x : InverseEtaBase) : InverseEtaFibre x ≃ₗ[ℂ] ℂ :=
  (inverseEtaFibreCoordinateEquiv x).linearEquiv ℂ
'''
LINEAR_PLUS=LINEAR+'''\n@[simp] theorem inverseEtaFibreCoordinateLinearEquiv_apply
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinateLinearEquiv x u =
      inverseEtaFibreCoordinate u :=
  rfl
'''

OLD_MAPS='''@[simp] theorem inverseEtaFibreCoordinate_zero (x : InverseEtaBase) :
    inverseEtaFibreCoordinate (0 : InverseEtaFibre x) = 0 :=
  (inverseEtaFibreCoordinateLinearEquiv x).map_zero

@[simp] theorem inverseEtaFibreCoordinate_add
    {x : InverseEtaBase} (u v : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (u + v) =
      inverseEtaFibreCoordinate u + inverseEtaFibreCoordinate v :=
  (inverseEtaFibreCoordinateLinearEquiv x).map_add u v

@[simp] theorem inverseEtaFibreCoordinate_neg
    {x : InverseEtaBase} (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (-u) = -inverseEtaFibreCoordinate u :=
  (inverseEtaFibreCoordinateLinearEquiv x).map_neg u

@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) =
      c * inverseEtaFibreCoordinate u := by
  simpa only [smul_eq_mul] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u
'''
NEW_MAPS='''@[simp] theorem inverseEtaFibreCoordinate_zero (x : InverseEtaBase) :
    inverseEtaFibreCoordinate (0 : InverseEtaFibre x) = 0 := by
  simpa only [inverseEtaFibreCoordinateLinearEquiv_apply] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_zero

@[simp] theorem inverseEtaFibreCoordinate_add
    {x : InverseEtaBase} (u v : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (u + v) =
      inverseEtaFibreCoordinate u + inverseEtaFibreCoordinate v := by
  simpa only [inverseEtaFibreCoordinateLinearEquiv_apply] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_add u v

@[simp] theorem inverseEtaFibreCoordinate_neg
    {x : InverseEtaBase} (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (-u) = -inverseEtaFibreCoordinate u := by
  simpa only [inverseEtaFibreCoordinateLinearEquiv_apply] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_neg u

@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) =
      c * inverseEtaFibreCoordinate u := by
  simpa only [inverseEtaFibreCoordinateLinearEquiv_apply,
    smul_eq_mul] using
      (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u
'''

OLD_MK='''@[simp] theorem inverseEtaFibreMk_zero (tau : H) :
    inverseEtaFibreMk tau 0 =
      (0 : InverseEtaFibre
        (Mock2.Definition15Geometry.quotientMap tau)) := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  simp

@[simp] theorem inverseEtaFibreMk_add
    (tau : H) (z w : ℂ) :
    inverseEtaFibreMk tau (z + w) =
      inverseEtaFibreMk tau z + inverseEtaFibreMk tau w := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  simp only [inverseEtaFibreCoordinate_mk,
    inverseEtaFibreCoordinate_add, mul_add]

@[simp] theorem inverseEtaFibreMk_smul
    (tau : H) (c z : ℂ) :
    inverseEtaFibreMk tau (c * z) =
      c • inverseEtaFibreMk tau z := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  simp only [inverseEtaFibreCoordinate_mk,
    inverseEtaFibreCoordinate_smul]
  ring
'''
NEW_MK='''@[simp] theorem inverseEtaFibreMk_zero (tau : H) :
    inverseEtaFibreMk tau 0 =
      (0 : InverseEtaFibre
        (Mock2.Definition15Geometry.quotientMap tau)) := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * 0 = 0
  simp

@[simp] theorem inverseEtaFibreMk_add
    (tau : H) (z w : ℂ) :
    inverseEtaFibreMk tau (z + w) =
      inverseEtaFibreMk tau z + inverseEtaFibreMk tau w := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change
    Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * (z + w) =
      Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z +
        Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * w
  ring

@[simp] theorem inverseEtaFibreMk_smul
    (tau : H) (c z : ℂ) :
    inverseEtaFibreMk tau (c * z) =
      c • inverseEtaFibreMk tau z := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change
    Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * (c * z) =
      c * (Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z)
  ring
'''

OLD_HERM='''theorem inverseEtaFibreHermitian_smul_right
    {x : InverseEtaBase} (c : ℂ) (u v : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (c • v) =
      c * inverseEtaFibreHermitian u v := by
  simp only [inverseEtaFibreHermitian,
    inverseEtaFibreCoordinate_smul, inner_smul_right]
'''
NEW_HERM='''theorem inverseEtaFibreHermitian_smul_right
    {x : InverseEtaBase} (c : ℂ) (u v : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (c • v) =
      c * inverseEtaFibreHermitian u v := by
  unfold inverseEtaFibreHermitian
  rw [inverseEtaFibreCoordinate_smul]
  simpa only [← smul_eq_mul] using
    (inner_smul_right
      (inverseEtaFibreCoordinate u)
      (inverseEtaFibreCoordinate v) c)
'''

OLD_POS='''theorem inverseEtaFibreHermitian_self_pos
    {x : InverseEtaBase} {u : InverseEtaFibre x} (hu : u ≠ 0) :
    0 < (inverseEtaFibreHermitian u u).re := by
  unfold inverseEtaFibreHermitian
  rw [re_inner_self_pos (𝕜 := ℂ)]
  intro hCoordinate
  apply hu
  apply (inverseEtaFibreCoordinateEquiv x).injective
  simpa using hCoordinate
'''
NEW_POS='''theorem inverseEtaFibreHermitian_self_pos
    {x : InverseEtaBase} {u : InverseEtaFibre x} (hu : u ≠ 0) :
    0 < (inverseEtaFibreHermitian u u).re := by
  have hCoordinate : inverseEtaFibreCoordinate u ≠ 0 := by
    intro hzero
    apply hu
    apply (inverseEtaFibreCoordinateEquiv x).injective
    simpa only [inverseEtaFibreCoordinate_zero] using hzero
  rw [inverseEtaFibreHermitian_self_re]
  exact pow_pos (norm_pos_iff.mpr hCoordinate) 2
'''

OLD_LIFT='''noncomputable def covariantTotalLift
    (f : EtaCovariantLift) (tau : H) : InverseEtaTotal :=
  inverseEtaTotalMk tau (f : H -> ℂ) tau
'''
NEW_LIFT='''noncomputable def covariantTotalLift
    (f : EtaCovariantLift) (tau : H) : InverseEtaTotal :=
  inverseEtaTotalMk tau ((f : H -> ℂ) tau)
'''

OLD_FUN_Q='''@[simp] theorem covariantToSectionFun_quotientMap
    (f : EtaCovariantLift) (tau : H) :
    covariantToSectionFun f
        (Mock2.Definition15Geometry.quotientMap tau) =
      inverseEtaTotalMk tau ((f : H -> ℂ) tau) := by
  rfl
'''
NEW_FUN_Q='''@[simp] theorem covariantToSectionFun_quotientMap
    (f : EtaCovariantLift) (tau : H) :
    covariantToSectionFun f
        (Mock2.Definition15Geometry.quotientMap tau) =
      inverseEtaTotalMk tau ((f : H -> ℂ) tau) := by
  change covariantTotalLift f tau = _
  rfl
'''

OLD_SECTION='''noncomputable def covariantToSection
    (f : EtaCovariantLift) : InverseEtaQuotientSection where
  toFun := covariantToSectionFun f
  projection_toFun x := by
    refine Quotient.inductionOn x ?_
    intro tau
    rfl

@[simp] theorem covariantToSection_quotientMap
    (f : EtaCovariantLift) (tau : H) :
    covariantToSection f
        (Mock2.Definition15Geometry.quotientMap tau) =
      inverseEtaTotalMk tau ((f : H -> ℂ) tau) := by
  rfl
'''
NEW_SECTION='''noncomputable def covariantToSection
    (f : EtaCovariantLift) : InverseEtaQuotientSection where
  toFun := covariantToSectionFun f
  projection_toFun x := by
    refine Quotient.inductionOn x ?_
    intro tau
    rw [covariantToSectionFun_quotientMap]
    exact inverseEtaProjection_mk tau ((f : H -> ℂ) tau)

@[simp] theorem covariantToSection_quotientMap
    (f : EtaCovariantLift) (tau : H) :
    covariantToSection f
        (Mock2.Definition15Geometry.quotientMap tau) =
      inverseEtaTotalMk tau ((f : H -> ℂ) tau) := by
  change covariantToSectionFun f
      (Mock2.Definition15Geometry.quotientMap tau) = _
  exact covariantToSectionFun_quotientMap f tau
'''

OLD_LEFT='''@[simp] theorem quotientSectionToCovariant_covariantToSection
    (f : EtaCovariantLift) :
    quotientSectionToCovariant (covariantToSection f) = f := by
  apply Subtype.ext
  funext tau
  change
    QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.inverseEtaSection tau *
        etaTrivializedCoordinate
          (inverseEtaTotalMk tau ((f : H -> ℂ) tau)) =
      (f : H -> ℂ) tau
  rw [etaTrivializedCoordinate_mk]
  simp [QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.inverseEtaSection, Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero, mul_assoc]
'''
NEW_LEFT='''@[simp] theorem quotientSectionToCovariant_covariantToSection
    (f : EtaCovariantLift) :
    quotientSectionToCovariant (covariantToSection f) = f := by
  apply Subtype.ext
  funext tau
  rw [quotientSectionToCovariant_apply,
    covariantToSection_quotientMap,
    etaTrivializedCoordinate_mk]
  simp [QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.inverseEtaSection,
    Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero,
    mul_assoc]
'''

OLD_DIST='''theorem covariantToSection_distinguished_toFun :
    (covariantToSection distinguishedInverseEtaLift).toFun =
      QYM.FullCertification.Mock2EtaQuotientMeasureExtension.descendedInverseEtaBundleSection := by
  funext x
  refine Quotient.inductionOn x ?_
  intro tau
  rfl
'''
NEW_DIST='''theorem covariantToSection_distinguished_toFun :
    (covariantToSection distinguishedInverseEtaLift).toFun =
      QYM.FullCertification.Mock2EtaQuotientMeasureExtension.descendedInverseEtaBundleSection := by
  funext x
  refine Quotient.inductionOn x ?_
  intro tau
  rw [covariantToSection_quotientMap]
  rfl
'''

OLD_COORD='''  obtain ⟨tau, rfl⟩ := QYM.FullCertification.Mock2EtaQuotientMeasureExtension.quotientMap_surjective x
  change Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.inverseEtaSection tau = 1
  simp [QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.inverseEtaSection, Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero]
'''
NEW_COORD='''  obtain ⟨tau, rfl⟩ := QYM.FullCertification.Mock2EtaQuotientMeasureExtension.quotientMap_surjective x
  rw [covariantToSection_quotientMap,
    etaTrivializedCoordinate_mk]
  simp [distinguishedInverseEtaLift,
    QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.inverseEtaSection,
    Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero]
'''

def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def audit(t): return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}

def rep(text,label,old,new):
    n=text.count(old)
    if n!=1: raise SystemExit(f'{label} count={n}')
    return text.replace(old,new,1)

def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS: raise SystemExit('usage: qym_c07_variants.py VARIANT QYM.lean')
    v,p=sys.argv[1],Path(sys.argv[2]); before=p.read_bytes()
    if hashlib.sha256(before).hexdigest()!=BASELINE_SHA256 or blob(before)!=BASELINE_BLOB: raise SystemExit('baseline mismatch')
    text=before.decode(); a0=audit(text)
    text=rep(text,'fibre topology',FIBRE,TOPO_CHANGE if v=='change_infer' else TOPO_INDUCED)
    for label,old,new in [('dependent inverse',OLD_DEP,NEW_DEP),('reconstruction continuity',OLD_CONT,NEW_CONT),('linear apply',LINEAR,LINEAR_PLUS),('linear maps',OLD_MAPS,NEW_MAPS),('fibre mk',OLD_MK,NEW_MK),('Hermitian smul',OLD_HERM,NEW_HERM),('Hermitian positivity',OLD_POS,NEW_POS),('covariant lift application',OLD_LIFT,NEW_LIFT)]: text=rep(text,label,old,new)
    if v=='explicit_covariant':
        for label,old,new in [('covariant quotient evaluation',OLD_FUN_Q,NEW_FUN_Q),('section projection/evaluation',OLD_SECTION,NEW_SECTION),('left inverse',OLD_LEFT,NEW_LEFT),('distinguished section',OLD_DIST,NEW_DIST),('distinguished coordinate',OLD_COORD,NEW_COORD)]: text=rep(text,label,old,new)
    a1=audit(text)
    if a1!=a0: raise SystemExit(f'forbidden delta {a0}->{a1}')
    p.write_text(text); after=p.read_bytes()
    print(json.dumps({'schema':'qym-c07-v1','variant':v,'input_sha256':BASELINE_SHA256,'input_blob':BASELINE_BLOB,'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':blob(after),'bytes':len(after),'lf':after.count(b'\n'),'fixed_producers_targeted':['inverseEtaFibreOfCoordinate','inverseEtaFibreCoordinate_continuous','inverseEtaFibreOfCoordinate_continuous','inverseEtaFibreCoordinateLinearEquiv','inverseEtaFibreMk','inverseEtaFibreHermitian','covariantTotalLift','covariantToSection'],'forbidden_before':a0,'forbidden_after':a1},indent=2,sort_keys=True))
if __name__=='__main__': main()
