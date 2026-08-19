#!/usr/bin/env python3
from pathlib import Path
import hashlib, sys
BASE='8abc23b49c1cabed88fac0a67c3958d4dec7411d9c078ff555e137a1c19560d7'

def one(t,a,b,label):
 c=t.count(a)
 if c!=1: raise SystemExit(f'{label}: {c}')
 return t.replace(a,b,1)

def main():
 p=Path(sys.argv[1]); q=Path(sys.argv[2]); raw=p.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=BASE: raise SystemExit('wrong base')
 t=raw.decode()
 t=one(t,
'''    simpa only [Function.comp_apply] using
      totalOfBaseScalar_continuous.comp
        (continuous_const.prodMk continuous_id)
''',
'''    simpa only [Function.comp_apply, id_eq] using
      totalOfBaseScalar_continuous.comp
        (continuous_const.prodMk continuous_id)
''','fibre continuity')
 t=one(t,
'''  · intro huv
    apply (QYM.FullCertification.P3InverseEtaQuotientBundleExtension.inverseEtaFibreCoordinateEquiv
      (actualStageBasePoint x)).injective
    simpa only [actualStageFibreValue_coordinate] using huv
''',
'''  · intro huv
    apply (QYM.FullCertification.P3InverseEtaQuotientBundleExtension.inverseEtaFibreCoordinateEquiv
      (actualStageBasePoint x)).injective
    change
      QYM.FullCertification.P3InverseEtaQuotientBundleExtension.inverseEtaFibreCoordinate
          (actualStageFibreValue u x) =
        QYM.FullCertification.P3InverseEtaQuotientBundleExtension.inverseEtaFibreCoordinate
          (actualStageFibreValue v x)
    simpa only [actualStageFibreValue_coordinate] using huv
''','fibre equality reverse')
 t=one(t,
'''  rw [inner_self_eq_norm_sq_to_K]
  change ‖u‖ ^ 2 = 0 ↔ u = 0
  rw [sq_eq_zero_iff, norm_eq_zero]
''',
'''  rw [inner_self_eq_norm_sq_to_K]
  simpa [sq_eq_zero_iff] using (norm_eq_zero : ‖u‖ = 0 ↔ u = 0)
''','petersson definiteness')
 t=one(t,
'''  rw [actualStageBundleValue, hx, actualStageSectionCoordinate]
  rw [← s.projection_toFun (actualStageBasePoint x)]
  exact QYM.FullCertification.P3InverseEtaQuotientBundleExtension.totalOfBaseScalar_projection_coordinate
    (s (actualStageBasePoint x))
''',
'''  rw [actualStageBundleValue, hx, actualStageSectionCoordinate]
  calc
    QYM.FullCertification.P3InverseEtaQuotientBundleExtension.totalOfBaseScalar
        (actualStageBasePoint x)
        (QYM.FullCertification.P3InverseEtaQuotientBundleExtension.etaTrivializedCoordinate
          (s (actualStageBasePoint x))) =
      QYM.FullCertification.P3InverseEtaQuotientBundleExtension.totalOfBaseScalar
        (QYM.FullCertification.P3InverseEtaQuotientBundleExtension.inverseEtaProjection
          (s (actualStageBasePoint x)))
        (QYM.FullCertification.P3InverseEtaQuotientBundleExtension.etaTrivializedCoordinate
          (s (actualStageBasePoint x))) := by
            rw [s.projection_toFun]
    _ = s (actualStageBasePoint x) :=
      QYM.FullCertification.P3InverseEtaQuotientBundleExtension.totalOfBaseScalar_projection_coordinate _
''','bundle value ae')
 t=one(t,
'''  Mock2FA.PaperCorrections.AutomorphicSobolev.ExplicitDiscriminantPotential.potential_pos (actualStageBasePoint x)
''',
'''  Mock2FA.PaperCorrections.AutomorphicSobolev.ExplicitDiscriminantPotential.potential_pos
    (x : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient)
''','potential positivity')
 t=one(t,
'''  by_cases hx : x ∈ naturalStageSet n
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Set.indicator_of_mem hx]
    simpa only [Pi.add_apply] using huv
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx]
    simp
''',
'''  by_cases hx : x ∈ naturalStageSet n
  · simpa [globalStageProjectionRepresentative, hx, Pi.add_apply] using huv
  · simp [globalStageProjectionRepresentative, hx]
''','projection add')
 t=one(t,
'''  by_cases hx : x ∈ naturalStageSet n
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simpa only [Pi.smul_apply, smul_eq_mul] using hcu
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp
''',
'''  by_cases hx : x ∈ naturalStageSet n
  · simpa [globalStageProjectionRepresentative, hx, Pi.smul_apply, smul_eq_mul] using hcu
  · simp [globalStageProjectionRepresentative, hx]
''','projection smul')
 t=one(t,
'''  by_cases hx : x ∈ naturalStageSet n
  · change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [globalStageProjectionErrorDensity, globalL2DominatingDensity,
      globalStageProjectionRepresentative, Set.indicator_of_mem hx]
    simp
  · change x ∉ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
      ((n : ℝ) + 2) at hx
    rw [globalStageProjectionErrorDensity, globalL2DominatingDensity,
      globalStageProjectionRepresentative, Set.indicator_of_notMem hx]
    simp
''',
'''  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
  · simp [globalStageProjectionErrorDensity, globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
''','density bound')
 t=one(t,
'''  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
    ((n : ℝ) + 2) at hn
  rw [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, Set.indicator_of_mem hn]
  simp
''',
'''  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hn]
''','density eventually zero')
 t=one(t,
'''  have hx : x ∈ naturalStageSet n :=
    naturalStageSet_monotone hn hN
  change x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet
    ((n : ℝ) + 2) at hx
  rw [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, Set.indicator_of_mem hx]
  simp
''',
'''  have hx : x ∈ naturalStageSet n :=
    naturalStageSet_monotone hn hN
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hx]
''','density pointwise')
 t=one(t,
'''  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  change
    ‖covariantDerivative u‖ ^ 2 +
      (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 =
    ‖covariantDerivative u‖ ^ 2 +
      (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2
  rfl
''',
'''  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_num
''','hamiltonian real part')
 t=one(t,
'''  simpa only [Function.comp_apply,
    QYM.FullCertification.P3InverseEtaQuotientBundleExtension.inverseEtaTotalTrivializationHomeomorph_fst] using
''',
'''  simpa [Function.comp_apply,
    QYM.FullCertification.P3InverseEtaQuotientBundleExtension.inverseEtaTotalTrivializationHomeomorph_fst] using
''','projection contmdiff simp')
 t=one(t,
'''  simpa only [Function.comp_apply] using
    (contMDiff_snd.comp
''',
'''  simpa [Function.comp_apply] using
    (contMDiff_snd.comp
''','eta coordinate contmdiff simp')
 q.write_text(t)
 result=hashlib.sha256(q.read_bytes()).hexdigest()
 if result!='ad39de0ce64e45483f062d18ae289a377c25c474e643c1d3cdb84813ab11a2c2':
  raise SystemExit('unexpected candidate '+result)
 print('sha256='+result)
if __name__=='__main__': main()
