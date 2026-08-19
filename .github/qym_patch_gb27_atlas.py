#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = 'ad39de0ce64e45483f062d18ae289a377c25c474e643c1d3cdb84813ab11a2c2'
EXPECTED_SHA256 = '13f61def42995ff3b1a1c3ca223e7bc8f1d6cc30728c3b64a8a5f25985dd07d4'
START = '/-! ## 1. The unconditional P2 base atlas -/'
END = '/-! ## 2. The explicitly transported atlas on the total space -/'

REPLACEMENT = r'''/-! ## 1. The unconditional P2 base atlas -/

/-- The inverse-eta base is the original `Gamma(2)` orbit quotient used by the
actual line bundle. -/
abbrev InverseEtaBase := QYM.FullCertification.P3InverseEtaQuotientBundleExtension.InverseEtaBase

/-- The effective quotient on which P2 constructed the smooth atlas. -/
abbrev EffectiveInverseEtaBase :=
  QYM.FullCertification.P3GammaTwoQuotientBridgeExtension.EffectiveGammaTwoQuotient

/-- The actual inverse-eta orbit-quotient total space. -/
abbrev InverseEtaTotal := QYM.FullCertification.P3InverseEtaQuotientBundleExtension.InverseEtaTotal

namespace Homeomorph

/-- Pull a charted-space atlas back along a global homeomorphism. -/
@[instance_reducible]
noncomputable def qymPullbackChartedSpace
    {H : Type*} {M M' : Type*}
    [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
    [ChartedSpace H M] (F : M' ≃ₜ M) : ChartedSpace H M' where
  atlas := {e | ∃ a ∈ atlas H M, e = F.toOpenPartialHomeomorph.trans a}
  chartAt x := F.toOpenPartialHomeomorph.trans (chartAt H (F x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt H (F x), chart_mem_atlas H (F x), rfl⟩

/-- Pulling an atlas back along a homeomorphism preserves every structure
groupoid already carried by the target atlas. -/
theorem qymPullback_hasGroupoid
    {H : Type*} {M M' : Type*}
    [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
    [ChartedSpace H M] (F : M' ≃ₜ M) (G : StructureGroupoid H)
    [HasGroupoid M G] :
    letI : ChartedSpace H M' := F.qymPullbackChartedSpace (H := H)
    HasGroupoid M' G := by
  letI : ChartedSpace H M' := F.qymPullbackChartedSpace (H := H)
  refine { compatible := ?_ }
  intro e e' he he'
  rcases he with ⟨a, ha, rfl⟩
  rcases he' with ⟨b, hb, rfl⟩
  let f := F.toOpenPartialHomeomorph
  refine G.mem_of_eqOnSource (G.compatible ha hb) ?_
  calc
    (f.trans a).symm.trans (f.trans b) =
        (a.symm.trans f.symm).trans (f.trans b) := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    _ = a.symm.trans ((f.symm.trans f).trans b) := by
      simp only [OpenPartialHomeomorph.trans_assoc]
    _ ≈ a.symm.trans
        ((OpenPartialHomeomorph.ofSet f.target f.open_target).trans b) :=
      OpenPartialHomeomorph.EqOnSource.trans'
        (Setoid.refl _)
        (OpenPartialHomeomorph.EqOnSource.trans'
          (OpenPartialHomeomorph.symm_trans_self f)
          (Setoid.refl _))
    _ = a.symm.trans b := by simp [f]

end Homeomorph

/-- Pull the proved P2 upper-half-plane atlas back from the effective quotient
to the original quotient along the explicit quotient homeomorphism. -/
noncomputable def inverseEtaBaseChartedSpaceH :
    ChartedSpace ℍ InverseEtaBase := by
  letI : ChartedSpace ℍ EffectiveInverseEtaBase :=
    QYM.FullCertification.P2SmoothQuotientAtlasExtension.allCoveringSheetsChartedSpaceH
  exact
    QYM.FullCertification.P3GammaTwoQuotientBridgeExtension.originalEffectiveHomeomorph
      |>.qymPullbackChartedSpace (H := ℍ)

/-- The pulled-back upper-half-plane atlas inherits the smooth structure
groupoid from the effective quotient. -/
theorem inverseEtaBase_hasUpperHalfPlaneGroupoid :
    letI : ChartedSpace ℍ EffectiveInverseEtaBase :=
      QYM.FullCertification.P2SmoothQuotientAtlasExtension.allCoveringSheetsChartedSpaceH
    letI : HasGroupoid EffectiveInverseEtaBase
        QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid :=
      QYM.FullCertification.P2SmoothTransitionClosureExtension.allCoveringSheets_hasGroupoid
    letI : ChartedSpace ℍ InverseEtaBase := inverseEtaBaseChartedSpaceH
    HasGroupoid InverseEtaBase
      QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid := by
  letI : ChartedSpace ℍ EffectiveInverseEtaBase :=
    QYM.FullCertification.P2SmoothQuotientAtlasExtension.allCoveringSheetsChartedSpaceH
  letI : HasGroupoid EffectiveInverseEtaBase
      QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid :=
    QYM.FullCertification.P2SmoothTransitionClosureExtension.allCoveringSheets_hasGroupoid
  letI : ChartedSpace ℍ InverseEtaBase := inverseEtaBaseChartedSpaceH
  exact
    Homeomorph.qymPullback_hasGroupoid
      QYM.FullCertification.P3GammaTwoQuotientBridgeExtension.originalEffectiveHomeomorph
      QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid

/-- The chosen complex smooth atlas on the inverse-eta base. -/
noncomputable def inverseEtaBaseChartedSpaceComplex :
    ChartedSpace ℂ InverseEtaBase := by
  letI : ChartedSpace ℍ InverseEtaBase := inverseEtaBaseChartedSpaceH
  exact ChartedSpace.comp ℂ ℍ InverseEtaBase

/-- The pulled-back P2 base atlas has the ordinary complex smooth structure
groupoid. -/
theorem inverseEtaBase_hasGroupoid :
    letI : ChartedSpace ℍ InverseEtaBase := inverseEtaBaseChartedSpaceH
    letI : HasGroupoid InverseEtaBase
        QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid :=
      inverseEtaBase_hasUpperHalfPlaneGroupoid
    letI : ChartedSpace ℂ InverseEtaBase := ChartedSpace.comp ℂ ℍ InverseEtaBase
    HasGroupoid InverseEtaBase (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : ChartedSpace ℍ InverseEtaBase := inverseEtaBaseChartedSpaceH
  letI : HasGroupoid InverseEtaBase
      QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid :=
    inverseEtaBase_hasUpperHalfPlaneGroupoid
  letI : ChartedSpace ℂ InverseEtaBase := ChartedSpace.comp ℂ ℍ InverseEtaBase
  apply StructureGroupoid.HasGroupoid.comp
    QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he

/-- The pulled-back P2 base atlas is an unconditional complex smooth
manifold. -/
theorem inverseEtaBase_isManifold :
    letI : ChartedSpace ℍ InverseEtaBase := inverseEtaBaseChartedSpaceH
    letI : HasGroupoid InverseEtaBase
        QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid :=
      inverseEtaBase_hasUpperHalfPlaneGroupoid
    letI : ChartedSpace ℂ InverseEtaBase := ChartedSpace.comp ℂ ℍ InverseEtaBase
    IsManifold 𝓘(ℂ) ∞ InverseEtaBase := by
  letI : ChartedSpace ℍ InverseEtaBase := inverseEtaBaseChartedSpaceH
  letI : HasGroupoid InverseEtaBase
      QYM.FullCertification.P2SmoothQuotientAtlasExtension.upperHalfPlaneSmoothGroupoid :=
    inverseEtaBase_hasUpperHalfPlaneGroupoid
  letI : ChartedSpace ℂ InverseEtaBase := ChartedSpace.comp ℂ ℍ InverseEtaBase
  letI : HasGroupoid InverseEtaBase (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    inverseEtaBase_hasGroupoid
  exact IsManifold.mk' 𝓘(ℂ) ∞ InverseEtaBase

'''

def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit('usage: qym_patch_gb27_atlas.py INPUT OUTPUT')
    src = Path(sys.argv[1])
    out = Path(sys.argv[2])
    raw = src.read_bytes()
    got = hashlib.sha256(raw).hexdigest()
    if got != BASE_SHA256:
        raise SystemExit(f'wrong input sha256: {got}')
    text = raw.decode()
    if text.count(START) != 1 or text.count(END) != 1:
        raise SystemExit('atlas boundary markers are not unique')
    a = text.index(START)
    b = text.index(END)
    if not a < b:
        raise SystemExit('atlas markers reversed')
    text = text[:a] + REPLACEMENT + text[b:]
    out.write_text(text)
    result = hashlib.sha256(out.read_bytes()).hexdigest()
    if result != EXPECTED_SHA256:
        raise SystemExit(f'unexpected output sha256: {result}')
    print('sha256=' + result)

if __name__ == '__main__':
    main()
