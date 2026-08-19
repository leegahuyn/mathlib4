import PrimalitySheafVerification.Mock2_FunctionalAnalysis

open scoped MatrixGroups UpperHalfPlane

namespace QYM.FullCertification.P3GammaTwoQuotientBridgeExtension

abbrev H := ℍ
abbrev GammaTwo := CongruenceSubgroup.Gamma 2
abbrev OriginalGammaTwoQuotient := Mock2.Definition15Geometry.X
abbrev EffectiveGammaTwoQuotient :=
  Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient
abbrev GammaTwoEffective :=
  Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoEffective

namespace Effective

open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

end Effective

/-- The identity on the upper half-plane descends from the original
`Gamma(2)` quotient to the faithful/effective quotient. -/
noncomputable def originalToEffective :
    OriginalGammaTwoQuotient → EffectiveGammaTwoQuotient :=
  Quotient.lift
    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk
    (by
      intro z w hzw
      change z ∈ MulAction.orbit GammaTwo w at hzw
      rcases hzw with ⟨gamma, rfl⟩
      exact
        Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk_gamma_smul
          gamma w)

/-- The identity on the upper half-plane also descends in the reverse
direction because every effective element has a `Gamma(2)` representative. -/
noncomputable def effectiveToOriginal :
    EffectiveGammaTwoQuotient → OriginalGammaTwoQuotient :=
  Quotient.lift Mock2.Definition15Geometry.quotientMap
    (by
      intro z w hzw
      change z ∈ MulAction.orbit GammaTwoEffective w at hzw
      rcases hzw with ⟨g, rfl⟩
      rcases
          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.effective_exists_gamma g
        with ⟨gamma, hgamma⟩
      rw [hgamma w]
      exact Mock2.Definition15Geometry.quotientMap_smul gamma w)

@[simp]
theorem originalToEffective_quotientMap (z : H) :
    originalToEffective (Mock2.Definition15Geometry.quotientMap z) =
      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk z :=
  rfl

@[simp]
theorem effectiveToOriginal_quotientMk (z : H) :
    effectiveToOriginal
        (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk z) =
      Mock2.Definition15Geometry.quotientMap z :=
  rfl

/-- The two quotient presentations are canonically equivalent because they
have exactly the same orbits. -/
noncomputable def originalEffectiveEquiv :
    OriginalGammaTwoQuotient ≃ EffectiveGammaTwoQuotient where
  toFun := originalToEffective
  invFun := effectiveToOriginal
  left_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro z
    rfl
  right_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro z
    rfl

/-- Continuity of the forward quotient bridge follows from the quotient
universal property and continuity of the effective orbit projection. -/
theorem originalToEffective_continuous :
    Continuous originalToEffective := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous
    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk
  exact
    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk_isOpenQuotientMap.continuous

/-- Continuity of the reverse quotient bridge follows from the effective
open-quotient universal property. -/
theorem effectiveToOriginal_continuous :
    Continuous effectiveToOriginal := by
  apply
    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  change Continuous Mock2.Definition15Geometry.quotientMap
  exact Mock2.Definition15Geometry.quotientMapContinuous.continuous

/-- Canonical homeomorphism between the original and effective quotient
presentations. -/
noncomputable def originalEffectiveHomeomorph :
    OriginalGammaTwoQuotient ≃ₜ EffectiveGammaTwoQuotient where
  toEquiv := originalEffectiveEquiv
  continuous_toFun := originalToEffective_continuous
  continuous_invFun := effectiveToOriginal_continuous

@[simp]
theorem originalEffectiveHomeomorph_apply_quotientMap (z : H) :
    originalEffectiveHomeomorph
        (Mock2.Definition15Geometry.quotientMap z) =
      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk z :=
  rfl

@[simp]
theorem originalEffectiveHomeomorph_symm_apply_quotientMk (z : H) :
    originalEffectiveHomeomorph.symm
        (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoQuotientMk z) =
      Mock2.Definition15Geometry.quotientMap z :=
  rfl

end QYM.FullCertification.P3GammaTwoQuotientBridgeExtension
