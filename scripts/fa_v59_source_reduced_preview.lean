/-
V58 idx4198 staged body-only preview.

This is intentionally not a standalone Lean file.  The exact `by ...` term
below is the proposed replacement for the body of
`gammaTwoReducedChart_pairwise_disjoint_translates` in the locked core_base
candidate.  It changes no declaration header, introduces no public helper,
and performs no source-order move.  It has only static evidence; direct Lean
verification of the composed full candidate is mandatory before promotion.
-/

by
  rw [pairwise_disjoint_smul_iff]
  intro a ha
  have hStabilizer :
      ∀ {g : SL(2, ℤ)}, g ∈ CongruenceSubgroup.Gamma 2 →
        ∀ {z : ℍ}, z ∈ ModularGroup.fd → g • z = z →
          g = 1 ∨ g = -1 := by
    intro g hgΓ z hz hgz
    have hcases := ModularGroup.cases_of_mem_fd_smul_mem_fd
      (g := g) hz (hgz.symm ▸ hz)
    rcases hcases with hpm | hT | hTinv | hS | hTS | hTinvSTinv |
        hSTinv | hST | hTST | hTinvS
    · exact hpm
    · rcases hT.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hTinv.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hS.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hTS.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hTinvSTinv.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hSTinv.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hST.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hTST.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
    · rcases hTinvS.1 with rfl | rfl <;>
        rw [CongruenceSubgroup.Gamma_mem] at hgΓ <;>
        norm_num [Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
          Matrix.mul_fin_two] at hgΓ
  have hRawCentral :
      ∀ (gamma : GammaTwo) {z : ℍ},
        ((gamma : SL(2, ℤ)) • z) = z →
          gamma = 1 ∨
            gamma =
              FixedPhaseEssentialCoreRoute.gammaTwoCentralNegOne := by
    intro gamma z hfix
    obtain ⟨delta, hdelta⟩ := ModularGroup.exists_smul_mem_fd z
    let w : ℍ := delta • z
    let conjugate : SL(2, ℤ) :=
      delta * (gamma : SL(2, ℤ)) * delta⁻¹
    have hConjugateMem : conjugate ∈ CongruenceSubgroup.Gamma 2 := by
      exact (CongruenceSubgroup.Gamma_normal 2).conj_mem
        (gamma : SL(2, ℤ)) gamma.property delta
    have hConjugateFix : conjugate • w = w := by
      dsimp only [conjugate, w]
      simp only [mul_smul, inv_smul_smul, hfix]
    have hCentral : conjugate = 1 ∨ conjugate = -1 :=
      hStabilizer hConjugateMem hdelta hConjugateFix
    rcases hCentral with hOne | hNeg
    · left
      apply Subtype.ext
      have h := congrArg
        (fun b : SL(2, ℤ) ↦ delta⁻¹ * b * delta) hOne
      simpa [conjugate, mul_assoc] using h
    · right
      apply Subtype.ext
      have h := congrArg
        (fun b : SL(2, ℤ) ↦ delta⁻¹ * b * delta) hNeg
      simpa [conjugate,
        FixedPhaseEssentialCoreRoute.gammaTwoCentralNegOne_coe,
        mul_assoc] using h
  have hEffectiveFree :
      ∀ (b : GammaTwoEffective) (z : ℍ), b • z = z → b = 1 := by
    intro b z hb
    obtain ⟨gamma, hgamma⟩ := effective_exists_gamma b
    have hfix : ((gamma : SL(2, ℤ)) • z) = z := by
      change gamma • z = z
      exact (hgamma z).symm.trans hb
    have hcentral := hRawCentral gamma hfix
    apply Subtype.ext
    apply Equiv.ext
    intro w
    change b • w = (1 : GammaTwoEffective) • w
    rw [hgamma w]
    rcases hcentral with rfl | rfl
    · simp only [one_smul]
    · change
        ((FixedPhaseEssentialCoreRoute.gammaTwoCentralNegOne : GammaTwo) :
            SL(2, ℤ)) • w = w
      exact FixedPhaseEssentialCoreRoute.gammaTwoCentralNegOne_smul w
  apply hEffectiveFree a z₀
  apply gammaTwoReducedChart_inter_translate_imp_smul_eq z₀ a
  simpa only [image_smul] using ha
