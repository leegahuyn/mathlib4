lemma qym_tinv01 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 1)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two, qym_tinv00] at h
  exact h

lemma qym_tinv10 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 0 = (0 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 1 0)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two] at h
  exact h

lemma qym_tinv11 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 1 = (1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 1 1)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two, qym_tinv10] at h
  exact h

lemma qym_upper_pair_not_mem_gammaTwo
    {g : SL(2, ℤ)}
    (hentry : g 0 1 = (1 : ℤ) ∨ g 0 1 = (-1 : ℤ)) :
    g ∉ CongruenceSubgroup.Gamma 2 ∧
      -g ∉ CongruenceSubgroup.Gamma 2 := by
  constructor
  · intro hg
    have hUpper := (CongruenceSubgroup.Gamma_mem.mp hg).2.1
    rcases hentry with h | h
    · rw [h] at hUpper
      norm_num at hUpper
    · rw [h] at hUpper
      norm_num at hUpper
  · intro hg
    have hUpper := (CongruenceSubgroup.Gamma_mem.mp hg).2.1
    rcases hentry with h | h
    · have hn : (-g : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
        simp [h]
      rw [hn] at hUpper
      norm_num at hUpper
    · have hn : (-g : SL(2, ℤ)) 0 1 = (1 : ℤ) := by
        simp [h]
      rw [hn] at hUpper
      norm_num at hUpper

lemma qym_lower_pair_not_mem_gammaTwo
    {g : SL(2, ℤ)}
    (hentry : g 1 0 = (1 : ℤ) ∨ g 1 0 = (-1 : ℤ)) :
    g ∉ CongruenceSubgroup.Gamma 2 ∧
      -g ∉ CongruenceSubgroup.Gamma 2 := by
  constructor
  · intro hg
    have hLower := (CongruenceSubgroup.Gamma_mem.mp hg).2.2.1
    rcases hentry with h | h
    · rw [h] at hLower
      norm_num at hLower
    · rw [h] at hLower
      norm_num at hLower
  · intro hg
    have hLower := (CongruenceSubgroup.Gamma_mem.mp hg).2.2.1
    rcases hentry with h | h
    · have hn : (-g : SL(2, ℤ)) 1 0 = (-1 : ℤ) := by
        simp [h]
      rw [hn] at hLower
      norm_num at hLower
    · have hn : (-g : SL(2, ℤ)) 1 0 = (1 : ℤ) := by
        simp [h]
      rw [hn] at hLower
      norm_num at hLower

lemma qym_TS_upper_entry :
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    (∑ k : Fin 2, ModularGroup.T.val 0 k * ModularGroup.S.val k 1) = -1
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.T, ModularGroup.S]

lemma qym_tinvS_lower_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T⁻¹).val 1 k * ModularGroup.S.val k 0) = 1
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.S, qym_tinv10, qym_tinv11]

lemma qym_tinvS_11_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T⁻¹).val 1 k * ModularGroup.S.val k 1) = 0
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.S, qym_tinv10, qym_tinv11]

lemma qym_tinvSTinv_lower_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ : SL(2, ℤ)) 1 0 =
      (1 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T⁻¹ * ModularGroup.S).val 1 k *
        (ModularGroup.T⁻¹).val k 0) = 1
  simp only [Fin.sum_univ_two]
  norm_num [qym_tinvS_lower_entry, qym_tinvS_11_entry,
    qym_tinv00, qym_tinv10]

lemma qym_STinv_upper_entry :
    (ModularGroup.S * ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    (∑ k : Fin 2,
      ModularGroup.S.val 0 k * (ModularGroup.T⁻¹).val k 1) = -1
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.S, qym_tinv01, qym_tinv11]

lemma qym_ST_upper_entry :
    (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    (∑ k : Fin 2, ModularGroup.S.val 0 k * ModularGroup.T.val k 1) = -1
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.T, ModularGroup.S]

lemma qym_TS_lower_entry :
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by
  change
    (∑ k : Fin 2, ModularGroup.T.val 1 k * ModularGroup.S.val k 0) = 1
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.T, ModularGroup.S]

lemma qym_TS_11_entry :
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by
  change
    (∑ k : Fin 2, ModularGroup.T.val 1 k * ModularGroup.S.val k 1) = 0
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.T, ModularGroup.S]

lemma qym_TST_lower_entry :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 =
      (1 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T * ModularGroup.S).val 1 k * ModularGroup.T.val k 0) = 1
  simp only [Fin.sum_univ_two]
  norm_num [qym_TS_lower_entry, qym_TS_11_entry, ModularGroup.T]

theorem qym_gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
  have hTbad :
      ModularGroup.T ∉ CongruenceSubgroup.Gamma 2 ∧
        -ModularGroup.T ∉ CongruenceSubgroup.Gamma 2 :=
    qym_upper_pair_not_mem_gammaTwo (Or.inl (by norm_num [ModularGroup.T]))
  have hTinvbad :
      ModularGroup.T⁻¹ ∉ CongruenceSubgroup.Gamma 2 ∧
        -ModularGroup.T⁻¹ ∉ CongruenceSubgroup.Gamma 2 :=
    qym_upper_pair_not_mem_gammaTwo (Or.inr qym_tinv01)
  have hSbad :
      ModularGroup.S ∉ CongruenceSubgroup.Gamma 2 ∧
        -ModularGroup.S ∉ CongruenceSubgroup.Gamma 2 :=
    qym_upper_pair_not_mem_gammaTwo (Or.inr (by norm_num [ModularGroup.S]))
  have hTSbad :
      ModularGroup.T * ModularGroup.S ∉ CongruenceSubgroup.Gamma 2 ∧
        -(ModularGroup.T * ModularGroup.S) ∉ CongruenceSubgroup.Gamma 2 :=
    qym_upper_pair_not_mem_gammaTwo (Or.inr qym_TS_upper_entry)
  have hTinvSTinvbad :
      ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ ∉
          CongruenceSubgroup.Gamma 2 ∧
        -(ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹) ∉
          CongruenceSubgroup.Gamma 2 :=
    qym_lower_pair_not_mem_gammaTwo (Or.inl qym_tinvSTinv_lower_entry)
  have hSTinvbad :
      ModularGroup.S * ModularGroup.T⁻¹ ∉ CongruenceSubgroup.Gamma 2 ∧
        -(ModularGroup.S * ModularGroup.T⁻¹) ∉ CongruenceSubgroup.Gamma 2 :=
    qym_upper_pair_not_mem_gammaTwo (Or.inr qym_STinv_upper_entry)
  have hSTbad :
      ModularGroup.S * ModularGroup.T ∉ CongruenceSubgroup.Gamma 2 ∧
        -(ModularGroup.S * ModularGroup.T) ∉ CongruenceSubgroup.Gamma 2 :=
    qym_upper_pair_not_mem_gammaTwo (Or.inr qym_ST_upper_entry)
  have hTSTbad :
      ModularGroup.T * ModularGroup.S * ModularGroup.T ∉
          CongruenceSubgroup.Gamma 2 ∧
        -(ModularGroup.T * ModularGroup.S * ModularGroup.T) ∉
          CongruenceSubgroup.Gamma 2 :=
    qym_lower_pair_not_mem_gammaTwo (Or.inl qym_TST_lower_entry)
  have eliminate
      {g : SL(2, ℤ)}
      (hbad : g ∉ CongruenceSubgroup.Gamma 2 ∧
        -g ∉ CongruenceSubgroup.Gamma 2)
      (heq : gamma = g ∨ gamma = -g) : False := by
    rcases heq with h | h
    · subst gamma
      exact hbad.1 hGamma
    · subst gamma
      exact hbad.2 hGamma
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvSCase
  · exact hcentral
  · exact (eliminate hTbad hT.1).elim
  · exact (eliminate hTinvbad hTinv.1).elim
  · exact (eliminate hSbad hS.1).elim
  · exact (eliminate hTSbad hTS.1).elim
  · exact (eliminate hTinvSTinvbad hTinvSTinv.1).elim
  · exact (eliminate hSTinvbad hSTinv.1).elim
  · exact (eliminate hSTbad hST.1).elim
  · exact (eliminate hTSTbad hTST.1).elim
  · rcases hTinvSCase.1 with hpos | hneg
    · subst gamma
      exact (qym_tinvS_not_mem_gammaTwo hGamma).elim
    · subst gamma
      exact (qym_neg_tinvS_not_mem_gammaTwo hGamma).elim
