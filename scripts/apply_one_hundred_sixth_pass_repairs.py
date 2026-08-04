from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fifth_pass_repairs as pass105
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """    norm_num [AdvancedClaimsIIPaperI2PrecisionTube,
""",
            """    norm_num [Fin.sum_univ_succ, Finset.sum_range_succ,
      AdvancedClaimsIIPaperI2PrecisionTube,
""", 1,
            "Mock1Advanced expand finite sums in precision-tube arithmetic",
        ),
        (
            """    norm_num [AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifferenceResidue,
""",
            """    norm_num [Finset.sum_range_succ,
      AdvancedClaimsIIPaperI2MahlerCoefficient,
      AdvancedClaimsIIPaperI2ForwardDifferenceResidue,
""", 1,
            "Mock1Advanced expand finite ranges in residue arithmetic",
        ),
        (
            """    norm_num [FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime, AdvancedClaimsIIPaperI2Precision,
""",
            """    norm_num [Finset.sum_range_succ,
      FiniteCongruenceMod, IntCongruent, PrimePower,
      AdvancedClaimsIIPaperI2Prime, AdvancedClaimsIIPaperI2Precision,
""", 1,
            "Mock1Advanced expand finite ranges in congruence arithmetic",
        ),
        (
            """  rw [advanced_claims_ii_signed_pair_norm_decomposition a b target h]
  positivity
""",
            """  rw [advanced_claims_ii_signed_pair_norm_decomposition a b target h]
  have hsq : 0 <= (a + b) ^ 2 := sq_nonneg (a + b)
  linarith
""", 1,
            "Mock1Advanced derive the norm bound from square nonnegativity",
        ),
        (
            """  rw [advanced_claims_ii_appell_lerch_ridge_total_exponent]
  positivity
""",
            """  rw [advanced_claims_ii_appell_lerch_ridge_total_exponent]
  have hm : (0 : Rat) <= (m : Rat) := by positivity
  have hsq : (0 : Rat) <= (m : Rat) ^ 2 := sq_nonneg (m : Rat)
  nlinarith
""", 1,
            "Mock1Advanced prove ridge exponent negativity arithmetically",
        ),
        (
            """  rcases hblock with hblock | hblock | hblock
  · subst block
    simp [referenceMock1MList, referenceMock1RPhases]
  · subst block
    simp [referenceMock1MList, referenceMock1RPhases]
  · subst block
    simp [referenceMock1MList, referenceMock1RPhases]
""",
            """  rcases hblock with rfl | rfl | rfl <;>
    simp [referenceMock1MList, referenceMock1RPhases]
""", 1,
            "Mock1Advanced eliminate weighted-block membership cases",
        ),
        (
            """  rcases hterm with hterm | hterm | hterm
  · subst term
    norm_num
  · subst term
    norm_num
  · subst term
    norm_num
""",
            """  rcases hterm with rfl | rfl | rfl <;> norm_num
""", 1,
            "Mock1Advanced eliminate declared-principal-term cases",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """theorem gammaLower_mem_Gamma2 : gammaLower ∈ Gamma2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gammaLower]
""",
            """theorem gammaLower_mem_Gamma2 : gammaLower ∈ Gamma2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  change (1 : ZMod 2) = 1 /\\
    (0 : ZMod 2) = 0 /\\
    (2 : ZMod 2) = 0 /\\
    (1 : ZMod 2) = 1
  decide
""", 1,
            "Mock2 discharge the four Gamma2 entry congruences directly",
        ),
        (
            """  rw [ModularGroup.im_smul_eq_div_normSq]
  change (1 : ℝ) / Complex.normSq (2 * Complex.I + 1) = 1 / 5
  norm_num [Complex.normSq]
""",
            """  rw [ModularGroup.im_smul_eq_div_normSq]
  have hdenom :
      UpperHalfPlane.denom
          (SpecialLinearGroup.toGL
            ((SpecialLinearGroup.map (Int.castRingHom ℝ)) gammaLower))
          Complex.I = 2 * Complex.I + 1 := by
    ext <;> norm_num [UpperHalfPlane.denom, gammaLower]
  rw [hdenom, UpperHalfPlane.I_im]
  norm_num [Complex.normSq]
""", 1,
            "Mock2 compute the cast lower-unipotent denominator before normSq",
        ),
        (
            """    (presheaf F).res hUV s x = s ⟨x.1, hUV x.2⟩ :=
""",
            """    ((presheaf F).res hUV s).toFun x =
      s.toFun ⟨x.1, hUV x.2⟩ :=
""", 1,
            "Mock2 project restriction values through toFun",
        ),
        (
            """  s (coverIndex C x) ⟨x.1, coverIndex_mem C x⟩
""",
            """  (s (coverIndex C x)).toFun ⟨x.1, coverIndex_mem C x⟩
""", 1,
            "Mock2 evaluate selected chart through toFun",
        ),
        (
            """    glueFunction C s x = s i ⟨x.1, hxi⟩ := by
""",
            """    glueFunction C s x = (s i).toFun ⟨x.1, hxi⟩ := by
""", 1,
            "Mock2 state chart independence through toFun",
        ),
        (
            """  have heq := congrArg
    (fun f : LocallyConstant (C.piece j ⊓ C.piece i) F => f z)
    (hs j i)
""",
            """  have heq := congrArg (fun f => f.toFun z) (hs j i)
""", 1,
            "Mock2 compare overlap values through inferred toFun",
        ),
        (
            """    let A : Set (C.piece i) := (s i : C.piece i → F) ⁻¹' {s i xi}
""",
            """    let A : Set (C.piece i) := (s i).toFun ⁻¹' {(s i).toFun xi}
""", 1,
            "Mock2 define local fibre through toFun",
        ),
        (
            """    have hz_value : s i z = s i xi := by
""",
            """    have hz_value : (s i).toFun z = (s i).toFun xi := by
""", 1,
            "Mock2 record local fibre equality through toFun",
        ),
        (
            """      glueFunction C s y = s i ⟨y.1, hyi⟩ :=
        glueFunction_eq_section C s hs i y hyi
      _ = s i z := by rw [← hz_eq]
      _ = s i xi := hz_value
""",
            """      glueFunction C s y = (s i).toFun ⟨y.1, hyi⟩ :=
        glueFunction_eq_section C s hs i y hyi
      _ = (s i).toFun z := by rw [← hz_eq]
      _ = (s i).toFun xi := hz_value
""", 1,
            "Mock2 calculate glued values through toFun",
        ),
        (
            """  have heq := congrArg (fun f : LocallyConstant (C.piece i) F => f zi) (hxy i)
""",
            """  have heq := congrArg (fun f => f.toFun zi) (hxy i)
""", 1,
            "Mock2 compare restrictions through inferred toFun",
        ),
        (
            """      (⟨x.1, C.piece_le_target i x.2⟩ : C.target) = s i x
""",
            """      (⟨x.1, C.piece_le_target i x.2⟩ : C.target) = (s i).toFun x
""", 1,
            "Mock2 state gluing through toFun",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  simpa [Function.comp_apply, hzero] using
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
""",
            """  convert
    (hcontinuous.tendsto (0 : ℂ)).comp
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
    using 1 <;> simp [Function.comp_def, hzero]
""", 1,
            "Mock2Advanced normalize reciprocal-Gamma composition extensionally",
        ),
        (
            """    simpa [Function.comp_apply] using
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
""",
            """    convert
      ((Real.continuous_const_rpow hbase).comp continuous_neg).tendsto 0
      using 1 <;> simp [Function.comp_def]
""", 1,
            "Mock2Advanced normalize negative-exponent composition extensionally",
        ),
        (
            """  by_cases hx : x ≤ 0
  · apply congrArg (fun y : ℝ => max 0 y)
    calc
      min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2) =
          (x + T / 2) - (-T / 2) := by
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      _ = T - |x| := by
        rw [abs_of_nonpos hx]
        ring
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    apply congrArg (fun y : ℝ => max 0 y)
    calc
      min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2) =
          T / 2 - (x - T / 2) := by
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      _ = T - |x| := by
        rw [abs_of_nonneg hx0]
        ring
""",
            """  by_cases hx : x ≤ 0
  · calc
      max (min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2)) 0 =
          max 0 (min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2)) :=
        max_comm _ _
      _ = max 0 (T - |x|) := congrArg (fun y : ℝ => max 0 y) (by
        rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos hx]
        ring)
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    calc
      max (min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2)) 0 =
          max 0 (min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2)) :=
        max_comm _ _
      _ = max 0 (T - |x|) := congrArg (fun y : ℝ => max 0 y) (by
        rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg hx0]
        ring)
""", 1,
            "Mock2Advanced align max arguments in overlap-volume proof",
        ),
        (
            """theorem continuous_profile (T : ℝ) : Continuous (profile T) := by
  simpa [profile] using
    continuous_const.max (continuous_const.sub continuous_abs)
""",
            """theorem continuous_profile (T : ℝ) : Continuous (profile T) := by
  change Continuous (fun t : ℝ => max 0 (T - |t|))
  exact continuous_const.max (continuous_const.sub continuous_abs)
""", 1,
            "Mock2Advanced expose profile before continuity",
        ),
        (
            """  rw [hasCompactSupport_def, tsupport_profile hT]
  exact isCompact_Icc
""",
            """  change IsCompact (tsupport (profile T))
  rw [tsupport_profile hT]
  exact isCompact_Icc
""", 1,
            "Mock2Advanced expose tsupport before compactness",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """      (fun γ : SL(2, ℤ) =>
        ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) from by
""",
            """      (fun γ : SL(2, ℤ) =>
        ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1),
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1))) from by
""", 1,
            "FunctionalAnalysis encode SL2Z by two entry pairs",
        ),
        (
            """  ext q
  induction q using Quotient.inductionOn'
  constructor
  · intro hz
    refine ⟨_, ?_, rfl⟩
    simpa only [Function.mem_support, descendInvariant_mk] using hz
""",
            """  ext q
  refine Quotient.inductionOn' q ?_
  intro z
  constructor
  · intro hz
    refine ⟨z, ?_, rfl⟩
    change descendInvariant ρ hρ (gammaTwoQuotientMk z) ≠ 0 at hz
    simpa only [Function.mem_support, descendInvariant_mk] using hz
""", 1,
            "FunctionalAnalysis retain representative in support proof",
        ),
        (
            """    Measurable (descendInvariant ρ hρ) :=
  measurable_from_quotient.mpr (by
    simpa [Function.comp_def] using hρm)
""",
            """    Measurable (descendInvariant ρ hρ) := by
  rw [measurable_from_quotient]
  change Measurable (fun z => descendInvariant ρ hρ (gammaTwoQuotientMk z))
  simpa only [descendInvariant_mk] using hρm
""", 1,
            "FunctionalAnalysis expose quotient lift in measurability proof",
        ),
    ])


def main() -> int:
    pass105.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
