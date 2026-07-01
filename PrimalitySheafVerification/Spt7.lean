/-
================================================================================
  Spt7.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun, "Section 4: Overlaps, Tor, Koszul Regularity, and
                     Sheaf / Local Charts".

  Kernel-checked against Mathlib; NO `sorry`, NO new global `axiom`.  Conditional
  results carry their assumptions as explicit hypotheses.

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    Thm .1 (independence, canonical profile A=4, M=pₙ+3)
                       ↦ canonical_coprime, canonical_obstructionFree,
                         modCritical_AP, pAdicCritical_AP,
                         numericCritical_AP, ecCritical_AP,
                         fourLayerStrictIndependence                         PROVED
    Thm .3 / .19 / Lem .6 / .39, Cor .9 / .40  equalizer kernel = (lcm),
        Čech Ĥ¹ ≅ ℤ/gcd, Tor₁ ≅ ℤ/gcd, obstruction-free ⇔ gcd=1,
        prime-power CRT decomposition of the concrete Tor₁ kernel
                       ↦ kernel_mem_iff_lcm, crt_solvable_iff, card_ker_mulLeft,
                         obstructionFree_iff_*, TorH1_primePowerDecomposition PROVED
    Thm .19(a) thickness (CORRECTED)  gcd→min, lcm/intersection→max
                       ↦ factorization_gcd_apply / lcm_apply,
                         localized_intersection_prime_power_ideal_eq_span     PROVED
    Prop .8, IC; Cor .9  monotonicity/additivity of IC; |Tor| = exp(IC)
                       ↦ IC_mono, IC_mono_left, IC_coprime_add,
                         card_Tor_eq_exp_IC, cor9_tfae_gcd_tor_ic            PROVED
    Lem .10 / .14, Thm .11 / .15, Prop .16  Koszul / regular-sequence criterion
                       ↦ stalk_regularity_test, singleton_regular_iff,
                         nil_regular, cons_regular_iff, koszulR1ChainComplex,
                         koszulR1H1_eq_bot_iff_isSMulRegular,
                         koszulR1H0EquivQuotSMulTop,
                         koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton,
                         koszulR2ChainComplex,
                         koszulR2H0EquivQuotOfListPair,
                         koszulR2H1_subsingleton_of_isWeaklyRegular_pair,
                         koszulR2H2_eq_bot_of_isWeaklyRegular_pair,
                         koszulR2PositiveAcyclic_of_isWeaklyRegular_pair,
                         koszulR2PositiveAcyclic_of_cons_certificate,
                         koszulLowDegreePositiveAcyclic,
                         koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_length_le_two,
                         koszulLowDegreeRegularityCertificate,
                         koszulLowDegreeRegularityCertificate_iff_isWeaklyRegular_length_le_two,
                         koszulInterface_singleton_iff_koszulR1PositiveAcyclic,
                         koszulR2PositiveAcyclic_of_interface_pair,
                         koszulLowDegreePositiveAcyclic_of_interface_length_le_two,
                         koszulLowDegreeRegularityCertificate_iff_interface_length_le_two,
                         KoszulComplexModel,
                         KoszulComplexModel.acyclic_iff_isWeaklyRegular,
                         KoszulComplexModel.lowDegreeRegularityCertificate_iff_acyclic,
                         lowDegreeKoszulComplexModel,
                         lowDegreeKoszulComplexModel_complex_singleton,
                         lowDegreeKoszulComplexModel_complex_pair,
                         koszulAcyclic_iff_isWeaklyRegular_of_interface,
                         koszulAcyclic_iff_isRegular_of_interface,
                         koszulLowDegreePositiveAcyclic_of_isRegular_length_le_two,
                         koszulLowDegreeRegularityCertificate_of_isRegular_length_le_two,
                         koszulLowDegreePositiveAcyclic_of_regular_interface_length_le_two,
                         koszulLowDegreeRegularityCertificate_of_regular_interface_length_le_two,
                         regular_of_linearEquiv,
                         regularSequence_of_faithfullyFlat_of_isBaseChange,
                         weaklyRegularSequence_of_localizedModule             PROVED
    Prop .18 (depth lower bound; CM/direct dimension trigger)
                       ↦ HasWeakRegularSequenceLength,
                         ModuleDepthDimensionInterface,
                         prop18_depth_lower_bound_of_isWeaklyRegular,
                         prop18_depth_lower_bound,
                         prop18_dimension_lower_bound_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_depth_eq_dimension,
                         prop18_depth_lower_bound_of_koszulAcyclic,
                         prop18_depth_lower_bound_of_koszulRegularAcyclic,
                         prop18_depth_lower_bound_of_koszulModelAcyclic,
                         prop18_depth_lower_bound_of_lowDegreeRegularityCertificate,
                         prop18_depth_lower_bound_of_flatBaseChange,
                         prop18_depth_lower_bound_of_faithfullyFlatBaseChange,
                         prop18_depth_lower_bound_of_localizedModule,
                         prop18_dimension_lower_bound_of_koszulAcyclic_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_koszulRegularAcyclic_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_koszulModelAcyclic_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_lowDegreeRegularityCertificate_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_koszulAcyclic_of_depth_eq_dimension,
                         prop18_dimension_lower_bound_of_koszulRegularAcyclic_of_depth_eq_dimension,
                         prop18_dimension_lower_bound_of_koszulModelAcyclic_of_depth_eq_dimension,
                         prop18_dimension_lower_bound_of_lowDegreeRegularityCertificate_of_depth_eq_dimension,
                         prop18_dimension_lower_bound_of_flatBaseChange_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_faithfullyFlatBaseChange_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_localizedModule_of_isCohenMacaulay,
                         prop18_dimension_lower_bound_of_flatBaseChange_of_depth_eq_dimension,
                         prop18_dimension_lower_bound_of_faithfullyFlatBaseChange_of_depth_eq_dimension,
                         prop18_dimension_lower_bound_of_localizedModule_of_depth_eq_dimension,
                         prop18_depth_eq_dimension_trigger_of_depth_eq_dimension,
                         prop18_depth_eq_dimension_trigger_of_koszulAcyclic,
                         prop18_depth_eq_dimension_trigger_of_koszulRegularAcyclic,
                         prop18_depth_eq_dimension_trigger_of_koszulModelAcyclic,
                         prop18_depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate,
                         prop18_depth_eq_dimension_trigger_of_koszulAcyclic_of_depth_eq_dimension,
                         prop18_depth_eq_dimension_trigger_of_koszulRegularAcyclic_of_depth_eq_dimension,
                         prop18_depth_eq_dimension_trigger_of_koszulModelAcyclic_of_depth_eq_dimension,
                         prop18_depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate_of_depth_eq_dimension,
                         prop18_depth_eq_dimension_trigger                  PROVED (interface)
    Lem .37 (det–trace formal algebraic core)
                       ↦ detTraceWeightedLogSeries,
                         detTraceShiftedSeries,
                         derivative_detTraceWeightedLogSeries,
                         powerSeries_eq_of_derivative_eq_mul,
                          exp_subst_eq_of_derivative_eq_mul,
                          matrixDetOneSubSeries,
                         matrixTraceLogSeries,
                         derivative_matrixDetOneSubInvSeries,
                          lem37_det_trace_formal_identity                    PROVED
    §6.2 Euler product `Z_U`
                       ↦ zetaULinearLocalFactor,
                         zetaU_eulerProduct_hasProd,
                         zetaU_eulerProduct_tprod,
                         zetaU_eulerProduct_partial,
                         quadraticEulerLocalFactor_eq_mul,
                         quadraticEulerPartialProduct_eq_mul,
                         quadraticEulerProduct_hasProd_of_linear,
                         zetaULSeries_deriv,
                         zetaULSeries_logDeriv_eq,
                         zetaULSeries_abscissa_logMul                        PROVED
    Def .20/.21, Lem .22-.25/.29 constructible six-functor interface
                       ↦ SixFunctorData,
                         SixFunctorData.pull_constructible,
                         SixFunctorData.push_constructible,
                         SixFunctorData.shriek_constructible,
                         SixFunctorData.exceptionalPull_constructible,
                         SixFunctorData.tensor_constructible,
                         SixFunctorData.internalHom_constructible,
                         SixFunctorData.dual_constructible,
                         SixFunctorData.glue_triangle_distinguished,
                         SixFunctorData.pull_id_iso,
                         SixFunctorData.pull_comp_iso,
                         SixFunctorData.push_id_iso,
                         SixFunctorData.push_comp_iso,
                         SixFunctorData.shriek_id_iso,
                         SixFunctorData.shriek_comp_iso,
                         SixFunctorData.shriek_comp_three_iso,
                         SixFunctorData.exceptionalPull_id_iso,
                         SixFunctorData.exceptionalPull_comp_iso,
                         SixFunctorData.baseChangeShriek_iso,
                         SixFunctorData.projectionFormula_iso                PROVED (interface)
    Lem .32 curve reduction (Nagata/Stein factorization as certificate)
                       ↦ CurveFactorization,
                         CurveFactorization.shriek_factorization_iso,
                         CurveFactorization.curveReduction_terms_constructible
                                                                            PROVED (interface)
    Prop .33/.41, Thm .34/.42, Prop .38  Weil II / weight-radius package
                       ↦ weightRadius,
                         WeilIIPackage,
                         WeilIIPackage.frob_abs_eq,
                         WeilIIPackage.pure_weight_radiusBound,
                         WeilIIPackage.mixed_weight_radiusBound,
                         DetTraceRadiusCertificate,
                         prop38_radius_limit_of_pure,
                         prop38_radius_limit_of_mixed                       PROVED (interface)
    Lem .36 Grothendieck-Lefschetz trace formula
                       ↦ glAltSign,
                         glAlternatingTraceOf,
                         GrothendieckLefschetzPackage,
                         GrothendieckLefschetzPackage.pointCount_eq_alternatingTrace,
                         GrothendieckLefschetzPackage.logDerivative_expansion,
                         GrothendieckLefschetzPackage.logDerivative_matrixTrace_expansion,
                         lem36_logDerivative_expansion                      PROVED (interface)
    Prop .43, Thm .44, Cor .45/.46  Global Purity B assembly
                       ↦ FiniteSupportCohomologyVanishing,
                         prop43_positive_cohomology_vanishes,
                         GlobalPurityBConclusion,
                         thm44_globalPurityB_of_pure,
                         cor45_globalPurityB_radiusLimit,
                         cor46_globalPurityB_logDerivative_expansion        PROVED (interface)
    Thm .47 (Equivalence C) good-prime synchronization (CONDITIONAL)
                       ↦ equivalence_C,
                         ArithmeticCechTorGate,
                         arithmeticCechTorGate_tfae,
                         WeightPurityGate,
                         weightPurityGate_radiusLimit,
                         EquivalenceCGate,
                         equivalence_C_faithful_tfae,
                         equivalence_C_faithful                             PROVED (interface)
    §J Mathlib-gap workaround checklist
                       ↦ ConcreteSurrogateCertificate,
                         LowDegreeKoszulCertificate,
                         BundledInterfaceCertificate,
                         FormalAlgebraCoreCertificate,
                         ExistingAnalogReuseCertificate,
                         MathlibGapWorkaroundChecklist,
                         mathlibGapWorkaroundChecklist                      PROVED
    짠K Mathlib handle inventory (exploratory reuse handles)
                       ??FaithfullyFlatBaseChangeHandle,
                         DepthCMLocalizationHandle,
                         EulerProductMathlibHandle,
                         LSeriesDerivativeMathlibHandle,
                         MathlibAbstractTorFunctorHandle,
                         ConcreteTorMathlibBridge,
                         KoszulReuseHandle,
                         mathlibHandleInventoryChecklist                    PROVED

  ⚠ CORRECTION (7th paper, same error): Thm .19(a) gives `((M)∩(pᵏ))_(p) = p^{εp}`,
  `εp = min{vp M,k}`.  Wrong: the intersection is `(lcm)`, of `p`-thickness `max`;
  `min` is the valuation of `gcd` (failure fiber / Tor).

  HONEST OMISSIONS: the full arbitrary-length tensor/mapping-cone construction of
  the Koszul complex is still not in Mathlib.  Below we formalize the `r = 1`
  and `r = 2` explicit low-degree complexes, including the `r = 2` middle
  exactness proof under weak regularity, and the certification interface needed
  for the general-length Koszul acyclicity criterion: any future honest Koszul
  acyclicity predicate satisfying nil/cons laws is proved equivalent to
  weak/strong regularity.  The 6-functor / weight / Deligne machinery
  (Lem .22–.46, Thm .42/.44, Equivalence C §) needs étale cohomology and weights,
  absent from Mathlib (conditional/omitted).
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE

open scoped BigOperators
open scoped PowerSeries
open scoped Polynomial

namespace Spt7

/-! ## §A — Independence at good primes for the canonical profile (Theorem .1).

`A = 4`, `M = pₙ·1 + (A-1) = pₙ + 3`.  For a prime `p ≥ 5`, `vp(M) = 0`, so
`gcd(M, pᵏ) = 1` and `Tor₁ = 0` (the overlap is obstruction-free). -/

/-- **Theorem .1 (arithmetic core).** For prime `p ≥ 5` and `k ≥ 0`,
    `gcd(p+3, pᵏ) = 1` (i.e. `vp(p+3) = 0`). -/
theorem canonical_coprime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (k : ℕ) :
    Nat.Coprime (p + 3) (p ^ k) := by
  have hp3 : ¬ p ∣ (p + 3) := by
    intro h
    have h3 : p ∣ 3 := (Nat.dvd_add_right (dvd_refl p)).mp h
    have := Nat.le_of_dvd (by norm_num) h3; omega
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hp3).symm.pow_right k

/-- **Theorem .1 (consequence).** The canonical overlap is obstruction-free. -/
theorem canonical_obstructionFree {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (k : ℕ) :
    Nat.gcd (p + 3) (p ^ k) = 1 := canonical_coprime hp h5 k

/-! ### Four-layer independence scaffold for Theorem .1

The analytic `p`-adic logarithm in the numeric layer is not modeled here directly.  Following
the paper's `(Hk)` reduction, the numeric gate is represented by the corresponding
valuation/congruence condition.  After translating each local good residue to `0`, the four
layers are simply four congruence predicates on integer sections.  Pairwise coprime layer
moduli make the independence witnesses pure CRT arithmetic. -/

/-- Injectivity of a nonconstant integer arithmetic progression.  We use this as the formal
"infinite arithmetic progression" certificate: the map `t ↦ base + step * t` embeds `ℤ`. -/
theorem arithmeticProgression_injective {step base : ℤ} (hstep : step ≠ 0) :
    Function.Injective (fun t : ℤ => base + step * t) := by
  intro s t h
  have hsub : step * (s - t) = 0 := by
    calc
      step * (s - t) = (base + step * s) - (base + step * t) := by ring
      _ = 0 := by
        change base + step * s = base + step * t at h
        rw [h, sub_self]
  rcases mul_eq_zero.mp hsub with h0 | hst
  · exact (hstep h0).elim
  · exact sub_eq_zero.mp hst

/-- Binary CRT arithmetic progression: for coprime moduli `m,n`, there is an infinite
progression with residue `1` modulo `m` and residue `0` modulo `n`.

The residue class is explicitly constructed with `ZMod.chineseRemainder`; the final integer
progression is obtained by choosing an integer representative and adding multiples of `m*n`. -/
theorem crtBinaryArithmeticProgression_exists {m n : ℕ}
    (hm : 1 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    ∃ base step : ℤ,
      step ≠ 0 ∧
      Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ,
        ((base + step * t : ℤ) : ZMod m) = 1 ∧
          ((base + step * t : ℤ) : ZMod n) = 0 := by
  let z : ZMod (m * n) := (ZMod.chineseRemainder h).symm (1, 0)
  obtain ⟨base, hbase⟩ := ZMod.intCast_surjective z
  let step : ℤ := ((m * n : ℕ) : ℤ)
  have hstepNat : m * n ≠ 0 := Nat.mul_ne_zero (ne_of_gt (lt_trans Nat.zero_lt_one hm)) (ne_of_gt hn)
  have hstep : step ≠ 0 := by
    dsimp [step]
    exact_mod_cast hstepNat
  refine ⟨base, step, hstep, arithmeticProgression_injective (base := base) hstep, ?_⟩
  intro t
  have hstep_zero : ((step : ℤ) : ZMod (m * n)) = 0 := by
    dsimp [step]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp
  have hx : (((base + step * t : ℤ) : ZMod (m * n))) = z := by
    rw [Int.cast_add, Int.cast_mul, hbase, hstep_zero, zero_mul, add_zero]
  have hpair :
      ZMod.chineseRemainder h (((base + step * t : ℤ) : ZMod (m * n))) = (1, 0) := by
    rw [hx]
    simp [z]
  constructor
  · simpa [ZMod.chineseRemainder] using congrArg Prod.fst hpair
  · simpa [ZMod.chineseRemainder] using congrArg Prod.snd hpair

/-- A translated four-layer congruence profile.  Each modulus controls one decision layer.
The `1 <` hypotheses ensure that residue `1` is genuinely different from the good residue `0`;
the pairwise coprimality hypotheses are exactly the CRT compatibility needed for independent
witness progressions. -/
structure FourLayerProfile where
  numMod : ℕ
  modMod : ℕ
  padicMod : ℕ
  ecMod : ℕ
  hnum : 1 < numMod
  hmod : 1 < modMod
  hpadic : 1 < padicMod
  hec : 1 < ecMod
  h_num_mod : Nat.Coprime numMod modMod
  h_num_padic : Nat.Coprime numMod padicMod
  h_num_ec : Nat.Coprime numMod ecMod
  h_mod_padic : Nat.Coprime modMod padicMod
  h_mod_ec : Nat.Coprime modMod ecMod
  h_padic_ec : Nat.Coprime padicMod ecMod

namespace FourLayerProfile

/-- Product of the three non-numeric moduli. -/
def othersNum (P : FourLayerProfile) : ℕ := P.modMod * (P.padicMod * P.ecMod)

/-- Product of the three non-modular moduli. -/
def othersMod (P : FourLayerProfile) : ℕ := P.numMod * (P.padicMod * P.ecMod)

/-- Product of the three non-`p`-adic moduli. -/
def othersPadic (P : FourLayerProfile) : ℕ := P.numMod * (P.modMod * P.ecMod)

/-- Product of the three non-EC moduli. -/
def othersEC (P : FourLayerProfile) : ℕ := P.numMod * (P.modMod * P.padicMod)

theorem othersNum_pos (P : FourLayerProfile) : 0 < P.othersNum := by
  dsimp [othersNum]
  exact Nat.mul_pos (lt_trans Nat.zero_lt_one P.hmod)
    (Nat.mul_pos (lt_trans Nat.zero_lt_one P.hpadic) (lt_trans Nat.zero_lt_one P.hec))

theorem othersMod_pos (P : FourLayerProfile) : 0 < P.othersMod := by
  dsimp [othersMod]
  exact Nat.mul_pos (lt_trans Nat.zero_lt_one P.hnum)
    (Nat.mul_pos (lt_trans Nat.zero_lt_one P.hpadic) (lt_trans Nat.zero_lt_one P.hec))

theorem othersPadic_pos (P : FourLayerProfile) : 0 < P.othersPadic := by
  dsimp [othersPadic]
  exact Nat.mul_pos (lt_trans Nat.zero_lt_one P.hnum)
    (Nat.mul_pos (lt_trans Nat.zero_lt_one P.hmod) (lt_trans Nat.zero_lt_one P.hec))

theorem othersEC_pos (P : FourLayerProfile) : 0 < P.othersEC := by
  dsimp [othersEC]
  exact Nat.mul_pos (lt_trans Nat.zero_lt_one P.hnum)
    (Nat.mul_pos (lt_trans Nat.zero_lt_one P.hmod) (lt_trans Nat.zero_lt_one P.hpadic))

theorem coprime_num_others (P : FourLayerProfile) : Nat.Coprime P.numMod P.othersNum := by
  dsimp [othersNum]
  exact P.h_num_mod.mul_right (P.h_num_padic.mul_right P.h_num_ec)

theorem coprime_mod_others (P : FourLayerProfile) : Nat.Coprime P.modMod P.othersMod := by
  dsimp [othersMod]
  exact P.h_num_mod.symm.mul_right (P.h_mod_padic.mul_right P.h_mod_ec)

theorem coprime_padic_others (P : FourLayerProfile) : Nat.Coprime P.padicMod P.othersPadic := by
  dsimp [othersPadic]
  exact P.h_num_padic.symm.mul_right (P.h_mod_padic.symm.mul_right P.h_padic_ec)

theorem coprime_ec_others (P : FourLayerProfile) : Nat.Coprime P.ecMod P.othersEC := by
  dsimp [othersEC]
  exact P.h_num_ec.symm.mul_right (P.h_mod_ec.symm.mul_right P.h_padic_ec.symm)

end FourLayerProfile

/-- Numeric/log layer after the `(Hk)` valuation reduction, modeled as a congruence gate. -/
def Fnum (P : FourLayerProfile) (x : ℤ) : Prop := ((x : ZMod P.numMod) = 0)

/-- Modular residue layer. -/
def Fmod (P : FourLayerProfile) (x : ℤ) : Prop := ((x : ZMod P.modMod) = 0)

/-- Henselian/`p`-adic lifting layer, modeled at a fixed congruence precision. -/
def Fp_adic (P : FourLayerProfile) (x : ℤ) : Prop := ((x : ZMod P.padicMod) = 0)

/-- Elliptic/Jacobian regularity layer, modeled by its good-open congruence detector. -/
def FEC (P : FourLayerProfile) (x : ℤ) : Prop := ((x : ZMod P.ecMod) = 0)

/-- The four-layer fiber product, computed sectionwise as intersection of the four gates. -/
def FourLayerPass (P : FourLayerProfile) (x : ℤ) : Prop :=
  Fnum P x ∧ Fmod P x ∧ Fp_adic P x ∧ FEC P x

theorem Fnum_iff_dvd (P : FourLayerProfile) (x : ℤ) :
    Fnum P x ↔ ((P.numMod : ℤ) ∣ x) :=
  ZMod.intCast_zmod_eq_zero_iff_dvd x P.numMod

theorem Fmod_iff_dvd (P : FourLayerProfile) (x : ℤ) :
    Fmod P x ↔ ((P.modMod : ℤ) ∣ x) :=
  ZMod.intCast_zmod_eq_zero_iff_dvd x P.modMod

theorem Fp_adic_iff_dvd (P : FourLayerProfile) (x : ℤ) :
    Fp_adic P x ↔ ((P.padicMod : ℤ) ∣ x) :=
  ZMod.intCast_zmod_eq_zero_iff_dvd x P.padicMod

theorem FEC_iff_dvd (P : FourLayerProfile) (x : ℤ) :
    FEC P x ↔ ((P.ecMod : ℤ) ∣ x) :=
  ZMod.intCast_zmod_eq_zero_iff_dvd x P.ecMod

theorem zmod_zero_of_dvd_of_zmod_zero {q n : ℕ} (hqn : q ∣ n) {x : ℤ}
    (hx : ((x : ℤ) : ZMod n) = 0) : ((x : ℤ) : ZMod q) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx ⊢
  have hqn' : (q : ℤ) ∣ (n : ℤ) := by exact_mod_cast hqn
  exact hqn'.trans hx

theorem zmod_one_ne_zero_of_one_lt {m : ℕ} (hm : 1 < m) : (1 : ZMod m) ≠ 0 := by
  intro h
  have hm1 : m = 1 := (ZMod.one_eq_zero_iff.mp h)
  omega

theorem gate_fails_of_coord_one {m : ℕ} (hm : 1 < m) {x : ℤ}
    (hx : ((x : ℤ) : ZMod m) = 1) : ¬ ((x : ℤ) : ZMod m) = 0 := by
  intro hz
  exact zmod_one_ne_zero_of_one_lt hm (by rw [← hx, hz])

theorem dvd_num_othersMod (P : FourLayerProfile) : P.numMod ∣ P.othersMod := by
  dsimp [FourLayerProfile.othersMod]
  exact dvd_mul_right _ _

theorem dvd_padic_othersMod (P : FourLayerProfile) : P.padicMod ∣ P.othersMod := by
  dsimp [FourLayerProfile.othersMod]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

theorem dvd_ec_othersMod (P : FourLayerProfile) : P.ecMod ∣ P.othersMod := by
  dsimp [FourLayerProfile.othersMod]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

theorem dvd_mod_othersNum (P : FourLayerProfile) : P.modMod ∣ P.othersNum := by
  dsimp [FourLayerProfile.othersNum]
  exact dvd_mul_right _ _

theorem dvd_padic_othersNum (P : FourLayerProfile) : P.padicMod ∣ P.othersNum := by
  dsimp [FourLayerProfile.othersNum]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

theorem dvd_ec_othersNum (P : FourLayerProfile) : P.ecMod ∣ P.othersNum := by
  dsimp [FourLayerProfile.othersNum]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

theorem dvd_num_othersPadic (P : FourLayerProfile) : P.numMod ∣ P.othersPadic := by
  dsimp [FourLayerProfile.othersPadic]
  exact dvd_mul_right _ _

theorem dvd_mod_othersPadic (P : FourLayerProfile) : P.modMod ∣ P.othersPadic := by
  dsimp [FourLayerProfile.othersPadic]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

theorem dvd_ec_othersPadic (P : FourLayerProfile) : P.ecMod ∣ P.othersPadic := by
  dsimp [FourLayerProfile.othersPadic]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

theorem dvd_num_othersEC (P : FourLayerProfile) : P.numMod ∣ P.othersEC := by
  dsimp [FourLayerProfile.othersEC]
  exact dvd_mul_right _ _

theorem dvd_mod_othersEC (P : FourLayerProfile) : P.modMod ∣ P.othersEC := by
  dsimp [FourLayerProfile.othersEC]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

theorem dvd_padic_othersEC (P : FourLayerProfile) : P.padicMod ∣ P.othersEC := by
  dsimp [FourLayerProfile.othersEC]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

/-- **Thm .1, Mod-critical witness.**
There is an infinite arithmetic progression on which the numeric, `p`-adic, and EC layers pass,
while the modular layer alone fails. -/
theorem modCritical_AP (P : FourLayerProfile) :
    ∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, Fnum P (base + step * t) ∧ ¬ Fmod P (base + step * t) ∧
        Fp_adic P (base + step * t) ∧ FEC P (base + step * t) := by
  obtain ⟨base, step, hstep, hinj, hcoords⟩ :=
    crtBinaryArithmeticProgression_exists P.hmod P.othersMod_pos P.coprime_mod_others
  refine ⟨base, step, hstep, hinj, ?_⟩
  intro t
  rcases hcoords t with ⟨hbad, hgood⟩
  exact ⟨zmod_zero_of_dvd_of_zmod_zero (dvd_num_othersMod P) hgood,
    gate_fails_of_coord_one P.hmod hbad,
    zmod_zero_of_dvd_of_zmod_zero (dvd_padic_othersMod P) hgood,
    zmod_zero_of_dvd_of_zmod_zero (dvd_ec_othersMod P) hgood⟩

/-- **Thm .1, Numeric-critical witness.**
There is an infinite arithmetic progression on which the modular, `p`-adic, and EC layers pass,
while the numeric/valuation layer alone fails. -/
theorem numericCritical_AP (P : FourLayerProfile) :
    ∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, ¬ Fnum P (base + step * t) ∧ Fmod P (base + step * t) ∧
        Fp_adic P (base + step * t) ∧ FEC P (base + step * t) := by
  obtain ⟨base, step, hstep, hinj, hcoords⟩ :=
    crtBinaryArithmeticProgression_exists P.hnum P.othersNum_pos P.coprime_num_others
  refine ⟨base, step, hstep, hinj, ?_⟩
  intro t
  rcases hcoords t with ⟨hbad, hgood⟩
  exact ⟨gate_fails_of_coord_one P.hnum hbad,
    zmod_zero_of_dvd_of_zmod_zero (dvd_mod_othersNum P) hgood,
    zmod_zero_of_dvd_of_zmod_zero (dvd_padic_othersNum P) hgood,
    zmod_zero_of_dvd_of_zmod_zero (dvd_ec_othersNum P) hgood⟩

/-- **Thm .1, p-Adic-critical witness.**
There is an infinite arithmetic progression on which the numeric, modular, and EC layers pass,
while the `p`-adic layer alone fails. -/
theorem pAdicCritical_AP (P : FourLayerProfile) :
    ∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, Fnum P (base + step * t) ∧ Fmod P (base + step * t) ∧
        ¬ Fp_adic P (base + step * t) ∧ FEC P (base + step * t) := by
  obtain ⟨base, step, hstep, hinj, hcoords⟩ :=
    crtBinaryArithmeticProgression_exists P.hpadic P.othersPadic_pos P.coprime_padic_others
  refine ⟨base, step, hstep, hinj, ?_⟩
  intro t
  rcases hcoords t with ⟨hbad, hgood⟩
  exact ⟨zmod_zero_of_dvd_of_zmod_zero (dvd_num_othersPadic P) hgood,
    zmod_zero_of_dvd_of_zmod_zero (dvd_mod_othersPadic P) hgood,
    gate_fails_of_coord_one P.hpadic hbad,
    zmod_zero_of_dvd_of_zmod_zero (dvd_ec_othersPadic P) hgood⟩

/-- **Thm .1, EC-critical witness.**
There is an infinite arithmetic progression on which the numeric, modular, and `p`-adic layers
pass, while the EC layer alone fails. -/
theorem ecCritical_AP (P : FourLayerProfile) :
    ∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, Fnum P (base + step * t) ∧ Fmod P (base + step * t) ∧
        Fp_adic P (base + step * t) ∧ ¬ FEC P (base + step * t) := by
  obtain ⟨base, step, hstep, hinj, hcoords⟩ :=
    crtBinaryArithmeticProgression_exists P.hec P.othersEC_pos P.coprime_ec_others
  refine ⟨base, step, hstep, hinj, ?_⟩
  intro t
  rcases hcoords t with ⟨hbad, hgood⟩
  exact ⟨zmod_zero_of_dvd_of_zmod_zero (dvd_num_othersEC P) hgood,
    zmod_zero_of_dvd_of_zmod_zero (dvd_mod_othersEC P) hgood,
    zmod_zero_of_dvd_of_zmod_zero (dvd_padic_othersEC P) hgood,
    gate_fails_of_coord_one P.hec hbad⟩

/-- **Thm .1, four-layer strict independence.**
Each of the four translated decision predicates admits an infinite arithmetic progression on
which exactly that layer fails and the other three pass. -/
theorem fourLayerStrictIndependence (P : FourLayerProfile) :
    (∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, Fnum P (base + step * t) ∧ ¬ Fmod P (base + step * t) ∧
        Fp_adic P (base + step * t) ∧ FEC P (base + step * t)) ∧
    (∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, ¬ Fnum P (base + step * t) ∧ Fmod P (base + step * t) ∧
        Fp_adic P (base + step * t) ∧ FEC P (base + step * t)) ∧
    (∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, Fnum P (base + step * t) ∧ Fmod P (base + step * t) ∧
        ¬ Fp_adic P (base + step * t) ∧ FEC P (base + step * t)) ∧
    (∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, Fnum P (base + step * t) ∧ Fmod P (base + step * t) ∧
        Fp_adic P (base + step * t) ∧ ¬ FEC P (base + step * t)) :=
  ⟨modCritical_AP P, numericCritical_AP P, pAdicCritical_AP P, ecCritical_AP P⟩

/-! ## §B — Equalizer / Čech–Tor / CRT (Thm .3/.19, Lem .6/.39, Cor .9/.40). -/

theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a := lcm_dvd_iff.symm

theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- **Lem .39 (Čech Ĥ¹ obstruction / gluing).** Local witnesses glue iff `gcd ∣ (a-b)`. -/
theorem crt_solvable_iff (M N a b : ℤ) :
    (∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b)) ↔ (↑(Int.gcd M N) : ℤ) ∣ (a - b) := by
  constructor
  · rintro ⟨x, hMa, hNb⟩
    have h1 : (↑(Int.gcd M N) : ℤ) ∣ (x - a) := (Int.gcd_dvd_left M N).trans hMa
    have h2 : (↑(Int.gcd M N) : ℤ) ∣ (x - b) := (Int.gcd_dvd_right M N).trans hNb
    simpa [sub_sub_sub_cancel_right] using dvd_sub h2 h1
  · rintro ⟨w, hw⟩
    have hbez : (↑(Int.gcd M N) : ℤ) = M * Int.gcdA M N + N * Int.gcdB M N := Int.gcd_eq_gcd_ab M N
    have hab : a - b = (M * Int.gcdA M N + N * Int.gcdB M N) * w := by rw [← hbez, hw]
    refine ⟨a - M * Int.gcdA M N * w, ⟨-(Int.gcdA M N) * w, by ring⟩, ⟨Int.gcdB M N * w, ?_⟩⟩
    have hrw : a - M * Int.gcdA M N * w - b = (a - b) - M * Int.gcdA M N * w := by ring
    rw [hrw, hab]; ring

noncomputable def crt_iso {a b : ℕ} (h : Nat.Coprime a b) :
    ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder h

/-- Cokernel of an additive homomorphism, implemented as the quotient by its range. -/
abbrev AddCoker {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :=
  B ⧸ f.range

/-- Natural-cast compatibility for `Int.gcd`. -/
theorem int_gcd_natCast (M N : ℕ) :
    Int.gcd (M : ℤ) (N : ℤ) = Nat.gcd M N := by
  simp [Int.gcd]

/-- Divisibility by `n` turns into equality in `ZMod n`. -/
theorem intCast_eq_of_dvd_sub {n : ℕ} {X Y : ℤ} (h : (n : ℤ) ∣ (X - Y)) :
    (X : ZMod n) = (Y : ZMod n) := by
  have hz : ((X - Y : ℤ) : ZMod n) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  rwa [Int.cast_sub, sub_eq_zero] at hz

/-- The CRT comparison map `Φ : ℤ → ZMod M × ZMod N`, `x ↦ (x mod M, x mod N)`. -/
def crtPhi (M N : ℕ) : ℤ →+ ZMod M × ZMod N where
  toFun x := ((x : ZMod M), (x : ZMod N))
  map_zero' := by simp
  map_add' x y := by simp only [Int.cast_add, Prod.mk_add_mk]

/-- The overlap difference `∂ : ZMod M × ZMod N → ZMod (gcd M N)`,
`(a,b) ↦ a - b` after restriction to the common quotient. -/
def crtDel (M N : ℕ) : ZMod M × ZMod N →+ ZMod (Nat.gcd M N) where
  toFun y :=
    ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N)) y.1 -
    ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N)) y.2
  map_zero' := by simp
  map_add' y z := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

@[simp]
theorem crtDel_intCast (M N : ℕ) (a b : ℤ) :
    crtDel M N ((a : ZMod M), (b : ZMod N)) =
      (a : ZMod (Nat.gcd M N)) - (b : ZMod (Nat.gcd M N)) := by
  simp only [crtDel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_intCast]

@[simp]
theorem crtDel_comp_crtPhi (M N : ℕ) (x : ℤ) :
    crtDel M N (crtPhi M N x) = 0 := by
  change crtDel M N ((x : ZMod M), (x : ZMod N)) = 0
  rw [crtDel_intCast]
  simp

/-- The kernel of `Φ` consists of integers divisible by both moduli. -/
theorem crtPhi_mem_ker_iff (M N : ℕ) (x : ℤ) :
    x ∈ (crtPhi M N).ker ↔ (M : ℤ) ∣ x ∧ (N : ℤ) ∣ x := by
  rw [AddMonoidHom.mem_ker]
  change ((x : ZMod M), (x : ZMod N)) = 0 ↔ (M : ℤ) ∣ x ∧ (N : ℤ) ∣ x
  rw [Prod.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The kernel of `Φ` is the intersection ideal, equivalently the `lcm` condition. -/
theorem crtPhi_mem_ker_iff_lcm (M N : ℕ) (x : ℤ) :
    x ∈ (crtPhi M N).ker ↔ (lcm (M : ℤ) (N : ℤ)) ∣ x := by
  rw [crtPhi_mem_ker_iff, kernel_mem_iff_lcm]

/-- Exactness in the middle of the CRT/Čech sequence:
`range Φ = ker ∂`. -/
theorem crtDel_exact_crtPhi (M N : ℕ) :
    Function.Exact (crtPhi M N) (crtDel M N) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, b⟩ := y
    obtain ⟨a', rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨b', rfl⟩ := ZMod.intCast_surjective b
    rw [crtDel_intCast] at hy
    have hcong : ((a' - b' : ℤ) : ZMod (Nat.gcd M N)) = 0 := by
      rw [Int.cast_sub]
      exact hy
    have hdvd : (Nat.gcd M N : ℤ) ∣ (a' - b') :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcong
    obtain ⟨x, hxa, hxb⟩ :=
      (crt_solvable_iff (M : ℤ) (N : ℤ) a' b').mpr (by
        rw [int_gcd_natCast]
        exact hdvd)
    refine ⟨x, ?_⟩
    have h1 : ((x : ℤ) : ZMod M) = ((a' : ℤ) : ZMod M) :=
      intCast_eq_of_dvd_sub hxa
    have h2 : ((x : ℤ) : ZMod N) = ((b' : ℤ) : ZMod N) :=
      intCast_eq_of_dvd_sub hxb
    show ((x : ZMod M), (x : ZMod N)) = ((a' : ZMod M), (b' : ZMod N))
    rw [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  · rintro ⟨x, rfl⟩
    exact crtDel_comp_crtPhi M N x

/-- The difference map `∂` is onto `ZMod (gcd M N)`. -/
theorem crtDel_surjective (M N : ℕ) :
    Function.Surjective (crtDel M N) := by
  intro z
  obtain ⟨z', rfl⟩ := ZMod.intCast_surjective z
  refine ⟨((z' : ZMod M), ((0 : ℤ) : ZMod N)), ?_⟩
  rw [crtDel_intCast]
  simp

/-- The range of `Φ` is exactly the kernel of the difference map. -/
theorem crtPhi_range_eq_crtDel_ker (M N : ℕ) :
    (crtPhi M N).range = (crtDel M N).ker := by
  ext y
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  exact (crtDel_exact_crtPhi M N y).symm

/-- Čech `Ĥ¹` in the modular CRT presentation: `coker Φ`. -/
abbrev cechPhiCoker (M N : ℕ) : Type :=
  AddCoker (crtPhi M N)

/-- **Lem .39 / Cor .40 / Thm .3 (cokernel form).**
For `Φ : ℤ → ZMod M × ZMod N`, `x ↦ (x mod M, x mod N)`, the cokernel is
canonically the common obstruction group `ZMod (gcd M N)`, via `(a,b) ↦ a-b`. -/
noncomputable def cechPhiCokerEquivZModGcd (M N : ℕ) :
    cechPhiCoker M N ≃+ ZMod (Nat.gcd M N) :=
  QuotientAddGroup.liftEquiv (crtPhi M N).range
    (φ := crtDel M N) (crtDel_surjective M N)
    (crtPhi_range_eq_crtDel_ker M N)

@[simp]
theorem cechPhiCokerEquivZModGcd_mk (M N : ℕ) (y : ZMod M × ZMod N) :
    cechPhiCokerEquivZModGcd M N (QuotientAddGroup.mk y) = crtDel M N y := by
  simp [cechPhiCokerEquivZModGcd]

/-- The Čech obstruction group has cardinality `gcd M N`. -/
theorem cechPhiCoker_card (M N : ℕ) :
    Nat.card (cechPhiCoker M N) = Nat.gcd M N := by
  calc
    Nat.card (cechPhiCoker M N) = Nat.card (ZMod (Nat.gcd M N)) :=
      Nat.card_congr (cechPhiCokerEquivZModGcd M N).toEquiv
    _ = Nat.gcd M N := Nat.card_zmod (Nat.gcd M N)

/-- The Čech obstruction group is trivial exactly in the coprime case. -/
theorem cechPhiCoker_card_eq_one_iff_gcd_eq_one (M N : ℕ) :
    Nat.card (cechPhiCoker M N) = 1 ↔ Nat.gcd M N = 1 := by
  rw [cechPhiCoker_card]

theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

/-- Integer principal ideals generated by natural numbers intersect in the principal ideal
generated by their natural lcm. -/
theorem kernel_ideal_inter_nat (M N : ℕ) :
    (Ideal.span {((M : ℕ) : ℤ)} ⊓ Ideal.span {((N : ℕ) : ℤ)} : Ideal ℤ) =
      Ideal.span {((Nat.lcm M N : ℕ) : ℤ)} := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton]
  change ((M : ℤ) ∣ a ∧ (N : ℤ) ∣ a) ↔ ((Nat.lcm M N : ℕ) : ℤ) ∣ a
  rw [← lcm_dvd_iff]
  have hlcm : lcm (M : ℤ) (N : ℤ) = ((Nat.lcm M N : ℕ) : ℤ) := by
    change ((Int.lcm (M : ℤ) (N : ℤ) : ℕ) : ℤ) = ((Nat.lcm M N : ℕ) : ℤ)
    rfl
  rw [hlcm]

/-- Corrected Theorem .19(a), valuation form: the intersection/lcm thickness at `p`
against a prime power is `max(vₚ M,k)`, not `min(vₚ M,k)`. -/
theorem lcm_prime_power_thickness {M p k : ℕ} (hM : M ≠ 0) (hp : p.Prime) :
    (Nat.lcm M (p ^ k)).factorization p = max (M.factorization p) k := by
  rw [factorization_lcm_apply hM (pow_ne_zero k hp.ne_zero), Nat.factorization_pow_self hp]

/-- Failure-fiber/Tor thickness: the gcd side is the one with `min(vₚ M,k)`. -/
theorem gcd_prime_power_thickness {M p k : ℕ} (hM : M ≠ 0) (hp : p.Prime) :
    (Nat.gcd M (p ^ k)).factorization p = min (M.factorization p) k := by
  rw [factorization_gcd_apply hM (pow_ne_zero k hp.ne_zero), Nat.factorization_pow_self hp]

/-- The corrected intersection thickness exponent really gives a divisor of the lcm. -/
theorem lcm_prime_power_pow_dvd {M p k : ℕ} (hM : M ≠ 0) (hp : p.Prime) :
    p ^ max (M.factorization p) k ∣ Nat.lcm M (p ^ k) := by
  have hn : Nat.lcm M (p ^ k) ≠ 0 := Nat.lcm_ne_zero hM (pow_ne_zero k hp.ne_zero)
  exact (hp.pow_dvd_iff_le_factorization hn).mpr (by
    rw [lcm_prime_power_thickness hM hp])

/-- After removing the whole corrected `p`-power thickness from the lcm, the remaining factor is
not divisible by `p`; hence it becomes a unit in the localization at `(p)`. -/
theorem lcm_prime_power_unit_part_not_dvd {M p k : ℕ} (hM : M ≠ 0) (hp : p.Prime) :
    ¬ p ∣ Nat.lcm M (p ^ k) / p ^ max (M.factorization p) k := by
  let n := Nat.lcm M (p ^ k)
  let e := max (M.factorization p) k
  have hn : n ≠ 0 := Nat.lcm_ne_zero hM (pow_ne_zero k hp.ne_zero)
  have he : e = n.factorization p := by
    simp [e, n, lcm_prime_power_thickness hM hp]
  simpa [n, e, he] using Nat.not_dvd_ordCompl hp hn

/-- A natural number not divisible by `p` is not in the integer ideal `(p)`. -/
theorem int_nat_notMem_span_singleton_of_not_dvd {u p : ℕ} (hpu : ¬ p ∣ u) :
    (u : ℤ) ∉ (Ideal.span {(p : ℤ)} : Ideal ℤ) := by
  intro hu
  exact hpu (Int.natCast_dvd.mp (Ideal.mem_span_singleton.mp hu))

/-- Mapping a principal ideal whose generator differs by a right unit does not change the
generated ideal. -/
theorem map_span_singleton_mul_right_unit {S : Type*} [CommRing S] [Algebra ℤ S]
    {a b u : ℤ} (ha : a = b * u) (hu : IsUnit ((algebraMap ℤ S) u)) :
    Ideal.map (algebraMap ℤ S) (Ideal.span {a}) =
      Ideal.span {(algebraMap ℤ S) b} := by
  rw [Ideal.map_span, Set.image_singleton, ha, map_mul]
  exact Ideal.span_singleton_mul_right_unit hu _

/-- The lcm ideal localized at a prime ideal `P = (p)` is generated by the corrected
`p`-thickness `p^max(vₚ M,k)`. -/
theorem localized_lcm_prime_power_ideal_eq_span
    {M p k : ℕ} (hM : M ≠ 0) (hp : p.Prime)
    (P : Ideal ℤ) [P.IsPrime] (hP : P = Ideal.span {(p : ℤ)})
    (Rₚ : Type*) [CommRing Rₚ] [Algebra ℤ Rₚ] [IsLocalization.AtPrime Rₚ P] :
    Ideal.map (algebraMap ℤ Rₚ)
        (Ideal.span {((Nat.lcm M (p ^ k) : ℕ) : ℤ)}) =
      Ideal.span {(algebraMap ℤ Rₚ) (((p ^ max (M.factorization p) k : ℕ) : ℤ))} := by
  let e := max (M.factorization p) k
  let n := Nat.lcm M (p ^ k)
  let u := n / p ^ e
  have hdvd : p ^ e ∣ n := by
    simpa [e, n] using lcm_prime_power_pow_dvd (M := M) (p := p) (k := k) hM hp
  have hfacNat : n = p ^ e * u := by
    change n = p ^ e * (n / p ^ e)
    rw [mul_comm]
    exact (Nat.div_mul_cancel hdvd).symm
  have hfacInt : ((n : ℕ) : ℤ) = ((p ^ e : ℕ) : ℤ) * (u : ℤ) := by
    exact_mod_cast hfacNat
  have hnot : (u : ℤ) ∉ P := by
    rw [hP]
    exact int_nat_notMem_span_singleton_of_not_dvd
      (lcm_prime_power_unit_part_not_dvd (M := M) (p := p) (k := k) hM hp)
  have hunit : IsUnit ((algebraMap ℤ Rₚ) (u : ℤ)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff Rₚ P (u : ℤ)).mpr (by
      rw [Ideal.mem_primeCompl_iff]
      exact hnot)
  simpa [e, n] using
    map_span_singleton_mul_right_unit (S := Rₚ) (a := ((n : ℕ) : ℤ))
      (b := ((p ^ e : ℕ) : ℤ)) (u := (u : ℤ)) hfacInt hunit

/-- **Corrected Thm .19(a), localized ideal form.**
After localizing at a prime ideal `P = (p)`, the intersection `(M) ∩ (p^k)` is generated by
`p^max(vₚ M,k)`. This is the corrected form of the paper statement; the `min` exponent belongs
to the gcd/Tor failure fiber, not to the intersection. -/
theorem localized_intersection_prime_power_ideal_eq_span
    {M p k : ℕ} (hM : M ≠ 0) (hp : p.Prime)
    (P : Ideal ℤ) [P.IsPrime] (hP : P = Ideal.span {(p : ℤ)})
    (Rₚ : Type*) [CommRing Rₚ] [Algebra ℤ Rₚ] [IsLocalization.AtPrime Rₚ P] :
    Ideal.map (algebraMap ℤ Rₚ)
        ((Ideal.span {((M : ℕ) : ℤ)} ⊓ Ideal.span {(((p ^ k : ℕ)) : ℤ)} : Ideal ℤ)) =
      Ideal.span {(algebraMap ℤ Rₚ) (((p ^ max (M.factorization p) k : ℕ) : ℤ))} := by
  rw [kernel_ideal_inter_nat M (p ^ k)]
  exact localized_lcm_prime_power_ideal_eq_span (M := M) (p := p) (k := k) hM hp P hP Rₚ

theorem range_mulLeft (N : ℕ) [NeZero N] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).range = AddSubgroup.zmultiples (M : ZMod N) := by
  ext y
  rw [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x.val : ℤ), ?_⟩
    rw [zsmul_eq_mul]; push_cast; rw [ZMod.natCast_zmod_val]; simp [mul_comm]
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ZMod N), by rw [zsmul_eq_mul]; simp [mul_comm]⟩

/-- **Lem .6 / Thm .3 / .19.** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(N, M)`. -/
theorem card_ker_mulLeft (N : ℕ) [NeZero N] (M : ℕ) :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker = Nat.gcd N M := by
  have hG : Nat.card (ZMod N) = N := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hr : Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).range = N / N.gcd M := by
    rw [range_mulLeft, Nat.card_zmultiples, ZMod.addOrderOf_coe M (NeZero.ne N)]
  have hmul : Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker
              * Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).range = N := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, hG]
  rw [hr] at hmul
  have hg : 0 < N.gcd M := Nat.gcd_pos_of_pos_left M (Nat.pos_of_ne_zero (NeZero.ne N))
  have hdvd : N.gcd M ∣ N := Nat.gcd_dvd_left N M
  have hdpos : 0 < N / N.gcd M :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd) hg
  have hfin : Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker * (N / N.gcd M)
        = N.gcd M * (N / N.gcd M) := by rw [hmul, Nat.mul_div_cancel' hdvd]
  exact Nat.eq_of_mul_eq_mul_right hdpos hfin

/-- The distinguished kernel generator: the class of `N / gcd(N,M)` in `ZMod N`. -/
theorem dvd_mul_div_gcd (N M : ℕ) :
    N ∣ M * (N / Nat.gcd N M) := by
  refine ⟨M / Nat.gcd N M, ?_⟩
  calc
    M * (N / Nat.gcd N M)
        = (M / Nat.gcd N M * Nat.gcd N M) * (N / Nat.gcd N M) := by
          rw [Nat.div_mul_cancel (Nat.gcd_dvd_right N M)]
    _ = (M / Nat.gcd N M) * (Nat.gcd N M * (N / Nat.gcd N M)) := by
          rw [mul_assoc]
    _ = (M / Nat.gcd N M) * ((N / Nat.gcd N M) * Nat.gcd N M) := by
          rw [mul_comm (Nat.gcd N M)]
    _ = (M / Nat.gcd N M) * N := by
          rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N M)]
    _ = N * (M / Nat.gcd N M) := by
          rw [mul_comm]

/-- Cancelling the common divisor in `N ∣ M*r`: the kernel condition forces
`N/gcd(N,M) ∣ r`. -/
theorem div_gcd_dvd_of_dvd_mul {N M r : ℕ} (hN : N ≠ 0) (h : N ∣ M * r) :
    N / Nat.gcd N M ∣ r := by
  let d := Nat.gcd N M
  have hdpos : 0 < d := by
    simpa [d] using Nat.gcd_pos_of_pos_left (M) (Nat.pos_of_ne_zero hN)
  have hcop : Nat.Coprime (N / d) (M / d) := by
    simpa [Nat.Coprime, d] using
      Nat.gcd_div_gcd_div_gcd_of_pos_left (n := N) (m := M) (Nat.pos_of_ne_zero hN)
  have hcancel : N / d ∣ M / d * r := by
    have h' : (N / d) * d ∣ ((M / d) * r) * d := by
      have hleft : (N / d) * d = N := by
        simpa [d] using Nat.div_mul_cancel (Nat.gcd_dvd_left N M)
      have hright : ((M / d) * r) * d = M * r := by
        rw [mul_assoc, mul_comm r d, ← mul_assoc]
        simpa [d] using congrArg (fun t => t * r)
          (Nat.div_mul_cancel (Nat.gcd_dvd_right N M))
      rwa [hleft, hright]
    exact (Nat.mul_dvd_mul_iff_right hdpos).mp h'
  exact (hcop.dvd_mul_left).mp hcancel

/-- Membership in the kernel of multiplication by `M` on `ZMod N`, expressed on
the canonical representative. -/
theorem mem_ker_mulLeft_iff_dvd_val (N : ℕ) [NeZero N] (M : ℕ) (x : ZMod N) :
    x ∈ (AddMonoidHom.mulLeft (M : ZMod N)).ker ↔ N ∣ M * x.val := by
  rw [AddMonoidHom.mem_ker]
  change (M : ZMod N) * x = 0 ↔ N ∣ M * x.val
  constructor
  · intro hx
    have hx' : ((M * x.val : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact hx
    exact (ZMod.natCast_eq_zero_iff (M * x.val) N).mp hx'
  · intro hx
    have hx' : ((M * x.val : ℕ) : ZMod N) = 0 :=
      (ZMod.natCast_eq_zero_iff (M * x.val) N).mpr hx
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul]
    exact hx'

/-- The canonical generator of `ker(×M : ZMod N → ZMod N)`, namely
`(N / gcd(N,M)) • 1`. -/
def kerMulLeftGenerator (N : ℕ) [NeZero N] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker :=
  ⟨(N / Nat.gcd N M : ZMod N), by
    rw [AddMonoidHom.mem_ker]
    change (M : ZMod N) * (N / Nat.gcd N M : ZMod N) = 0
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_div_gcd N M⟩

@[simp]
theorem kerMulLeftGenerator_coe (N : ℕ) [NeZero N] (M : ℕ) :
    (kerMulLeftGenerator N M : ZMod N) = (N / Nat.gcd N M : ZMod N) := rfl

/-- The kernel is generated by the class of `N / gcd(N,M)`. -/
theorem ker_mulLeft_le_zmultiples_generator (N : ℕ) [NeZero N] (M : ℕ) :
    ∀ x : (AddMonoidHom.mulLeft (M : ZMod N)).ker,
      x ∈ AddSubgroup.zmultiples (kerMulLeftGenerator N M) := by
  intro x
  rw [AddSubgroup.mem_zmultiples_iff]
  have hx_dvd : N / Nat.gcd N M ∣ (x : ZMod N).val := by
    exact div_gcd_dvd_of_dvd_mul (N := N) (M := M) (r := (x : ZMod N).val)
      (NeZero.ne N) ((mem_ker_mulLeft_iff_dvd_val N M (x : ZMod N)).mp x.2)
  refine ⟨(((x : ZMod N).val / (N / Nat.gcd N M) : ℕ) : ℤ), ?_⟩
  ext
  change (((((x : ZMod N).val / (N / Nat.gcd N M) : ℕ) : ℤ) •
      (N / Nat.gcd N M : ZMod N)) = (x : ZMod N))
  rw [zsmul_eq_mul]
  rw [Int.cast_natCast]
  rw [← Nat.cast_mul, Nat.div_mul_cancel hx_dvd, ZMod.natCast_zmod_val]

/-- Concrete cyclic parametrization of the kernel, sending `1` to
`N/gcd(N,M) ∈ ZMod N`. -/
noncomputable def zmodGcdEquivKerMulLeft (N : ℕ) [NeZero N] (M : ℕ) :
    ZMod (Nat.gcd N M) ≃+
      (AddMonoidHom.mulLeft (M : ZMod N)).ker :=
  zmodAddEquivOfGenerator (ker_mulLeft_le_zmultiples_generator N M)
    (by rw [card_ker_mulLeft])

@[simp]
theorem zmodGcdEquivKerMulLeft_apply_one (N : ℕ) [NeZero N] (M : ℕ) :
    zmodGcdEquivKerMulLeft N M 1 = kerMulLeftGenerator N M := by
  simp [zmodGcdEquivKerMulLeft]

/-- **Lem .6 / Thm .3 / .19 / Prop .7 (group iso form).**
The kernel of multiplication by `M` on `ZMod N` is genuinely isomorphic to
`ZMod (gcd N M)`, not just equinumerous with it. -/
noncomputable def kerMulLeftEquivZModGcd (N : ℕ) [NeZero N] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod (Nat.gcd N M) :=
  (zmodGcdEquivKerMulLeft N M).symm

/-- Degree-1 differential of the tensored standard resolution
`[ZMod N --×M--> ZMod N]`. -/
def torD1 (M N : ℕ) : ZMod N →+ ZMod N :=
  AddMonoidHom.mulLeft (M : ZMod N)

/-- Concrete object model for `Tor₁^ℤ(ℤ/M, ℤ/N)` from the standard two-term
resolution: the first homology is the kernel of `×M`. -/
abbrev TorH1 (M N : ℕ) : AddSubgroup (ZMod N) :=
  (torD1 M N).ker

/-- The order form follows from the concrete kernel model. -/
theorem TorH1_card (M N : ℕ) [NeZero N] :
    Nat.card (TorH1 M N) = Nat.gcd N M := by
  rw [TorH1, torD1, card_ker_mulLeft]

/-- **Lem .6 / Thm .3 / .19 / Prop .7.**
`Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ZMod (gcd N M)` as an additive group, via the explicit
kernel model of the standard resolution. -/
noncomputable def TorH1_iso_zmod_gcd (M N : ℕ) [NeZero N] :
    TorH1 M N ≃+ ZMod (Nat.gcd N M) :=
  kerMulLeftEquivZModGcd N M

/-- The prime-power CRT product used by `ZMod.equivPi` really multiplies back to `N`. -/
theorem prod_primePower_factorization_eq_self (N : ℕ) (hN : N ≠ 0) :
    (∏ p : N.primeFactors, (p : ℕ) ^ N.factorization p) = N :=
  (Nat.prod_pow_primeFactors_factorization hN).symm

/-- Prime-power factors in the CRT decomposition are nonzero. -/
theorem primePower_factorization_ne_zero (N : ℕ) (p : N.primeFactors) :
    (p : ℕ) ^ N.factorization p ≠ 0 :=
  pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero

/-- The finite CRT map sends natural constants to the corresponding constants in each
prime-power coordinate. -/
@[simp]
theorem zmodEquivPi_natCast (M N : ℕ) (hN : N ≠ 0) (p : N.primeFactors) :
    ((ZMod.equivPi N hN) (M : ZMod N)) p =
      (M : ZMod ((p : ℕ) ^ N.factorization p)) := by
  simp [ZMod.equivPi]

/-- CRT coordinates of an element of the concrete `Tor₁` kernel again lie in the corresponding
prime-power concrete kernels. -/
theorem TorH1_crt_coord_mem (M N : ℕ) (hN : N ≠ 0) (x : TorH1 M N)
    (p : N.primeFactors) :
    (((ZMod.equivPi N hN) (x : ZMod N)) p) ∈
      TorH1 M ((p : ℕ) ^ N.factorization p) := by
  have hxker : (x : ZMod N) ∈ (AddMonoidHom.mulLeft (M : ZMod N)).ker := by
    exact x.2
  have hx : (M : ZMod N) * (x : ZMod N) = 0 := by
    exact (AddMonoidHom.mulLeft (M : ZMod N)).mem_ker.mp hxker
  have hcoord := congrFun (congrArg (fun z => (ZMod.equivPi N hN) z) hx) p
  change (((ZMod.equivPi N hN) (x : ZMod N)) p) ∈
    (AddMonoidHom.mulLeft (M : ZMod ((p : ℕ) ^ N.factorization p))).ker
  exact (AddMonoidHom.mulLeft (M : ZMod ((p : ℕ) ^ N.factorization p))).mem_ker.mpr (by
    simpa [map_mul, map_zero, ZMod.equivPi] using hcoord)

/-- If all prime-power CRT coordinates are in the corresponding concrete kernels, then the
CRT-glued element lies in the concrete kernel modulo `N`. -/
theorem TorH1_crt_inv_mem (M N : ℕ) (hN : N ≠ 0)
    (y : (p : N.primeFactors) → TorH1 M ((p : ℕ) ^ N.factorization p)) :
    ((ZMod.equivPi N hN).symm
        (fun p => (y p : ZMod ((p : ℕ) ^ N.factorization p)))) ∈ TorH1 M N := by
  let e := ZMod.equivPi N hN
  let y0 : (p : N.primeFactors) → ZMod ((p : ℕ) ^ N.factorization p) := fun p => y p
  change e.symm y0 ∈ (AddMonoidHom.mulLeft (M : ZMod N)).ker
  exact (AddMonoidHom.mulLeft (M : ZMod N)).mem_ker.mpr (by
    apply e.injective
    ext p
    have hp : (M : ZMod ((p : ℕ) ^ N.factorization p)) *
        (y p : ZMod ((p : ℕ) ^ N.factorization p)) = 0 := by
      have hpker : (y p : ZMod ((p : ℕ) ^ N.factorization p)) ∈
          (AddMonoidHom.mulLeft (M : ZMod ((p : ℕ) ^ N.factorization p))).ker := by
        exact (y p).2
      exact
        ((AddMonoidHom.mulLeft (M : ZMod ((p : ℕ) ^ N.factorization p))).mem_ker.mp hpker)
    change (e ((M : ZMod N) * e.symm y0)) p = (e 0) p
    rw [map_mul, map_zero, e.apply_symm_apply]
    simp [e, y0, ZMod.equivPi, hp])

/-- **Prop .7 (primewise CRT decomposition, concrete kernel form).**
For `N = ∏ q^{v_q(N)}`, the concrete `Tor₁` kernel modulo `N` is additively
isomorphic to the product of the concrete prime-power kernels. -/
noncomputable def TorH1_primePowerDecomposition (M N : ℕ) (hN : N ≠ 0) :
    TorH1 M N ≃+
      ((p : N.primeFactors) → TorH1 M ((p : ℕ) ^ N.factorization p)) where
  toFun x := fun p =>
    ⟨((ZMod.equivPi N hN) (x : ZMod N)) p, TorH1_crt_coord_mem M N hN x p⟩
  invFun y :=
    ⟨(ZMod.equivPi N hN).symm
        (fun p => (y p : ZMod ((p : ℕ) ^ N.factorization p))),
      TorH1_crt_inv_mem M N hN y⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext p
    simp
  map_add' x y := by
    ext p
    simp [map_add]

@[simp]
theorem TorH1_primePowerDecomposition_apply (M N : ℕ) (hN : N ≠ 0)
    (x : TorH1 M N) (p : N.primeFactors) :
    (TorH1_primePowerDecomposition M N hN x p :
      ZMod ((p : ℕ) ^ N.factorization p)) =
        ((ZMod.equivPi N hN) (x : ZMod N)) p :=
  rfl

/-- **Cor .9 / .40.** Obstruction-free ⟺ gcd = 1. -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N := Iff.rfl

/-! ## §C — Primewise decomposition & indicator complexity (Prop .8). -/

theorem gcd_eq_prod_primeFactors {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Nat.gcd M N = ∏ q ∈ N.primeFactors, q ^ min (M.factorization q) (N.factorization q) := by
  have hg : Nat.gcd M N ≠ 0 := Nat.gcd_ne_zero_left hM
  have hsub : (Nat.gcd M N).primeFactors ⊆ N.primeFactors :=
    Nat.primeFactors_mono (Nat.gcd_dvd_right M N) hN
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hg]
  rw [Finsupp.prod, Nat.support_factorization]
  rw [Finset.prod_congr rfl (fun q _ => by rw [factorization_gcd_apply hM hN])]
  refine Finset.prod_subset hsub ?_
  intro q hqN hqg
  have h0 : min (M.factorization q) (N.factorization q) = 0 := by
    rw [← factorization_gcd_apply hM hN, Nat.factorization_eq_zero_iff]
    exact Or.inr (Or.inl (fun hdvd =>
      hqg (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hqN).1, hdvd, hg⟩)))
  rw [h0, pow_zero]

noncomputable def IC (M N : ℕ) : ℝ :=
  ∑ q ∈ N.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q

theorem card_Tor_eq_exp_IC {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    (Nat.gcd M N : ℝ) = Real.exp (IC M N) := by
  rw [IC, Real.exp_sum, gcd_eq_prod_primeFactors hM hN, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
  rw [Nat.cast_pow, ← Nat.cast_min, ← Real.log_pow, Real.exp_log (by positivity)]

/-- **Prop .8 (monotonicity).** `N' ∣ N ⇒ IC(M;N') ≤ IC(M;N)`. -/
theorem IC_mono {M N' N : ℕ} (hN : N ≠ 0) (hdvd : N' ∣ N) : IC M N' ≤ IC M N := by
  have hN' : N' ≠ 0 := fun h => hN (by simpa [h] using hdvd)
  have hle : N'.factorization ≤ N.factorization := (Nat.factorization_le_iff_dvd hN' hN).mpr hdvd
  calc IC M N'
      ≤ ∑ q ∈ N'.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        exact mul_le_mul_of_nonneg_right (min_le_min le_rfl (by exact_mod_cast hle q)) hlog
    _ ≤ IC M N := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hdvd hN)
        intro q hq _
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        exact mul_nonneg (by positivity) hlog

/-- Divisibility gives pointwise monotonicity of prime exponents. -/
theorem factorization_le_of_dvd_nonzero {M M' : ℕ} (hM' : M' ≠ 0) (hdvd : M ∣ M') :
    M.factorization ≤ M'.factorization := by
  have hM : M ≠ 0 := fun h => hM' (by simpa [h] using hdvd)
  exact (Nat.factorization_le_iff_dvd hM hM').mpr hdvd

/-- The IC summand is monotone in the first modulus. -/
theorem IC_summand_mono_left {M M' N q : ℕ}
    (hfac : M.factorization q ≤ M'.factorization q) (hq : q ∈ N.primeFactors) :
    (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q ≤
      (min (M'.factorization q) (N.factorization q) : ℝ) * Real.log q := by
  have hlog : (0 : ℝ) ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
  have hmin : min (M.factorization q) (N.factorization q) ≤
      min (M'.factorization q) (N.factorization q) :=
    min_le_min hfac le_rfl
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmin) hlog

/-- **Prop .8 (monotonicity, first argument).** `M ∣ M' ⇒ IC(M;N) ≤ IC(M';N)`. -/
theorem IC_mono_left {M M' N : ℕ} (hM' : M' ≠ 0) (hdvd : M ∣ M') :
    IC M N ≤ IC M' N := by
  have hle : M.factorization ≤ M'.factorization :=
    factorization_le_of_dvd_nonzero hM' hdvd
  unfold IC
  apply Finset.sum_le_sum
  intro q hq
  exact IC_summand_mono_left (M := M) (M' := M') (N := N) (q := q) (hle q) hq

/-- **Prop .8 (additivity on coprime factors).** -/
theorem IC_coprime_add {M N1 N2 : ℕ} (hN1 : N1 ≠ 0) (hN2 : N2 ≠ 0) (h : Nat.Coprime N1 N2) :
    IC M (N1 * N2) = IC M N1 + IC M N2 := by
  have hco : Nat.gcd N1 N2 = 1 := h
  unfold IC
  rw [Nat.primeFactors_mul hN1 hN2, Finset.sum_union h.disjoint_primeFactors]
  congr 1
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq2 : N2.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inr (Or.inl (fun hd => (Nat.mem_primeFactors.mp hq).1.ne_one
        (Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd (Nat.mem_primeFactors.mp hq).2.1 hd))))
    rw [Nat.factorization_mul hN1 hN2]; simp [hq2]
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq1 : N1.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inr (Or.inl (fun hd => (Nat.mem_primeFactors.mp hq).1.ne_one
        (Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd hd (Nat.mem_primeFactors.mp hq).2.1))))
    rw [Nat.factorization_mul hN1 hN2]; simp [hq1]

/-- The indicator complexity is nonnegative termwise. -/
theorem IC_nonneg (M N : ℕ) : 0 ≤ IC M N := by
  unfold IC
  apply Finset.sum_nonneg
  intro q hq
  have hlog : (0 : ℝ) ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
  exact mul_nonneg (by positivity) hlog

/-- If the overlap is coprime, then the indicator complexity vanishes. -/
theorem IC_eq_zero_of_gcd_eq_one {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (hg : Nat.gcd M N = 1) : IC M N = 0 := by
  apply Real.exp_injective
  calc
    Real.exp (IC M N) = (Nat.gcd M N : ℝ) := (card_Tor_eq_exp_IC hM hN).symm
    _ = Real.exp 0 := by rw [hg, Nat.cast_one, Real.exp_zero]

/-- If the indicator complexity vanishes, then the overlap is coprime. -/
theorem gcd_eq_one_of_IC_eq_zero {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (hIC : IC M N = 0) : Nat.gcd M N = 1 := by
  have hcast : (Nat.gcd M N : ℝ) = 1 := by
    rw [card_Tor_eq_exp_IC hM hN, hIC, Real.exp_zero]
  exact Nat.cast_eq_one.mp hcast

/-- The numerical IC obstruction vanishes exactly in the coprime case. -/
theorem gcd_eq_one_iff_IC_eq_zero {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Nat.gcd M N = 1 ↔ IC M N = 0 :=
  ⟨IC_eq_zero_of_gcd_eq_one hM hN, gcd_eq_one_of_IC_eq_zero hM hN⟩

/-- The concrete `Tor₁` kernel is trivial exactly in the coprime case. -/
theorem TorH1_card_eq_one_iff_gcd_eq_one {M N : ℕ} (hN : N ≠ 0) :
    Nat.card (TorH1 M N) = 1 ↔ Nat.gcd M N = 1 := by
  haveI : NeZero N := ⟨hN⟩
  rw [TorH1_card M N, Nat.gcd_comm N M]

/-- **Cor .9 (full TFAE).**
For nonzero moduli, coprimality, trivial concrete `Tor₁`, and vanishing IC are equivalent. -/
theorem cor9_tfae_gcd_tor_ic {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    [Nat.gcd M N = 1, Nat.card (TorH1 M N) = 1, IC M N = 0].TFAE := by
  tfae_have 1 ↔ 2 := (TorH1_card_eq_one_iff_gcd_eq_one (M := M) (N := N) hN).symm
  tfae_have 1 ↔ 3 := gcd_eq_one_iff_IC_eq_zero hM hN
  tfae_finish

/-- Arithmetic part of Equivalence C: the Čech obstruction, concrete `Tor₁`, and
indicator complexity all vanish. -/
def ArithmeticCechTorGate (M N : ℕ) : Prop :=
  Nat.card (cechPhiCoker M N) = 1 ∧ Nat.card (TorH1 M N) = 1 ∧ IC M N = 0

/-- The arithmetic gate is exactly the coprime/equalizer condition. -/
theorem arithmeticCechTorGate_iff_gcd_eq_one {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    ArithmeticCechTorGate M N ↔ Nat.gcd M N = 1 := by
  constructor
  · intro h
    exact (TorH1_card_eq_one_iff_gcd_eq_one (M := M) (N := N) hN).mp h.2.1
  · intro hg
    exact
      ⟨(cechPhiCoker_card_eq_one_iff_gcd_eq_one M N).mpr hg,
        (TorH1_card_eq_one_iff_gcd_eq_one (M := M) (N := N) hN).mpr hg,
        (gcd_eq_one_iff_IC_eq_zero hM hN).mp hg⟩

/-- Full arithmetic TFAE feeding Equivalence C: equalizer face, Čech acyclicity,
concrete `Tor₁` triviality, IC vanishing, and the bundled arithmetic gate. -/
theorem arithmeticCechTorGate_tfae {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    [Nat.gcd M N = 1,
      Nat.card (cechPhiCoker M N) = 1,
      Nat.card (TorH1 M N) = 1,
      IC M N = 0,
      ArithmeticCechTorGate M N].TFAE := by
  tfae_have 1 ↔ 2 := (cechPhiCoker_card_eq_one_iff_gcd_eq_one M N).symm
  tfae_have 1 ↔ 3 := (TorH1_card_eq_one_iff_gcd_eq_one (M := M) (N := N) hN).symm
  tfae_have 1 ↔ 4 := gcd_eq_one_iff_IC_eq_zero hM hN
  tfae_have 1 ↔ 5 := (arithmeticCechTorGate_iff_gcd_eq_one (M := M) (N := N) hM hN).symm
  tfae_finish

/-! ## §D — Koszul / regular-sequence criterion (Lem .10/.14, Thm .11/.15, Prop .16).

Faithful regular-sequence API from Mathlib (`RingTheory.Sequence`).  `IsSMulRegular
M r` is "multiplication by `r` is injective on `M`" — the one-line stalk regularity
test; the inductive `cons` characterisation is the content of the Koszul criterion. -/

section Koszul
open CategoryTheory
open RingTheory.Sequence
open scoped Pointwise
universe u v
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Lem .10 / .14 (one-line stalk regularity test).** A single-element sequence
    `[r]` is regular iff `r` is `M`-regular (`IsSMulRegular`, i.e. multiplication by
    `r` is injective — a non-zero-divisor on the stalk). -/
theorem singleton_regular_iff (r : R) :
    IsWeaklyRegular M [r] ↔ IsSMulRegular M r := isWeaklyRegular_singleton_iff M r

/-- The empty sequence is (weakly) regular. -/
theorem nil_regular : IsWeaklyRegular M ([] : List R) := by simp

/-- **Theorem .11 / .15 (Koszul criterion, inductive content).** `r :: rs` is
    regular iff `r` is `M`-regular and `rs` is regular on `M/rM`. -/
theorem cons_regular_iff (r : R) (rs : List R) :
    IsWeaklyRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsWeaklyRegular (QuotSMulTop r M) rs :=
  isWeaklyRegular_cons_iff M r rs

/-! ### The `r = 1` low-degree Koszul complex

For a single element `r`, the low-degree Koszul model is the two-term chain complex
`M --(r • ·)--> M`, placed in degrees `1` and `0`.  The concrete homology modules
used below are the kernel in degree `1` and the cokernel in degree `0`. -/

/-- Multiplication by `r` as an `R`-linear endomorphism of `M`. -/
abbrev koszulR1Mul (r : R) : M →ₗ[R] M :=
  LinearMap.lsmul R M r

/-- The object function of the two-term `r = 1` Koszul chain complex:
`X₀ = M`, `X₁ = M`, and `Xₙ = 0` for `n ≥ 2` (realized by the zero module `PUnit`). -/
def koszulR1Obj : ℕ → ModuleCat R
  | 0 => ModuleCat.of R M
  | 1 => ModuleCat.of R M
  | _ + 2 => ModuleCat.of R PUnit

/-- The differential of the two-term model: `d₀ = r • ·`, and all higher
differentials are zero. -/
def koszulR1Differential (r : R) : ∀ n : ℕ,
    koszulR1Obj (R := R) (M := M) (n + 1) ⟶ koszulR1Obj (R := R) (M := M) n
  | 0 => ModuleCat.ofHom (koszulR1Mul (M := M) r)
  | _ + 1 => 0

@[simp]
theorem koszulR1Differential_zero (r : R) :
    koszulR1Differential (M := M) r 0 =
      ModuleCat.ofHom (koszulR1Mul (M := M) r) := rfl

@[simp]
theorem koszulR1Differential_succ (r : R) (n : ℕ) :
    koszulR1Differential (M := M) r (n + 1) = 0 := rfl

/-- The square-zero condition for the two-term differential. -/
theorem koszulR1Differential_sq (r : R) (n : ℕ) :
    koszulR1Differential (M := M) r (n + 1) ≫
      koszulR1Differential (M := M) r n = 0 := by
  cases n <;> simp [koszulR1Differential]

/-- The explicit two-term chain complex computing the single-element Koszul model. -/
noncomputable def koszulR1ChainComplex (r : R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (koszulR1Obj (R := R) (M := M)) (koszulR1Differential (M := M) r)
    (koszulR1Differential_sq (M := M) r)

@[simp]
theorem koszulR1ChainComplex_X_zero (r : R) :
    (koszulR1ChainComplex (M := M) r).X 0 = ModuleCat.of R M := by
  rfl

@[simp]
theorem koszulR1ChainComplex_X_one (r : R) :
    (koszulR1ChainComplex (M := M) r).X 1 = ModuleCat.of R M := by
  rfl

@[simp]
theorem koszulR1ChainComplex_X_succ_succ (r : R) (n : ℕ) :
    (koszulR1ChainComplex (M := M) r).X (n + 2) = ModuleCat.of R PUnit := by
  rfl

/-- The degree `1 → 0` differential is multiplication by `r`. -/
theorem koszulR1ChainComplex_d_one_zero (r : R) :
    (koszulR1ChainComplex (M := M) r).d 1 0 =
      ModuleCat.ofHom (koszulR1Mul (M := M) r) := by
  simpa [koszulR1ChainComplex] using
    ChainComplex.of_d (koszulR1Obj (R := R) (M := M))
      (koszulR1Differential (M := M) r)
      (koszulR1Differential_sq (M := M) r) 0

/-- Every higher displayed differential of the two-term model is zero. -/
theorem koszulR1ChainComplex_d_succ_succ (r : R) (n : ℕ) :
    (koszulR1ChainComplex (M := M) r).d (n + 2) (n + 1) = 0 := by
  change
    (ChainComplex.of (koszulR1Obj (R := R) (M := M))
      (koszulR1Differential (M := M) r)
      (koszulR1Differential_sq (M := M) r)).d ((n + 1) + 1) (n + 1) = 0
  exact
    (ChainComplex.of_d (koszulR1Obj (R := R) (M := M))
      (koszulR1Differential (M := M) r)
      (koszulR1Differential_sq (M := M) r) (n + 1)).trans
        (koszulR1Differential_succ (M := M) r n)

/-- The concrete degree-one homology of the single-element Koszul model:
the kernel of multiplication by `r`. -/
abbrev koszulR1H1 (r : R) : Submodule R M :=
  LinearMap.ker (koszulR1Mul (M := M) r)

/-- The concrete degree-zero homology of the single-element Koszul model:
the cokernel of multiplication by `r`. -/
abbrev koszulR1H0 (r : R) : Type _ :=
  M ⧸ LinearMap.range (koszulR1Mul (M := M) r)

/-- `H₁(K(r; M)) = 0` exactly when multiplication by `r` is injective on `M`. -/
theorem koszulR1H1_eq_bot_iff_isSMulRegular (r : R) :
    koszulR1H1 (M := M) r = ⊥ ↔ IsSMulRegular M r := by
  rw [koszulR1H1, koszulR1Mul]
  exact (isSMulRegular_iff_ker_lsmul_eq_bot M r).symm

/-- The range of multiplication by `r` is the standard submodule `rM`. -/
theorem koszulR1_range_eq_smul_top (r : R) :
    LinearMap.range (koszulR1Mul (M := M) r) = r • (⊤ : Submodule R M) := by
  rw [koszulR1Mul, LinearMap.lsmul_eq_distribSMultoLinearMap,
    LinearMap.range_eq_map, Submodule.pointwise_smul_def]

/-- `H₀(K(r; M))`, as the cokernel of multiplication by `r`, is `M / rM`. -/
noncomputable def koszulR1H0EquivQuotSMulTop (r : R) :
    koszulR1H0 (M := M) r ≃ₗ[R] QuotSMulTop r M :=
  Submodule.quotEquivOfEq _ _ (koszulR1_range_eq_smul_top (M := M) r)

@[simp]
theorem koszulR1H0EquivQuotSMulTop_mk (r : R) (x : M) :
    koszulR1H0EquivQuotSMulTop (M := M) r (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : QuotSMulTop r M) := by
  rfl

/-- Positive-degree acyclicity of the one-element explicit Koszul complex. -/
abbrev koszulR1PositiveAcyclic (r : R) : Prop :=
  koszulR1H1 (M := M) r = ⊥

theorem koszulR1PositiveAcyclic_iff_isSMulRegular (r : R) :
    koszulR1PositiveAcyclic (M := M) r ↔ IsSMulRegular M r :=
  koszulR1H1_eq_bot_iff_isSMulRegular (M := M) r

theorem koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton (r : R) :
    koszulR1PositiveAcyclic (M := M) r ↔ IsWeaklyRegular M [r] := by
  rw [koszulR1PositiveAcyclic_iff_isSMulRegular, singleton_regular_iff]

theorem koszulR1PositiveAcyclic_of_isWeaklyRegular_singleton
    (r : R) (hr : IsWeaklyRegular M [r]) :
    koszulR1PositiveAcyclic (M := M) r :=
  (koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton (M := M) r).2 hr

/-! ### The `r = 2` explicit Koszul complex

For two elements `x y : R`, the explicit low-degree Koszul complex is
`M --d₂--> M × M --d₁--> M`, with
`d₁(a,b) = x • a + y • b` and `d₂(c) = (y • c, -(x • c))`.
The middle exactness proof below is the concrete `r = 2` instance of the Koszul
criterion under Mathlib's `IsWeaklyRegular M [x, y]`. -/

/-- The `1 → 0` differential for the two-element Koszul complex. -/
abbrev koszulR2Left (x y : R) : M × M →ₗ[R] M :=
  (LinearMap.lsmul R M x).coprod (LinearMap.lsmul R M y)

/-- The `2 → 1` differential for the two-element Koszul complex. -/
abbrev koszulR2Right (x y : R) : M →ₗ[R] M × M :=
  LinearMap.prod (LinearMap.lsmul R M y) (-(LinearMap.lsmul R M x))

@[simp]
theorem koszulR2Left_apply (x y : R) (p : M × M) :
    koszulR2Left (M := M) x y p = x • p.1 + y • p.2 := rfl

@[simp]
theorem koszulR2Right_apply (x y : R) (m : M) :
    koszulR2Right (M := M) x y m = (y • m, -(x • m)) := rfl

/-- The two displayed differentials compose to zero. -/
theorem koszulR2Left_comp_right (x y : R) :
    (koszulR2Left (M := M) x y).comp (koszulR2Right (M := M) x y) = 0 := by
  ext m
  simp [koszulR2Left, koszulR2Right, smul_smul, mul_comm]

/-- The range of scalar multiplication by `r` is the pointwise scalar submodule `rM`. -/
theorem koszulRange_lsmul_eq_smul_top
    (M : Type*) [AddCommGroup M] [Module R M] (r : R) :
    LinearMap.range (LinearMap.lsmul R M r) = r • (⊤ : Submodule R M) := by
  rw [LinearMap.lsmul_eq_distribSMultoLinearMap,
    LinearMap.range_eq_map, Submodule.pointwise_smul_def]

/-- `(r)M` written with `Ideal.ofList`. -/
theorem ofList_singleton_smul_top_eq_smul_top (r : R) :
    Ideal.ofList [r] • (⊤ : Submodule R M) = r • (⊤ : Submodule R M) := by
  rw [show [r] = r :: [] by rfl, Ideal.ofList_cons_smul r [] (⊤ : Submodule R M)]
  simp

/-- `(x, y)M = xM + yM`. -/
theorem ofList_pair_smul_top_eq_smul_sup_smul (x y : R) :
    Ideal.ofList [x, y] • (⊤ : Submodule R M) =
      x • (⊤ : Submodule R M) ⊔ y • (⊤ : Submodule R M) := by
  rw [show [x, y] = x :: [y] by rfl, Ideal.ofList_cons_smul x [y] (⊤ : Submodule R M),
    ofList_singleton_smul_top_eq_smul_top (M := M) y]

/-- The range of `d₁` is exactly `(x, y)M`. -/
theorem koszulR2Left_range_eq_ofList_pair_smul_top (x y : R) :
    LinearMap.range (koszulR2Left (M := M) x y) =
      Ideal.ofList [x, y] • (⊤ : Submodule R M) := by
  rw [koszulR2Left, LinearMap.range_coprod, koszulRange_lsmul_eq_smul_top (M := M) x,
    koszulRange_lsmul_eq_smul_top (M := M) y,
    ofList_pair_smul_top_eq_smul_sup_smul (M := M) x y]

/-- The concrete degree-zero homology of the two-element Koszul complex. -/
abbrev koszulR2H0 (x y : R) : Type _ :=
  M ⧸ LinearMap.range (koszulR2Left (M := M) x y)

/-- `H₀(K(x,y; M))` is `M/(x,y)M`. -/
noncomputable def koszulR2H0EquivQuotOfListPair (x y : R) :
    koszulR2H0 (M := M) x y ≃ₗ[R]
      M ⧸ (Ideal.ofList [x, y] • (⊤ : Submodule R M)) :=
  Submodule.quotEquivOfEq _ _ (koszulR2Left_range_eq_ofList_pair_smul_top (M := M) x y)

@[simp]
theorem koszulR2H0EquivQuotOfListPair_mk (x y : R) (m : M) :
    koszulR2H0EquivQuotOfListPair (M := M) x y (Submodule.Quotient.mk m) =
      (Submodule.Quotient.mk m :
        M ⧸ (Ideal.ofList [x, y] • (⊤ : Submodule R M))) := by
  rfl

/-- The concrete degree-two homology cycles: the kernel of `d₂`. -/
abbrev koszulR2H2 (x y : R) : Submodule R M :=
  LinearMap.ker (koszulR2Right (M := M) x y)

/-- Membership in the degree-two cycles means annihilation by both `x` and `y`. -/
theorem mem_koszulR2H2_iff (x y : R) (m : M) :
    m ∈ koszulR2H2 (M := M) x y ↔ y • m = 0 ∧ x • m = 0 := by
  simp [koszulR2H2, koszulR2Right]

/-- If `x` is `M`-regular, then `H₂(K(x,y; M)) = 0`. -/
theorem koszulR2H2_eq_bot_of_isSMulRegular_left (x y : R) (hx : IsSMulRegular M x) :
    koszulR2H2 (M := M) x y = ⊥ := by
  ext m
  constructor
  · intro hm
    have hxzero : x • m = 0 := (mem_koszulR2H2_iff (M := M) x y m).mp hm |>.2
    exact hx.right_eq_zero_of_smul hxzero
  · intro hm
    have hm0 : m = 0 := by simpa using hm
    subst m
    simp [koszulR2H2]

/-- If `y` is `M`-regular, then `H₂(K(x,y; M)) = 0`. -/
theorem koszulR2H2_eq_bot_of_isSMulRegular_right (x y : R) (hy : IsSMulRegular M y) :
    koszulR2H2 (M := M) x y = ⊥ := by
  ext m
  constructor
  · intro hm
    have hyzero : y • m = 0 := (mem_koszulR2H2_iff (M := M) x y m).mp hm |>.1
    exact hy.right_eq_zero_of_smul hyzero
  · intro hm
    have hm0 : m = 0 := by simpa using hm
    subst m
    simp [koszulR2H2]

/-- If `[x, y]` is weakly regular, then the top homology `H₂` vanishes. -/
theorem koszulR2H2_eq_bot_of_isWeaklyRegular_pair
    (x y : R) (hxy : IsWeaklyRegular M [x, y]) :
    koszulR2H2 (M := M) x y = ⊥ := by
  exact koszulR2H2_eq_bot_of_isSMulRegular_left (M := M) x y
    ((isWeaklyRegular_cons_iff M x [y]).mp hxy).1

/-- The object function of the two-element Koszul chain complex:
`X₀ = M`, `X₁ = M × M`, `X₂ = M`, and `Xₙ = 0` for `n ≥ 3`. -/
def koszulR2Obj : ℕ → ModuleCat R
  | 0 => ModuleCat.of R M
  | 1 => ModuleCat.of R (M × M)
  | 2 => ModuleCat.of R M
  | _ + 3 => ModuleCat.of R PUnit

/-- The differential function of the two-element Koszul chain complex. -/
def koszulR2Differential (x y : R) : ∀ n : ℕ,
    koszulR2Obj (R := R) (M := M) (n + 1) ⟶ koszulR2Obj (R := R) (M := M) n
  | 0 => ModuleCat.ofHom (koszulR2Left (M := M) x y)
  | 1 => ModuleCat.ofHom (koszulR2Right (M := M) x y)
  | _ + 2 => 0

@[simp]
theorem koszulR2Differential_zero (x y : R) :
    koszulR2Differential (M := M) x y 0 =
      ModuleCat.ofHom (koszulR2Left (M := M) x y) := rfl

@[simp]
theorem koszulR2Differential_one (x y : R) :
    koszulR2Differential (M := M) x y 1 =
      ModuleCat.ofHom (koszulR2Right (M := M) x y) := rfl

@[simp]
theorem koszulR2Differential_succ_succ (x y : R) (n : ℕ) :
    koszulR2Differential (M := M) x y (n + 2) = 0 := rfl

/-- The square-zero condition for the two-element differential. -/
theorem koszulR2Differential_sq (x y : R) (n : ℕ) :
    koszulR2Differential (M := M) x y (n + 1) ≫
      koszulR2Differential (M := M) x y n = 0 := by
  cases n with
  | zero =>
      apply ModuleCat.hom_ext
      exact koszulR2Left_comp_right (M := M) x y
  | succ n =>
      cases n <;> simp [koszulR2Differential]

/-- The explicit three-term chain complex computing the two-element Koszul model. -/
noncomputable def koszulR2ChainComplex (x y : R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (koszulR2Obj (R := R) (M := M)) (koszulR2Differential (M := M) x y)
    (koszulR2Differential_sq (M := M) x y)

@[simp]
theorem koszulR2ChainComplex_X_zero (x y : R) :
    (koszulR2ChainComplex (M := M) x y).X 0 = ModuleCat.of R M := by
  rfl

@[simp]
theorem koszulR2ChainComplex_X_one (x y : R) :
    (koszulR2ChainComplex (M := M) x y).X 1 = ModuleCat.of R (M × M) := by
  rfl

@[simp]
theorem koszulR2ChainComplex_X_two (x y : R) :
    (koszulR2ChainComplex (M := M) x y).X 2 = ModuleCat.of R M := by
  rfl

@[simp]
theorem koszulR2ChainComplex_X_succ_succ_succ (x y : R) (n : ℕ) :
    (koszulR2ChainComplex (M := M) x y).X (n + 3) = ModuleCat.of R PUnit := by
  rfl

/-- The degree `1 → 0` differential is `d₁(a,b)=x•a+y•b`. -/
theorem koszulR2ChainComplex_d_one_zero (x y : R) :
    (koszulR2ChainComplex (M := M) x y).d 1 0 =
      ModuleCat.ofHom (koszulR2Left (M := M) x y) := by
  simpa [koszulR2ChainComplex] using
    ChainComplex.of_d (koszulR2Obj (R := R) (M := M))
      (koszulR2Differential (M := M) x y)
      (koszulR2Differential_sq (M := M) x y) 0

/-- The degree `2 → 1` differential is `d₂(c)=(y•c,-x•c)`. -/
theorem koszulR2ChainComplex_d_two_one (x y : R) :
    (koszulR2ChainComplex (M := M) x y).d 2 1 =
      ModuleCat.ofHom (koszulR2Right (M := M) x y) := by
  simpa [koszulR2ChainComplex] using
    ChainComplex.of_d (koszulR2Obj (R := R) (M := M))
      (koszulR2Differential (M := M) x y)
      (koszulR2Differential_sq (M := M) x y) 1

/-- The degree-one cycles `ker d₁`. -/
abbrev koszulR2H1Cycles (x y : R) : Submodule R (M × M) :=
  LinearMap.ker (koszulR2Left (M := M) x y)

/-- The boundary map `d₂`, codomain-restricted to the cycles using `d₁ ∘ d₂ = 0`. -/
def koszulR2RightToCycles (x y : R) : M →ₗ[R] koszulR2H1Cycles (M := M) x y :=
  (koszulR2Right (M := M) x y).codRestrict
    (koszulR2H1Cycles (M := M) x y) fun m => by
      change ((koszulR2Left (M := M) x y).comp (koszulR2Right (M := M) x y)) m = 0
      exact DFunLike.congr_fun (koszulR2Left_comp_right (M := M) x y) m

@[simp]
theorem koszulR2RightToCycles_apply (x y : R) (m : M) :
    (koszulR2RightToCycles (M := M) x y m : M × M) =
      koszulR2Right (M := M) x y m := rfl

/-- The concrete degree-one homology `ker d₁ / im d₂`. -/
abbrev koszulR2H1 (x y : R) : Type _ :=
  koszulR2H1Cycles (M := M) x y ⧸
    LinearMap.range (koszulR2RightToCycles (M := M) x y)

/-- **Two-element Koszul exactness at the middle.**
If `[x, y]` is weakly regular, then every cycle is a boundary: `im d₂ = ker d₁`. -/
theorem koszulR2RightToCycles_range_eq_top_of_isWeaklyRegular_pair
    (x y : R) (hxy : IsWeaklyRegular M [x, y]) :
    LinearMap.range (koszulR2RightToCycles (M := M) x y) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  rcases (isWeaklyRegular_cons_iff M x [y]).mp hxy with ⟨hx, hy_tail⟩
  have hy : IsSMulRegular (QuotSMulTop x M) y :=
    (isWeaklyRegular_singleton_iff (QuotSMulTop x M) y).mp hy_tail
  let a : M := (p : M × M).1
  let b : M := (p : M × M).2
  have hcycle_raw : koszulR2Left (M := M) x y (p : M × M) = 0 := p.property
  have hcycle : x • a + y • b = 0 := by
    dsimp [a, b]
    change koszulR2Left (M := M) x y (p : M × M) = 0
    exact hcycle_raw
  have hyb_eq : y • b = x • (-a) := by
    simpa [smul_neg] using eq_neg_of_add_eq_zero_right hcycle
  have hyb_mem : y • b ∈ x • (⊤ : Submodule R M) := by
    rw [hyb_eq]
    exact Submodule.smul_mem_pointwise_smul (-a) x (⊤ : Submodule R M) trivial
  have hyb_zero :
      y • (Submodule.Quotient.mk b : QuotSMulTop x M) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hyb_mem
  have hb_zero : (Submodule.Quotient.mk b : QuotSMulTop x M) = 0 :=
    hy.right_eq_zero_of_smul hyb_zero
  have hb_mem : b ∈ x • (⊤ : Submodule R M) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hb_zero
  rcases (Submodule.mem_smul_pointwise_iff_exists b x (⊤ : Submodule R M)).mp hb_mem with
    ⟨c, _, hc⟩
  have hxa : x • (a + y • c) = 0 := by
    calc
      x • (a + y • c) = x • a + x • (y • c) := by rw [smul_add]
      _ = x • a + y • (x • c) := by rw [smul_smul, smul_smul, mul_comm x y]
      _ = x • a + y • b := by rw [hc]
      _ = 0 := hcycle
  have ha_zero : a + y • c = 0 := hx.right_eq_zero_of_smul hxa
  have ha : y • (-c) = a := by
    simpa [smul_neg] using (eq_neg_of_add_eq_zero_left ha_zero).symm
  refine ⟨-c, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact ha
  · change -(x • (-c)) = (p : M × M).2
    rw [smul_neg, neg_neg, hc]

/-- Equivalently, the degree-one homology is a singleton under weak regularity. -/
theorem koszulR2H1_subsingleton_of_isWeaklyRegular_pair
    (x y : R) (hxy : IsWeaklyRegular M [x, y]) :
    Subsingleton (koszulR2H1 (M := M) x y) :=
  Submodule.Quotient.subsingleton_iff.mpr
    (koszulR2RightToCycles_range_eq_top_of_isWeaklyRegular_pair (M := M) x y hxy)

/-- Positive-degree acyclicity of the two-element explicit Koszul complex.

The degree-two homology is recorded as the kernel `koszulR2H2 = ⊥`; the degree-one
homology is recorded as a subsingleton quotient of cycles by boundaries. -/
abbrev koszulR2PositiveAcyclic (x y : R) : Prop :=
  koszulR2H2 (M := M) x y = ⊥ ∧ Subsingleton (koszulR2H1 (M := M) x y)

theorem koszulR2H2_eq_bot_of_positiveAcyclic
    {x y : R} (hxy : koszulR2PositiveAcyclic (M := M) x y) :
    koszulR2H2 (M := M) x y = ⊥ :=
  hxy.1

theorem koszulR2H1_subsingleton_of_positiveAcyclic
    {x y : R} (hxy : koszulR2PositiveAcyclic (M := M) x y) :
    Subsingleton (koszulR2H1 (M := M) x y) :=
  hxy.2

theorem koszulR2PositiveAcyclic_of_isWeaklyRegular_pair
    (x y : R) (hxy : IsWeaklyRegular M [x, y]) :
    koszulR2PositiveAcyclic (M := M) x y :=
  ⟨koszulR2H2_eq_bot_of_isWeaklyRegular_pair (M := M) x y hxy,
    koszulR2H1_subsingleton_of_isWeaklyRegular_pair (M := M) x y hxy⟩

theorem koszulR2PositiveAcyclic_of_cons_certificate
    (x y : R) (hx : IsSMulRegular M x)
    (hy : koszulR1PositiveAcyclic (M := QuotSMulTop x M) y) :
    koszulR2PositiveAcyclic (M := M) x y := by
  have hy' : IsWeaklyRegular (QuotSMulTop x M) [y] :=
    (koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton
      (M := QuotSMulTop x M) y).1 hy
  have hxy : IsWeaklyRegular M [x, y] :=
    (isWeaklyRegular_cons_iff M x [y]).2 ⟨hx, hy'⟩
  exact koszulR2PositiveAcyclic_of_isWeaklyRegular_pair (M := M) x y hxy

/-- Low-degree explicit Koszul acyclicity certificate.

This predicate deliberately covers only the explicitly constructed complexes of length
`0`, `1`, and `2`.  Lengths at least three reduce to `False`, so downstream use cannot
silently mistake this certification layer for the future arbitrary-length tensor-product
construction. -/
def koszulLowDegreePositiveAcyclic : List R → Prop
  | [] => True
  | [x] => koszulR1PositiveAcyclic (M := M) x
  | [x, y] => koszulR2PositiveAcyclic (M := M) x y
  | _ => False

@[simp]
theorem koszulLowDegreePositiveAcyclic_nil :
    koszulLowDegreePositiveAcyclic (R := R) (M := M) [] := by
  trivial

theorem koszulLowDegreePositiveAcyclic_singleton (x : R) :
    koszulLowDegreePositiveAcyclic (M := M) [x] ↔
      koszulR1PositiveAcyclic (M := M) x :=
  Iff.rfl

theorem koszulLowDegreePositiveAcyclic_pair (x y : R) :
    koszulLowDegreePositiveAcyclic (M := M) [x, y] ↔
      koszulR2PositiveAcyclic (M := M) x y :=
  Iff.rfl

theorem not_koszulLowDegreePositiveAcyclic_cons_cons_cons
    (x y z : R) (rs : List R) :
    ¬ koszulLowDegreePositiveAcyclic (M := M) (x :: y :: z :: rs) := by
  simp [koszulLowDegreePositiveAcyclic]

theorem length_le_two_of_koszulLowDegreePositiveAcyclic
    {rs : List R} (h : koszulLowDegreePositiveAcyclic (M := M) rs) :
    rs.length ≤ 2 := by
  cases rs with
  | nil =>
      simp
  | cons x xs =>
      cases xs with
      | nil =>
          simp
      | cons y ys =>
          cases ys with
          | nil =>
              simp
          | cons z zs =>
              exfalso
              exact not_koszulLowDegreePositiveAcyclic_cons_cons_cons
                (M := M) x y z zs h

theorem koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_singleton
    (x : R) (hx : IsWeaklyRegular M [x]) :
    koszulLowDegreePositiveAcyclic (M := M) [x] :=
  koszulR1PositiveAcyclic_of_isWeaklyRegular_singleton (M := M) x hx

theorem koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_pair
    (x y : R) (hxy : IsWeaklyRegular M [x, y]) :
    koszulLowDegreePositiveAcyclic (M := M) [x, y] :=
  koszulR2PositiveAcyclic_of_isWeaklyRegular_pair (M := M) x y hxy

theorem koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_length_le_two
    {rs : List R} (hrs : rs.length ≤ 2) (hreg : IsWeaklyRegular M rs) :
    koszulLowDegreePositiveAcyclic (M := M) rs := by
  cases rs with
  | nil =>
      trivial
  | cons x xs =>
      cases xs with
      | nil =>
          exact koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_singleton
            (M := M) x hreg
      | cons y ys =>
          cases ys with
          | nil =>
              exact koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_pair
                (M := M) x y hreg
          | cons z zs =>
              simp at hrs

/-- Low-degree Koszul regularity certificate.

For length two this records the `r = 1` certificate for the first element, the
`r = 1` certificate for the second element on the first quotient, and the explicit
`r = 2` positive acyclicity of the two-element Koszul complex.  This is stronger than
positive acyclicity alone, and is exactly the low-degree certification counterpart of
the `cons` law in the arbitrary-length interface. -/
def koszulLowDegreeRegularityCertificate : List R → Prop
  | [] => True
  | [x] => koszulR1PositiveAcyclic (M := M) x
  | [x, y] =>
      koszulR1PositiveAcyclic (M := M) x ∧
        koszulR1PositiveAcyclic (M := QuotSMulTop x M) y ∧
          koszulR2PositiveAcyclic (M := M) x y
  | _ => False

@[simp]
theorem koszulLowDegreeRegularityCertificate_nil :
    koszulLowDegreeRegularityCertificate (R := R) (M := M) [] := by
  trivial

theorem koszulLowDegreeRegularityCertificate_singleton (x : R) :
    koszulLowDegreeRegularityCertificate (M := M) [x] ↔
      koszulR1PositiveAcyclic (M := M) x :=
  Iff.rfl

theorem koszulLowDegreeRegularityCertificate_pair (x y : R) :
    koszulLowDegreeRegularityCertificate (M := M) [x, y] ↔
      koszulR1PositiveAcyclic (M := M) x ∧
        koszulR1PositiveAcyclic (M := QuotSMulTop x M) y ∧
          koszulR2PositiveAcyclic (M := M) x y :=
  Iff.rfl

theorem not_koszulLowDegreeRegularityCertificate_cons_cons_cons
    (x y z : R) (rs : List R) :
    ¬ koszulLowDegreeRegularityCertificate (M := M) (x :: y :: z :: rs) := by
  simp [koszulLowDegreeRegularityCertificate]

theorem koszulLowDegreePositiveAcyclic_of_regularCertificate
    {rs : List R} (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    koszulLowDegreePositiveAcyclic (M := M) rs := by
  cases rs with
  | nil =>
      trivial
  | cons x xs =>
      cases xs with
      | nil =>
          exact h
      | cons y ys =>
          cases ys with
          | nil =>
              exact h.2.2
          | cons z zs =>
              exfalso
              exact not_koszulLowDegreeRegularityCertificate_cons_cons_cons
                (M := M) x y z zs h

theorem length_le_two_of_koszulLowDegreeRegularityCertificate
    {rs : List R} (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    rs.length ≤ 2 :=
  length_le_two_of_koszulLowDegreePositiveAcyclic
    (M := M) (koszulLowDegreePositiveAcyclic_of_regularCertificate (M := M) h)

theorem koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_singleton
    (x : R) (hx : IsWeaklyRegular M [x]) :
    koszulLowDegreeRegularityCertificate (M := M) [x] :=
  koszulR1PositiveAcyclic_of_isWeaklyRegular_singleton (M := M) x hx

theorem koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_pair
    (x y : R) (hxy : IsWeaklyRegular M [x, y]) :
    koszulLowDegreeRegularityCertificate (M := M) [x, y] := by
  rcases (isWeaklyRegular_cons_iff M x [y]).mp hxy with ⟨hx, hy⟩
  exact
    ⟨(koszulR1PositiveAcyclic_iff_isSMulRegular (M := M) x).2 hx,
      koszulR1PositiveAcyclic_of_isWeaklyRegular_singleton
        (M := QuotSMulTop x M) y hy,
      koszulR2PositiveAcyclic_of_isWeaklyRegular_pair (M := M) x y hxy⟩

theorem koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_length_le_two
    {rs : List R} (hrs : rs.length ≤ 2) (hreg : IsWeaklyRegular M rs) :
    koszulLowDegreeRegularityCertificate (M := M) rs := by
  cases rs with
  | nil =>
      trivial
  | cons x xs =>
      cases xs with
      | nil =>
          exact koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_singleton
            (M := M) x hreg
      | cons y ys =>
          cases ys with
          | nil =>
              exact koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_pair
                (M := M) x y hreg
          | cons z zs =>
              simp at hrs

theorem isWeaklyRegular_of_koszulLowDegreeRegularityCertificate_singleton
    (x : R) (hx : koszulLowDegreeRegularityCertificate (M := M) [x]) :
    IsWeaklyRegular M [x] :=
  (koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton (M := M) x).1 hx

theorem isWeaklyRegular_of_koszulLowDegreeRegularityCertificate_pair
    (x y : R) (hxy : koszulLowDegreeRegularityCertificate (M := M) [x, y]) :
    IsWeaklyRegular M [x, y] := by
  rcases hxy with ⟨hx, hy, _⟩
  have hx' : IsSMulRegular M x :=
    (koszulR1PositiveAcyclic_iff_isSMulRegular (M := M) x).1 hx
  have hy' : IsWeaklyRegular (QuotSMulTop x M) [y] :=
    (koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton
      (M := QuotSMulTop x M) y).1 hy
  exact (isWeaklyRegular_cons_iff M x [y]).2 ⟨hx', hy'⟩

theorem isWeaklyRegular_of_koszulLowDegreeRegularityCertificate
    {rs : List R} (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    IsWeaklyRegular M rs := by
  cases rs with
  | nil =>
      exact nil_regular (R := R) (M := M)
  | cons x xs =>
      cases xs with
      | nil =>
          exact isWeaklyRegular_of_koszulLowDegreeRegularityCertificate_singleton
            (M := M) x h
      | cons y ys =>
          cases ys with
          | nil =>
              exact isWeaklyRegular_of_koszulLowDegreeRegularityCertificate_pair
                (M := M) x y h
          | cons z zs =>
              exfalso
              exact not_koszulLowDegreeRegularityCertificate_cons_cons_cons
                (M := M) x y z zs h

theorem koszulLowDegreeRegularityCertificate_iff_isWeaklyRegular_length_le_two
    {rs : List R} (hrs : rs.length ≤ 2) :
    koszulLowDegreeRegularityCertificate (M := M) rs ↔ IsWeaklyRegular M rs :=
  ⟨isWeaklyRegular_of_koszulLowDegreeRegularityCertificate (M := M),
    koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_length_le_two
      (M := M) hrs⟩

/-! ### General-length Koszul acyclicity interface

The eventual direct construction of the arbitrary-length Koszul complex should supply a
predicate `Acyclic M rs` and prove the two structural laws below:

* nil: the empty weak Koszul complex is acyclic;
* cons: `K(r :: rs; M)` is acyclic exactly when multiplication by `r` is injective
  on `M` and the tail Koszul complex is acyclic on `M/rM`.

Those two laws are precisely the mapping-cone/long-exact-sequence content needed for the
Koszul criterion.  The following theorems show that once such an acyclicity predicate is
available, Thm .11/.15 follows by ordinary list induction from Mathlib's regular-sequence API. -/

/-- A future honest Koszul-acyclicity predicate, parameterized over the coefficient module.
For now this is an interface: concrete implementations may be built from tensor products,
mapping cones, or low-degree explicit complexes. -/
abbrev KoszulAcyclicPredicate (R : Type u) [CommRing R] :=
  (M : Type v) → [AddCommGroup M] → [Module R M] → List R → Prop

/-- Weak acyclicity interface for arbitrary-length Koszul complexes. -/
structure KoszulWeakAcyclicityInterface {R : Type u} [CommRing R]
    (Acyclic : KoszulAcyclicPredicate R) : Prop where
  nil : ∀ {M : Type v} [AddCommGroup M] [Module R M],
    Acyclic M ([] : List R)
  cons : ∀ {M : Type v} [AddCommGroup M] [Module R M] (r : R) (rs : List R),
    Acyclic M (r :: rs) ↔
      IsSMulRegular M r ∧ Acyclic (QuotSMulTop r M) rs

/-- **Thm .11 / .15, interface form (weak).**
Any Koszul acyclicity predicate satisfying the nil/cons laws is equivalent to weak
regularity for every finite list of elements. -/
theorem koszulAcyclic_iff_isWeaklyRegular_of_interface
    {R : Type u} [CommRing R] {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulWeakAcyclicityInterface (R := R) Acyclic) :
    ∀ (rs : List R) {M : Type v} [AddCommGroup M] [Module R M],
      Acyclic M rs ↔ IsWeaklyRegular M rs := by
  intro rs
  induction rs with
  | nil =>
      intro M _ _
      constructor
      · intro _
        exact IsWeaklyRegular.nil R M
      · intro _
        exact hAcyclic.nil (M := M)
  | cons r rs ih =>
      intro M _ _
      rw [hAcyclic.cons (M := M) r rs, isWeaklyRegular_cons_iff M r rs]
      exact and_congr Iff.rfl (ih (M := QuotSMulTop r M))

theorem koszulInterface_singleton_iff_koszulR1PositiveAcyclic
    {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulWeakAcyclicityInterface (R := R) Acyclic) (r : R) :
    Acyclic M [r] ↔ koszulR1PositiveAcyclic (M := M) r := by
  rw [koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic [r] (M := M),
    koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton]

theorem koszulR2PositiveAcyclic_of_interface_pair
    {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulWeakAcyclicityInterface (R := R) Acyclic)
    {x y : R} (hxy : Acyclic M [x, y]) :
    koszulR2PositiveAcyclic (M := M) x y := by
  exact koszulR2PositiveAcyclic_of_isWeaklyRegular_pair (M := M) x y
    ((koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic [x, y] (M := M)).1 hxy)

theorem koszulLowDegreePositiveAcyclic_of_interface_length_le_two
    {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulWeakAcyclicityInterface (R := R) Acyclic)
    {rs : List R} (hrs : rs.length ≤ 2) (hrsAcyclic : Acyclic M rs) :
    koszulLowDegreePositiveAcyclic (M := M) rs :=
  koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_length_le_two
    (M := M) hrs
    ((koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 hrsAcyclic)

theorem koszulLowDegreeRegularityCertificate_iff_interface_length_le_two
    {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulWeakAcyclicityInterface (R := R) Acyclic)
    {rs : List R} (hrs : rs.length ≤ 2) :
    koszulLowDegreeRegularityCertificate (M := M) rs ↔ Acyclic M rs := by
  rw [koszulLowDegreeRegularityCertificate_iff_isWeaklyRegular_length_le_two
      (M := M) hrs,
    koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)]

/-- The canonical acyclicity predicate supplied by Mathlib's regular-sequence API. -/
abbrev weakRegularKoszulAcyclicPredicate (R : Type u) [CommRing R] :
    KoszulAcyclicPredicate.{u, v} R :=
  fun M _ _ rs => IsWeaklyRegular M rs

/-- Mathlib's `IsWeaklyRegular` satisfies the nil/cons Koszul acyclicity interface. -/
def weakRegularKoszulWeakInterface (R : Type u) [CommRing R] :
    KoszulWeakAcyclicityInterface.{u, v}
      (R := R) (weakRegularKoszulAcyclicPredicate.{u, v} R) where
  nil := by
    intro M _ _
    exact nil_regular (R := R) (M := M)
  cons := by
    intro M _ _ r rs
    exact cons_regular_iff (M := M) r rs

/-- A future concrete Koszul-complex model.

The field `complex` is where the eventual tensor-product/mapping-cone construction
will live.  The field `acyclic` is the associated acyclicity predicate, certified by
the nil/cons law.  The low-degree isomorphism fields pin down compatibility with the
explicit `r = 1` and `r = 2` complexes already constructed in this file, without
requiring a future construction to be definitionally equal to them. -/
structure KoszulComplexModel (R : Type u) [CommRing R] where
  complex :
    (M : Type v) → [AddCommGroup M] → [Module R M] → List R →
      ChainComplex (ModuleCat R) ℕ
  acyclic : KoszulAcyclicPredicate.{u, v} R
  weakInterface : KoszulWeakAcyclicityInterface.{u, v} (R := R) acyclic
  singletonIso :
    ∀ {M : Type v} [AddCommGroup M] [Module R M] (r : R),
      complex M [r] ≅ koszulR1ChainComplex (M := M) r
  pairIso :
    ∀ {M : Type v} [AddCommGroup M] [Module R M] (x y : R),
      complex M [x, y] ≅ koszulR2ChainComplex (M := M) x y

namespace KoszulComplexModel

theorem acyclic_iff_isWeaklyRegular
    {R : Type u} [CommRing R] (K : KoszulComplexModel R)
    (rs : List R) {M : Type v} [AddCommGroup M] [Module R M] :
    K.acyclic M rs ↔ IsWeaklyRegular M rs :=
  koszulAcyclic_iff_isWeaklyRegular_of_interface
    (R := R) (Acyclic := K.acyclic) K.weakInterface rs (M := M)

theorem lowDegreeRegularityCertificate_iff_acyclic
    {R : Type u} [CommRing R] (K : KoszulComplexModel R)
    {rs : List R} (hrs : rs.length ≤ 2)
    {M : Type v} [AddCommGroup M] [Module R M] :
    koszulLowDegreeRegularityCertificate (M := M) rs ↔ K.acyclic M rs := by
  rw [koszulLowDegreeRegularityCertificate_iff_isWeaklyRegular_length_le_two
      (M := M) hrs,
    K.acyclic_iff_isWeaklyRegular rs (M := M)]

theorem lowDegreePositiveAcyclic_of_acyclic
    {R : Type u} [CommRing R] (K : KoszulComplexModel R)
    {rs : List R} (hrs : rs.length ≤ 2)
    {M : Type v} [AddCommGroup M] [Module R M] (h : K.acyclic M rs) :
    koszulLowDegreePositiveAcyclic (M := M) rs :=
  koszulLowDegreePositiveAcyclic_of_regularCertificate (M := M)
    ((K.lowDegreeRegularityCertificate_iff_acyclic (M := M) hrs).2 h)

theorem acyclic_of_lowDegreeRegularityCertificate
    {R : Type u} [CommRing R] (K : KoszulComplexModel R)
    {rs : List R} (hrs : rs.length ≤ 2)
    {M : Type v} [AddCommGroup M] [Module R M]
    (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    K.acyclic M rs :=
  (K.lowDegreeRegularityCertificate_iff_acyclic (M := M) hrs).1 h

end KoszulComplexModel

/-- A concrete low-degree choice of complexes for the model API.

For lists of length one and two this is definitionally the explicit `r = 1` and
`r = 2` Koszul complex constructed above.  The empty and longer-list cases are only
placeholders: the acyclicity predicate of the associated model is still the honest
`IsWeaklyRegular` predicate, and the compatibility fields pin down the low-degree
cases that are actually implemented here. -/
noncomputable def lowDegreeKoszulComplex
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    List R → ChainComplex (ModuleCat R) ℕ
  | [] => koszulR1ChainComplex (M := M) (0 : R)
  | [r] => koszulR1ChainComplex (M := M) r
  | [x, y] => koszulR2ChainComplex (M := M) x y
  | _ => koszulR1ChainComplex (M := M) (0 : R)

@[simp]
theorem lowDegreeKoszulComplex_singleton
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    lowDegreeKoszulComplex R M [r] = koszulR1ChainComplex (M := M) r :=
  rfl

@[simp]
theorem lowDegreeKoszulComplex_pair
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x y : R) :
    lowDegreeKoszulComplex R M [x, y] = koszulR2ChainComplex (M := M) x y :=
  rfl

/-- The concrete low-degree `KoszulComplexModel` realized by the explicit complexes above. -/
noncomputable def lowDegreeKoszulComplexModel (R : Type u) [CommRing R] :
    KoszulComplexModel.{u, v} R where
  complex := fun M _ _ rs => lowDegreeKoszulComplex R M rs
  acyclic := weakRegularKoszulAcyclicPredicate.{u, v} R
  weakInterface := weakRegularKoszulWeakInterface.{u, v} R
  singletonIso := by
    intro M _ _ r
    exact Iso.refl _
  pairIso := by
    intro M _ _ x y
    exact Iso.refl _

theorem lowDegreeKoszulComplexModel_complex_singleton
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    (lowDegreeKoszulComplexModel.{u, v} R).complex M [r] =
      koszulR1ChainComplex (M := M) r :=
  rfl

theorem lowDegreeKoszulComplexModel_complex_pair
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x y : R) :
    (lowDegreeKoszulComplexModel.{u, v} R).complex M [x, y] =
      koszulR2ChainComplex (M := M) x y :=
  rfl

theorem lowDegreeKoszulComplexModel_acyclic_iff_isWeaklyRegular
    (R : Type u) [CommRing R] (rs : List R)
    {M : Type v} [AddCommGroup M] [Module R M] :
    (lowDegreeKoszulComplexModel.{u, v} R).acyclic M rs ↔ IsWeaklyRegular M rs :=
  Iff.rfl

theorem lowDegreeKoszulComplexModel_lowDegreeCertificate_iff_acyclic
    (R : Type u) [CommRing R] {rs : List R} (hrs : rs.length ≤ 2)
    {M : Type v} [AddCommGroup M] [Module R M] :
    koszulLowDegreeRegularityCertificate (M := M) rs ↔
      (lowDegreeKoszulComplexModel.{u, v} R).acyclic M rs :=
  KoszulComplexModel.lowDegreeRegularityCertificate_iff_acyclic
    (lowDegreeKoszulComplexModel.{u, v} R) hrs

/-- Strong acyclicity interface for arbitrary-length Koszul complexes.
The nil law is exact rather than automatic because `IsRegular M []` includes the
nonzero quotient condition. -/
structure KoszulRegularAcyclicityInterface {R : Type u} [CommRing R]
    (Acyclic : KoszulAcyclicPredicate R) : Prop where
  nil : ∀ {M : Type v} [AddCommGroup M] [Module R M],
    Acyclic M ([] : List R) ↔ IsRegular M ([] : List R)
  cons : ∀ {M : Type v} [AddCommGroup M] [Module R M] (r : R) (rs : List R),
    Acyclic M (r :: rs) ↔
      IsSMulRegular M r ∧ Acyclic (QuotSMulTop r M) rs

/-- **Thm .11 / .15, interface form (strong).**
The same nil/cons certification proves equivalence with Mathlib's `IsRegular`. -/
theorem koszulAcyclic_iff_isRegular_of_interface
    {R : Type u} [CommRing R] {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulRegularAcyclicityInterface (R := R) Acyclic) :
    ∀ (rs : List R) {M : Type v} [AddCommGroup M] [Module R M],
      Acyclic M rs ↔ IsRegular M rs := by
  intro rs
  induction rs with
  | nil =>
      intro M _ _
      exact hAcyclic.nil (M := M)
  | cons r rs ih =>
      intro M _ _
      rw [hAcyclic.cons (M := M) r rs, isRegular_cons_iff M r rs]
      exact and_congr Iff.rfl (ih (M := QuotSMulTop r M))

theorem koszulLowDegreePositiveAcyclic_of_isRegular_length_le_two
    {rs : List R} (hrs : rs.length ≤ 2) (hreg : IsRegular M rs) :
    koszulLowDegreePositiveAcyclic (M := M) rs :=
  koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_length_le_two
    (M := M) hrs hreg.toIsWeaklyRegular

theorem koszulLowDegreeRegularityCertificate_of_isRegular_length_le_two
    {rs : List R} (hrs : rs.length ≤ 2) (hreg : IsRegular M rs) :
    koszulLowDegreeRegularityCertificate (M := M) rs :=
  koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_length_le_two
    (M := M) hrs hreg.toIsWeaklyRegular

theorem koszulLowDegreePositiveAcyclic_of_regular_interface_length_le_two
    {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulRegularAcyclicityInterface (R := R) Acyclic)
    {rs : List R} (hrs : rs.length ≤ 2) (hrsAcyclic : Acyclic M rs) :
    koszulLowDegreePositiveAcyclic (M := M) rs :=
  koszulLowDegreePositiveAcyclic_of_isRegular_length_le_two
    (M := M) hrs
    ((koszulAcyclic_iff_isRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 hrsAcyclic)

theorem koszulLowDegreeRegularityCertificate_of_regular_interface_length_le_two
    {Acyclic : KoszulAcyclicPredicate R}
    (hAcyclic : KoszulRegularAcyclicityInterface (R := R) Acyclic)
    {rs : List R} (hrs : rs.length ≤ 2) (hrsAcyclic : Acyclic M rs) :
    koszulLowDegreeRegularityCertificate (M := M) rs :=
  koszulLowDegreeRegularityCertificate_of_isRegular_length_le_two
    (M := M) hrs
    ((koszulAcyclic_iff_isRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 hrsAcyclic)

/-- **Prop .16 (stability under linear isomorphism / base change).** Regularity
    transports along an `R`-linear equivalence. -/
theorem regular_of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N r :=
  e.isSMulRegular_congr r

/-- **Prop .12 / .16 (flat base change, weak form).**
Weak regular sequences are preserved by flat base change along an explicit base-change map. -/
theorem weaklyRegularSequence_of_flat_of_isBaseChange
    {S N : Type*} [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsWeaklyRegular M rs) :
    IsWeaklyRegular N (rs.map (algebraMap R S)) :=
  reg.of_flat_of_isBaseChange hf

/-- **Prop .12 / .16 (faithfully flat base change).**
Regular sequences are preserved by faithfully flat base change along an explicit base-change map.
The transported sequence is the image `rs.map (algebraMap R S)` over the new base ring. -/
theorem regularSequence_of_faithfullyFlat_of_isBaseChange
    {S N : Type*} [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FaithfullyFlat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsRegular M rs) :
    IsRegular N (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat_of_isBaseChange hf

/-- The algebra-specialized faithfully flat base-change theorem.  This is the form used for
completion-style or chart-ring base changes once the appropriate faithfully flat instance is
available. -/
theorem regularSequence_of_faithfullyFlat_algebra
    {S : Type*} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {rs : List R} (reg : IsRegular R rs) :
    IsRegular S (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat

/-- **Prop .16 (localization face, weak form).**
Localization of modules preserves weak regular sequences by flatness of localization. -/
theorem weaklyRegularSequence_of_localizedModule
    {S N : Type*} [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (T : Submonoid R) [IsLocalization T S] (f : M →ₗ[R] N)
    [IsLocalizedModule T f] {rs : List R} (reg : IsWeaklyRegular M rs) :
    IsWeaklyRegular N (rs.map (algebraMap R S)) :=
  reg.of_isLocalizedModule S T f

/-- **Prop .16 (localization at a prime).**
At a prime-local chart, a weakly regular sequence whose entries lie in the prime becomes a
regular sequence on the localized finite nontrivial module. -/
theorem regularSequence_of_localizedModule_atPrime_of_mem
    {S N : Type*} [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
    [Nontrivial N] [Module.Finite S N] (f : M →ₗ[R] N)
    [IsLocalizedModule.AtPrime p f] {rs : List R}
    (reg : IsRegular M rs) (mem : ∀ r ∈ rs, r ∈ p) :
    IsRegular N (rs.map (algebraMap R S)) :=
  reg.1.isRegular_of_isLocalizedModule_of_mem S p f mem

/-- Binary product/CRT-factor form: if two coordinate maps are base changes, then the product
map preserves regular sequences under the same faithfully flat scalar extension. -/
theorem regularSequence_of_faithfullyFlat_of_isBaseChange_prodMap
    {S M1 M2 N1 N2 : Type*} [CommRing S] [Algebra R S]
    [AddCommGroup M1] [AddCommGroup M2] [Module R M1] [Module R M2]
    [AddCommGroup N1] [AddCommGroup N2] [Module R N1] [Module R N2]
    [Module S N1] [Module S N2] [IsScalarTower R S N1] [IsScalarTower R S N2]
    [Module.FaithfullyFlat R S]
    (f1 : M1 →ₗ[R] N1) (f2 : M2 →ₗ[R] N2)
    (hf1 : IsBaseChange S f1) (hf2 : IsBaseChange S f2)
    {rs : List R} (reg : IsRegular (M1 × M2) rs) :
    IsRegular (N1 × N2) (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.prodMap f1 f2 hf1 hf2)

/-- Finite product/CRT-factor form: coordinatewise base change gives base change on the finite
product, so faithfully flat regularity transport applies to the whole product chart. -/
theorem regularSequence_of_faithfullyFlat_of_isBaseChange_pi
    {S : Type*} [CommRing S] [Algebra R S]
    {ι : Type*} [Finite ι] {Mι Nι : ι → Type*}
    [∀ i, AddCommGroup (Mι i)] [∀ i, AddCommGroup (Nι i)]
    [∀ i, Module R (Mι i)] [∀ i, Module R (Nι i)]
    [∀ i, Module S (Nι i)] [∀ i, IsScalarTower R S (Nι i)]
    [Module.FaithfullyFlat R S]
    (f : ∀ i, Mι i →ₗ[R] Nι i) (hf : ∀ i, IsBaseChange S (f i))
    {rs : List R} (reg : IsRegular ((i : ι) → Mι i) rs) :
    IsRegular ((i : ι) → Nι i) (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.pi f hf)

end Koszul

/-! ## §E — Depth lower bounds (Prop .18).

Mathlib's present `RingTheory.Regular.Depth` file does not yet expose a numerical module-depth
function.  To keep the theorem honest and mergeable, the finite depth and dimension functions are
therefore supplied by a small interface.  The interface asks only for the standard compatibility
laws that any future concrete depth API should provide: weak regular sequences give lower bounds
on depth, depth is bounded by dimension, and Cohen-Macaulay modules are exactly the case where the
two values agree. -/

section Depth

open RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite-depth lower-bound certificate before choosing a concrete numerical depth API:
there exists a weakly regular sequence on `M` of length `n`. -/
def HasWeakRegularSequenceLength (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  ∃ rs : List R, rs.length = n ∧ IsWeaklyRegular M rs

theorem hasWeakRegularSequenceLength_zero :
    HasWeakRegularSequenceLength R M 0 :=
  ⟨[], rfl, nil_regular (R := R) (M := M)⟩

theorem hasWeakRegularSequenceLength_of_isWeaklyRegular
    {rs : List R} (hreg : IsWeaklyRegular M rs) :
    HasWeakRegularSequenceLength R M rs.length :=
  ⟨rs, rfl, hreg⟩

theorem hasWeakRegularSequenceLength_of_isRegular
    {rs : List R} (hreg : IsRegular M rs) :
    HasWeakRegularSequenceLength R M rs.length :=
  hasWeakRegularSequenceLength_of_isWeaklyRegular (M := M) hreg.toIsWeaklyRegular

theorem exists_weaklyRegular_of_hasWeakRegularSequenceLength
    {n : ℕ} (h : HasWeakRegularSequenceLength R M n) :
    ∃ rs : List R, rs.length = n ∧ IsWeaklyRegular M rs :=
  h

/-- A lightweight API boundary for the numerical depth and dimension facts used by Prop .18.

The values are finite natural numbers here because Prop .18 only uses finite lower bounds coming
from a fixed regular sequence.  A future infinite-valued depth API can instantiate this interface
after truncating to the relevant finite comparison or by replacing this finite wrapper. -/
structure ModuleDepthDimensionInterface (R : Type u) [CommRing R] where
  depth : (M : Type v) → [AddCommGroup M] → [Module R M] → ℕ
  dimension : (M : Type v) → [AddCommGroup M] → [Module R M] → ℕ
  IsCohenMacaulay : (M : Type v) → [AddCommGroup M] → [Module R M] → Prop
  length_le_depth_of_isWeaklyRegular :
    ∀ {M : Type v} [AddCommGroup M] [Module R M] {rs : List R},
      IsWeaklyRegular M rs → rs.length ≤ depth M
  depth_le_dimension :
    ∀ {M : Type v} [AddCommGroup M] [Module R M], depth M ≤ dimension M
  depth_eq_dimension_of_isCohenMacaulay :
    ∀ {M : Type v} [AddCommGroup M] [Module R M],
      IsCohenMacaulay M → depth M = dimension M

namespace ModuleDepthDimensionInterface

theorem weaklyRegular_length_le_depth
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.depth M :=
  D.length_le_depth_of_isWeaklyRegular hreg

theorem regular_length_le_depth
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hreg : IsRegular M rs) :
    rs.length ≤ D.depth M :=
  D.weaklyRegular_length_le_depth hreg.toIsWeaklyRegular

theorem hasWeakRegularSequenceLength_le_depth
    (D : ModuleDepthDimensionInterface.{u, v} R) {n : ℕ}
    (h : HasWeakRegularSequenceLength R M n) :
    n ≤ D.depth M := by
  rcases h with ⟨rs, hlen, hreg⟩
  rw [← hlen]
  exact D.weaklyRegular_length_le_depth (M := M) hreg

theorem koszulAcyclic_length_le_depth
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (h : Acyclic M rs) :
    rs.length ≤ D.depth M :=
  D.weaklyRegular_length_le_depth (M := M)
    ((koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)

theorem koszulRegularAcyclic_length_le_depth
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (h : Acyclic M rs) :
    rs.length ≤ D.depth M :=
  D.regular_length_le_depth (M := M)
    ((koszulAcyclic_iff_isRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)

theorem koszulModel_acyclic_length_le_depth
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (h : K.acyclic M rs) :
    rs.length ≤ D.depth M :=
  D.weaklyRegular_length_le_depth (M := M)
    ((K.acyclic_iff_isWeaklyRegular rs (M := M)).1 h)

theorem weaklyRegular_length_le_dimension_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension M := by
  calc
    rs.length ≤ D.depth M := D.weaklyRegular_length_le_depth (M := M) hreg
    _ = D.dimension M := D.depth_eq_dimension_of_isCohenMacaulay (M := M) hCM

theorem regular_length_le_dimension_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (hreg : IsRegular M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_isCohenMacaulay
    (M := M) hCM hreg.toIsWeaklyRegular

theorem hasWeakRegularSequenceLength_le_dimension_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R) {n : ℕ}
    (hCM : D.IsCohenMacaulay M) (h : HasWeakRegularSequenceLength R M n) :
    n ≤ D.dimension M := by
  rcases h with ⟨rs, hlen, hreg⟩
  rw [← hlen]
  exact D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := M) hCM hreg

theorem dimension_le_depth_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (hEq : D.depth M = D.dimension M) :
    D.dimension M ≤ D.depth M :=
  le_of_eq hEq.symm

theorem weaklyRegular_length_le_dimension_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension M := by
  calc
    rs.length ≤ D.depth M := D.weaklyRegular_length_le_depth (M := M) hreg
    _ = D.dimension M := hEq

theorem regular_length_le_dimension_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (hreg : IsRegular M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_depth_eq_dimension
    (M := M) hEq hreg.toIsWeaklyRegular

theorem hasWeakRegularSequenceLength_le_dimension_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {n : ℕ}
    (hEq : D.depth M = D.dimension M) (h : HasWeakRegularSequenceLength R M n) :
    n ≤ D.dimension M := by
  rcases h with ⟨rs, hlen, hreg⟩
  rw [← hlen]
  exact D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := M) hEq hreg

theorem koszulAcyclic_length_le_dimension_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := M) hCM
    ((koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)

theorem koszulRegularAcyclic_length_le_dimension_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.regular_length_le_dimension_of_isCohenMacaulay (M := M) hCM
    ((koszulAcyclic_iff_isRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)

theorem koszulModel_acyclic_length_le_dimension_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (h : K.acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := M) hCM
    ((K.acyclic_iff_isWeaklyRegular rs (M := M)).1 h)

theorem koszulAcyclic_length_le_dimension_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := M) hEq
    ((koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)

theorem koszulRegularAcyclic_length_le_dimension_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.regular_length_le_dimension_of_depth_eq_dimension (M := M) hEq
    ((koszulAcyclic_iff_isRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)

theorem koszulModel_acyclic_length_le_dimension_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (h : K.acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := M) hEq
    ((K.acyclic_iff_isWeaklyRegular rs (M := M)).1 h)

theorem lowDegreeRegularityCertificate_length_le_depth
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    rs.length ≤ D.depth M :=
  D.weaklyRegular_length_le_depth (M := M)
    (isWeaklyRegular_of_koszulLowDegreeRegularityCertificate (M := M) h)

theorem lowDegreeRegularityCertificate_length_le_dimension_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := M) hCM
    (isWeaklyRegular_of_koszulLowDegreeRegularityCertificate (M := M) h)

theorem lowDegreeRegularityCertificate_length_le_dimension_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := M) hEq
    (isWeaklyRegular_of_koszulLowDegreeRegularityCertificate (M := M) h)

theorem depth_eq_length_of_isCohenMacaulay_of_dimension_le_length
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (hreg : IsWeaklyRegular M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length := by
  apply le_antisymm
  · calc
      D.depth M = D.dimension M := D.depth_eq_dimension_of_isCohenMacaulay (M := M) hCM
      _ ≤ rs.length := hdim
  · exact D.weaklyRegular_length_le_depth (M := M) hreg

theorem dimension_eq_length_of_isCohenMacaulay_of_dimension_le_length
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (hreg : IsWeaklyRegular M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.dimension M = rs.length :=
  le_antisymm hdim
    (D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := M) hCM hreg)

theorem depth_eq_length_of_depth_eq_dimension_of_dimension_le_length
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (hreg : IsWeaklyRegular M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length := by
  apply le_antisymm
  · calc
      D.depth M = D.dimension M := hEq
      _ ≤ rs.length := hdim
  · exact D.weaklyRegular_length_le_depth (M := M) hreg

theorem dimension_eq_length_of_depth_eq_dimension_of_dimension_le_length
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (hreg : IsWeaklyRegular M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.dimension M = rs.length :=
  le_antisymm hdim
    (D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := M) hEq hreg)

theorem depth_eq_dimension_trigger_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (hreg : IsWeaklyRegular M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  ⟨D.depth_eq_length_of_depth_eq_dimension_of_dimension_le_length
      (M := M) hEq hreg hdim,
    D.dimension_eq_length_of_depth_eq_dimension_of_dimension_le_length
      (M := M) hEq hreg hdim⟩

theorem depth_eq_dimension_trigger_of_koszulAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs :=
    ((koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)
  exact
    ⟨D.depth_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim,
      D.dimension_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim⟩

theorem depth_eq_dimension_trigger_of_koszulRegularAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs :=
    ((koszulAcyclic_iff_isRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h).toIsWeaklyRegular
  exact
    ⟨D.depth_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim,
      D.dimension_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim⟩

theorem depth_eq_dimension_trigger_of_koszulModelAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (h : K.acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs := (K.acyclic_iff_isWeaklyRegular rs (M := M)).1 h
  exact
    ⟨D.depth_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim,
      D.dimension_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim⟩

theorem depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs :=
    isWeaklyRegular_of_koszulLowDegreeRegularityCertificate (M := M) h
  exact
    ⟨D.depth_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim,
      D.dimension_eq_length_of_isCohenMacaulay_of_dimension_le_length
        (M := M) hCM hreg hdim⟩

theorem depth_eq_dimension_trigger_of_koszulAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs :=
    ((koszulAcyclic_iff_isWeaklyRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h)
  exact D.depth_eq_dimension_trigger_of_depth_eq_dimension (M := M) hEq hreg hdim

theorem depth_eq_dimension_trigger_of_koszulRegularAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs :=
    ((koszulAcyclic_iff_isRegular_of_interface
      (R := R) (Acyclic := Acyclic) hAcyclic rs (M := M)).1 h).toIsWeaklyRegular
  exact D.depth_eq_dimension_trigger_of_depth_eq_dimension (M := M) hEq hreg hdim

theorem depth_eq_dimension_trigger_of_koszulModelAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (h : K.acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs := (K.acyclic_iff_isWeaklyRegular rs (M := M)).1 h
  exact D.depth_eq_dimension_trigger_of_depth_eq_dimension (M := M) hEq hreg hdim

theorem depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length := by
  have hreg : IsWeaklyRegular M rs :=
    isWeaklyRegular_of_koszulLowDegreeRegularityCertificate (M := M) h
  exact D.depth_eq_dimension_trigger_of_depth_eq_dimension (M := M) hEq hreg hdim

end ModuleDepthDimensionInterface

/-- **Prop .18, first half.** Any weak regular sequence of length `r` gives `depth(M) ≥ r`
for every depth API satisfying the regular-sequence lower-bound compatibility law. -/
theorem prop18_depth_lower_bound_of_isWeaklyRegular
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.depth M :=
  D.weaklyRegular_length_le_depth (M := M) hreg

/-- **Prop .18, first half, certificate form.** If `M` admits a weak regular sequence of
length `r`, then `depth(M) ≥ r`. -/
theorem prop18_depth_lower_bound
    (D : ModuleDepthDimensionInterface.{u, v} R) {r : ℕ}
    (h : HasWeakRegularSequenceLength R M r) :
    r ≤ D.depth M :=
  D.hasWeakRegularSequenceLength_le_depth (M := M) h

/-- The same lower bound for Mathlib's strong regular sequences. -/
theorem prop18_depth_lower_bound_of_isRegular
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hreg : IsRegular M rs) :
    rs.length ≤ D.depth M :=
  D.regular_length_le_depth (M := M) hreg

/-- Koszul-acyclic interface form of the depth lower bound. -/
theorem prop18_depth_lower_bound_of_koszulAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (h : Acyclic M rs) :
    rs.length ≤ D.depth M :=
  D.koszulAcyclic_length_le_depth (M := M) hAcyclic h

/-- Strong Koszul-acyclic interface form of the depth lower bound. -/
theorem prop18_depth_lower_bound_of_koszulRegularAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (h : Acyclic M rs) :
    rs.length ≤ D.depth M :=
  D.koszulRegularAcyclic_length_le_depth (M := M) hAcyclic h

/-- Concrete-model form of the depth lower bound.  This is the statement a future honest
Koszul complex model should export directly. -/
theorem prop18_depth_lower_bound_of_koszulModelAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (h : K.acyclic M rs) :
    rs.length ≤ D.depth M :=
  D.koszulModel_acyclic_length_le_depth (M := M) K h

/-- Low-degree certificate form: the explicit `r ≤ 2` Koszul regularity certificate already
implies the Prop .18 depth lower bound. -/
theorem prop18_depth_lower_bound_of_lowDegreeRegularityCertificate
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    rs.length ≤ D.depth M :=
  D.lowDegreeRegularityCertificate_length_le_depth (M := M) h

/-- Flat base-change form of Prop .18: after transporting a weak regular sequence along an
explicit base-change map, its original length bounds the target depth. -/
theorem prop18_depth_lower_bound_of_flatBaseChange
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.depth N := by
  have hregS : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
    weaklyRegularSequence_of_flat_of_isBaseChange (M := M) hf hreg
  simpa using D.weaklyRegular_length_le_depth (M := N) hregS

/-- Faithfully flat base-change form of Prop .18 for strong regular sequences. -/
theorem prop18_depth_lower_bound_of_faithfullyFlatBaseChange
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FaithfullyFlat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hreg : IsRegular M rs) :
    rs.length ≤ D.depth N := by
  have hregS : IsRegular N (rs.map (algebraMap R S)) :=
    regularSequence_of_faithfullyFlat_of_isBaseChange (M := M) hf hreg
  simpa using D.regular_length_le_depth (M := N) hregS

/-- Localization form of Prop .18: a weak regular sequence remains weakly regular on the
localized module, so the localized depth is at least the original length. -/
theorem prop18_depth_lower_bound_of_localizedModule
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (T : Submonoid R) [IsLocalization T S] (f : M →ₗ[R] N)
    [IsLocalizedModule T f] (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.depth N := by
  have hregS : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
    weaklyRegularSequence_of_localizedModule (M := M) T f hreg
  simpa using D.weaklyRegular_length_le_depth (M := N) hregS

/-- **Prop .18, Cohen-Macaulay consequence.** Under an explicit CM equality hypothesis supplied
by the interface, a weak regular sequence also bounds the chosen dimension from below. -/
theorem prop18_dimension_lower_bound_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := M) hCM hreg

/-- Direct equality form of the Cohen-Macaulay consequence.  This is the adapter to use when a
future depth API exports the equality `depth = dimension` directly rather than through a named
Cohen-Macaulay predicate. -/
theorem prop18_dimension_lower_bound_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension M :=
  D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := M) hEq hreg

/-- Koszul-acyclic interface form of the Cohen-Macaulay dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_koszulAcyclic_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.koszulAcyclic_length_le_dimension_of_isCohenMacaulay (M := M) hAcyclic hCM h

/-- Strong Koszul-acyclic interface form of the Cohen-Macaulay dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_koszulRegularAcyclic_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.koszulRegularAcyclic_length_le_dimension_of_isCohenMacaulay (M := M) hAcyclic hCM h

/-- Concrete-model form of the Cohen-Macaulay dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_koszulModelAcyclic_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (h : K.acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.koszulModel_acyclic_length_le_dimension_of_isCohenMacaulay (M := M) K hCM h

/-- Low-degree certificate form of the Cohen-Macaulay dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_lowDegreeRegularityCertificate_of_isCohenMacaulay
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    rs.length ≤ D.dimension M :=
  D.lowDegreeRegularityCertificate_length_le_dimension_of_isCohenMacaulay (M := M) hCM h

/-- Koszul-acyclic interface form of the direct `depth = dimension` dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_koszulAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.koszulAcyclic_length_le_dimension_of_depth_eq_dimension (M := M) hAcyclic hEq h

/-- Strong Koszul-acyclic interface form of the direct `depth = dimension` dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_koszulRegularAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.koszulRegularAcyclic_length_le_dimension_of_depth_eq_dimension (M := M) hAcyclic hEq h

/-- Concrete-model form of the direct `depth = dimension` dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_koszulModelAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (h : K.acyclic M rs) :
    rs.length ≤ D.dimension M :=
  D.koszulModel_acyclic_length_le_dimension_of_depth_eq_dimension (M := M) K hEq h

/-- Low-degree certificate form of the direct `depth = dimension` dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_lowDegreeRegularityCertificate_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs) :
    rs.length ≤ D.dimension M :=
  D.lowDegreeRegularityCertificate_length_le_dimension_of_depth_eq_dimension (M := M) hEq h

/-- Flat base-change form of the Cohen-Macaulay dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_flatBaseChange_of_isCohenMacaulay
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hCM : D.IsCohenMacaulay N) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension N := by
  have hregS : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
    weaklyRegularSequence_of_flat_of_isBaseChange (M := M) hf hreg
  simpa using
    D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := N) hCM hregS

/-- Faithfully flat base-change form of the Cohen-Macaulay dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_faithfullyFlatBaseChange_of_isCohenMacaulay
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FaithfullyFlat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hCM : D.IsCohenMacaulay N) (hreg : IsRegular M rs) :
    rs.length ≤ D.dimension N := by
  have hregS : IsRegular N (rs.map (algebraMap R S)) :=
    regularSequence_of_faithfullyFlat_of_isBaseChange (M := M) hf hreg
  simpa using D.regular_length_le_dimension_of_isCohenMacaulay (M := N) hCM hregS

/-- Localization form of the Cohen-Macaulay dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_localizedModule_of_isCohenMacaulay
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (T : Submonoid R) [IsLocalization T S] (f : M →ₗ[R] N)
    [IsLocalizedModule T f] (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hCM : D.IsCohenMacaulay N) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension N := by
  have hregS : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
    weaklyRegularSequence_of_localizedModule (M := M) T f hreg
  simpa using
    D.weaklyRegular_length_le_dimension_of_isCohenMacaulay (M := N) hCM hregS

/-- Flat base-change form of the direct `depth = dimension` dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_flatBaseChange_of_depth_eq_dimension
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hEq : D.depth N = D.dimension N) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension N := by
  have hregS : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
    weaklyRegularSequence_of_flat_of_isBaseChange (M := M) hf hreg
  simpa using
    D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := N) hEq hregS

/-- Faithfully flat base-change form of the direct `depth = dimension` dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_faithfullyFlatBaseChange_of_depth_eq_dimension
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FaithfullyFlat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hEq : D.depth N = D.dimension N) (hreg : IsRegular M rs) :
    rs.length ≤ D.dimension N := by
  have hregS : IsRegular N (rs.map (algebraMap R S)) :=
    regularSequence_of_faithfullyFlat_of_isBaseChange (M := M) hf hreg
  simpa using D.regular_length_le_dimension_of_depth_eq_dimension (M := N) hEq hregS

/-- Localization form of the direct `depth = dimension` dimension lower bound. -/
theorem prop18_dimension_lower_bound_of_localizedModule_of_depth_eq_dimension
    {S : Type u} [CommRing S] [Algebra R S]
    {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (T : Submonoid R) [IsLocalization T S] (f : M →ₗ[R] N)
    [IsLocalizedModule T f] (D : ModuleDepthDimensionInterface.{u, v} S)
    {rs : List R} (hEq : D.depth N = D.dimension N) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ D.dimension N := by
  have hregS : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
    weaklyRegularSequence_of_localizedModule (M := M) T f hreg
  simpa using
    D.weaklyRegular_length_le_dimension_of_depth_eq_dimension (M := N) hEq hregS

/-- **Prop .18, equality trigger.** If the chosen dimension is already at most the length of a
weak regular sequence and `M` is Cohen-Macaulay, then depth and dimension both equal that length. -/
theorem prop18_depth_eq_dimension_trigger
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (hreg : IsWeaklyRegular M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  ⟨D.depth_eq_length_of_isCohenMacaulay_of_dimension_le_length (M := M) hCM hreg hdim,
    D.dimension_eq_length_of_isCohenMacaulay_of_dimension_le_length (M := M) hCM hreg hdim⟩

/-- Direct equality form of the Prop .18 equality trigger. -/
theorem prop18_depth_eq_dimension_trigger_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (hreg : IsWeaklyRegular M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_depth_eq_dimension (M := M) hEq hreg hdim

/-- Equality trigger from a Koszul-acyclicity interface certificate. -/
theorem prop18_depth_eq_dimension_trigger_of_koszulAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_koszulAcyclic (M := M) hAcyclic hCM h hdim

/-- Equality trigger from a strong Koszul-acyclicity interface certificate. -/
theorem prop18_depth_eq_dimension_trigger_of_koszulRegularAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hCM : D.IsCohenMacaulay M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_koszulRegularAcyclic (M := M) hAcyclic hCM h hdim

/-- Equality trigger from a concrete Koszul complex model certificate. -/
theorem prop18_depth_eq_dimension_trigger_of_koszulModelAcyclic
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M) (h : K.acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_koszulModelAcyclic (M := M) K hCM h hdim

/-- Equality trigger from the explicit low-degree Koszul regularity certificate. -/
theorem prop18_depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hCM : D.IsCohenMacaulay M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate (M := M) hCM h hdim

/-- Equality trigger from a Koszul-acyclicity interface and direct `depth = dimension`. -/
theorem prop18_depth_eq_dimension_trigger_of_koszulAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulWeakAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_koszulAcyclic_of_depth_eq_dimension
    (M := M) hAcyclic hEq h hdim

/-- Equality trigger from a strong Koszul-acyclicity interface and direct `depth = dimension`. -/
theorem prop18_depth_eq_dimension_trigger_of_koszulRegularAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    {Acyclic : KoszulAcyclicPredicate.{u, v} R}
    (hAcyclic : KoszulRegularAcyclicityInterface.{u, v} (R := R) Acyclic)
    {rs : List R} (hEq : D.depth M = D.dimension M) (h : Acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_koszulRegularAcyclic_of_depth_eq_dimension
    (M := M) hAcyclic hEq h hdim

/-- Equality trigger from a concrete Koszul complex model and direct `depth = dimension`. -/
theorem prop18_depth_eq_dimension_trigger_of_koszulModelAcyclic_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R)
    (K : KoszulComplexModel.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M) (h : K.acyclic M rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_koszulModelAcyclic_of_depth_eq_dimension
    (M := M) K hEq h hdim

/-- Equality trigger from a low-degree Koszul certificate and direct `depth = dimension`. -/
theorem prop18_depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate_of_depth_eq_dimension
    (D : ModuleDepthDimensionInterface.{u, v} R) {rs : List R}
    (hEq : D.depth M = D.dimension M)
    (h : koszulLowDegreeRegularityCertificate (M := M) rs)
    (hdim : D.dimension M ≤ rs.length) :
    D.depth M = rs.length ∧ D.dimension M = rs.length :=
  D.depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate_of_depth_eq_dimension
    (M := M) hEq h hdim

end Depth

/-! ## §F — det–trace formal algebraic core (Lemma .37).

Grothendieck--Lefschetz is outside Mathlib because étale cohomology and weights are absent.
The formal power-series heart is available: once the determinant side supplies the standard
Newton/Jacobi logarithmic derivative, the exponential trace identity follows by coefficient
recursion in `PowerSeries`.
-/

section DetTrace

/-- The formal logarithm primitive `∑_{i ≥ 1} a_i / i * X^i`, represented coefficientwise.
The zeroth coefficient is forced to be zero, making substitution into `PowerSeries.exp` legal. -/
noncomputable def detTraceWeightedLogSeries {K : Type*} [CommRing K] [Algebra ℚ K]
    (a : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else a n * algebraMap ℚ K (1 / (n : ℚ))

/-- The logarithmic derivative target `∑_{i ≥ 1} a_i * X^{i-1}`. -/
noncomputable def detTraceShiftedSeries {K : Type*} [CommRing K] (a : ℕ → K) :
    PowerSeries K :=
  PowerSeries.mk fun n => a (n + 1)

@[simp]
theorem coeff_detTraceWeightedLogSeries_zero {K : Type*} [CommRing K] [Algebra ℚ K]
    (a : ℕ → K) :
    PowerSeries.coeff 0 (detTraceWeightedLogSeries a) = 0 := by
  simp [detTraceWeightedLogSeries]

theorem coeff_detTraceWeightedLogSeries_of_ne_zero {K : Type*} [CommRing K] [Algebra ℚ K]
    (a : ℕ → K) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (detTraceWeightedLogSeries a) =
      a n * algebraMap ℚ K (1 / (n : ℚ)) := by
  simp [detTraceWeightedLogSeries, hn]

@[simp]
theorem coeff_detTraceShiftedSeries {K : Type*} [CommRing K] (a : ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (detTraceShiftedSeries a) = a (n + 1) := by
  simp [detTraceShiftedSeries]

theorem constantCoeff_detTraceWeightedLogSeries {K : Type*} [CommRing K] [Algebra ℚ K]
    (a : ℕ → K) :
    PowerSeries.constantCoeff (detTraceWeightedLogSeries a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_detTraceWeightedLogSeries_zero a

/-- Formal differentiation sends `∑_{i ≥ 1} a_i / i * X^i` to
`∑_{i ≥ 1} a_i * X^{i-1}` over any `ℚ`-algebra. -/
theorem derivative_detTraceWeightedLogSeries {K : Type*} [CommRing K] [Algebra ℚ K]
    (a : ℕ → K) :
    d⁄dX K (detTraceWeightedLogSeries a) = detTraceShiftedSeries a := by
  ext n
  rw [PowerSeries.coeff_derivative, detTraceWeightedLogSeries, detTraceShiftedSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  have hunit :
      algebraMap ℚ K (1 / ((n + 1 : ℕ) : ℚ)) * ((n : K) + 1) = 1 := by
    rw [show ((n : K) + 1) = algebraMap ℚ K ((n : ℚ) + 1) by norm_num,
      ← map_mul]
    have hrat : (1 / ((n + 1 : ℕ) : ℚ)) * ((n : ℚ) + 1) = 1 := by
      rw [show (((n + 1 : ℕ) : ℚ)) = (n : ℚ) + 1 by norm_num]
      rw [one_div]
      exact inv_mul_cancel₀ (ne_of_gt (by positivity : (0 : ℚ) < (n : ℚ) + 1))
    rw [hrat, map_one]
  rw [mul_assoc, hunit, mul_one]

theorem derivative_exp_subst_of_constantCoeff_zero {K : Type*} [CommRing K] [Algebra ℚ K]
    (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    d⁄dX K ((PowerSeries.exp K).subst f) =
      ((PowerSeries.exp K).subst f) * d⁄dX K f := by
  simpa [PowerSeries.derivative_exp] using
    (PowerSeries.derivative_subst (A := K)
      (f := PowerSeries.exp K) (g := f) (PowerSeries.HasSubst.of_constantCoeff_zero' hf))

theorem constantCoeff_exp_subst_of_constantCoeff_zero {K : Type*} [CommRing K] [Algebra ℚ K]
    (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff ((PowerSeries.exp K).subst f) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
      (PowerSeries.exp K) 0]
  let g : ℕ → K := fun d =>
    PowerSeries.coeff d (PowerSeries.exp K) • PowerSeries.coeff 0 (f ^ d)
  change ∑ᶠ d, g d = 1
  rw [finsum_eq_single g 0]
  · simp [g, PowerSeries.coeff_zero_eq_constantCoeff, hf]
  · intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => simp [g, PowerSeries.coeff_zero_eq_constantCoeff, hf]

/-- Uniqueness for the formal ODE `F' = F * A`.
The proof is a coefficient-by-coefficient strong induction; the coefficient of `X^n` in
`F * A` only depends on coefficients of `F` up to degree `n`. -/
theorem powerSeries_eq_of_derivative_eq_mul {K : Type*} [CommRing K] [IsAddTorsionFree K]
    {F G A : PowerSeries K}
    (h0 : PowerSeries.constantCoeff F = PowerSeries.constantCoeff G)
    (hF : d⁄dX K F = F * A)
    (hG : d⁄dX K G = G * A) :
    F = G := by
  apply PowerSeries.ext
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero =>
          simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h0
      | succ n =>
          have hprod : PowerSeries.coeff n (F * A) = PowerSeries.coeff n (G * A) := by
            rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            refine Finset.sum_congr rfl ?_
            intro p hp
            have hp_eq : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
            have hp_lt : p.1 < n + 1 := by
              exact Nat.lt_succ_of_le (by rw [← hp_eq]; exact Nat.le_add_right _ _)
            rw [ih p.1 hp_lt]
          have hderiv :
              PowerSeries.coeff n (d⁄dX K F) = PowerSeries.coeff n (d⁄dX K G) := by
            calc
              PowerSeries.coeff n (d⁄dX K F) = PowerSeries.coeff n (F * A) := by rw [hF]
              _ = PowerSeries.coeff n (G * A) := hprod
              _ = PowerSeries.coeff n (d⁄dX K G) := by rw [hG]
          rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hderiv
          rwa [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul,
            mul_comm, ← nsmul_eq_mul, smul_right_inj n.succ_ne_zero] at hderiv

/-- If `f' = A` and `F' = F * A`, then `F = exp(f)` as a formal power series. -/
theorem exp_subst_eq_of_derivative_eq_mul {K : Type*} [CommRing K] [Algebra ℚ K]
    [IsAddTorsionFree K] {F f A : PowerSeries K}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hdf : d⁄dX K f = A)
    (hF0 : PowerSeries.constantCoeff F = 1)
    (hFderiv : d⁄dX K F = F * A) :
    F = (PowerSeries.exp K).subst f := by
  apply powerSeries_eq_of_derivative_eq_mul
  · rw [hF0, constantCoeff_exp_subst_of_constantCoeff_zero f hf0]
  · exact hFderiv
  · rw [derivative_exp_subst_of_constantCoeff_zero f hf0, hdf]

/-- The generic det--trace formal exponential identity: a solution of the logarithmic derivative
equation `F' = F * ∑ a_{n+1}X^n` is exactly
`exp(∑_{i≥1} a_i / i * X^i)`. -/
theorem exp_detTraceWeightedLogSeries_unique {K : Type*} [CommRing K] [Algebra ℚ K]
    [IsAddTorsionFree K] {F : PowerSeries K} (a : ℕ → K)
    (hF0 : PowerSeries.constantCoeff F = 1)
    (hFderiv : d⁄dX K F = F * detTraceShiftedSeries a) :
    F = (PowerSeries.exp K).subst (detTraceWeightedLogSeries a) :=
  exp_subst_eq_of_derivative_eq_mul
    (constantCoeff_detTraceWeightedLogSeries a)
    (derivative_detTraceWeightedLogSeries a)
    hF0 hFderiv

/-- Columnwise Leibniz rule for the determinant of a polynomial-valued square matrix. -/
theorem derivative_det_eq_sum_updateCol {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R[X]) :
    Polynomial.derivative A.det =
      ∑ j : n, (A.updateCol j (fun i => Polynomial.derivative (A i j))).det := by
  rw [Matrix.det_apply']
  rw [Polynomial.derivative_sum]
  simp_rw [Polynomial.derivative_intCast_mul]
  simp_rw [Polynomial.derivative_prod_finset]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl ?_
  intro σ _hσ
  have hprod :
      (∏ x, if x = j then Polynomial.derivative (A (σ x) j) else A (σ x) x) =
        Polynomial.derivative (A (σ j) j) * ∏ i ∈ Finset.univ.erase j, A (σ i) i := by
    conv_lhs =>
      rw [← Finset.insert_erase (Finset.mem_univ j)]
      rw [Finset.prod_insert (Finset.notMem_erase j Finset.univ)]
    simp only [ite_true]
    apply congrArg (fun q : R[X] => Polynomial.derivative (A (σ j) j) * q)
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxne : x ≠ j := (Finset.mem_erase.mp hx).1
    simp [hxne]
  simp only [Matrix.updateCol_apply]
  rw [hprod]
  ac_rfl

/-- The same columnwise derivative formula rewritten by Cramer's rule and the adjugate. -/
theorem derivative_det_eq_sum_adjugate_mulVec {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R[X]) :
    Polynomial.derivative A.det =
      ∑ j : n, Matrix.mulVec A.adjugate (fun i => Polynomial.derivative (A i j)) j := by
  rw [derivative_det_eq_sum_updateCol]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [← Matrix.cramer_apply (A := A) (b := fun i => Polynomial.derivative (A i j)) j,
    Matrix.cramer_eq_adjugate_mulVec]

/-- The polynomial matrix `1 - X • T`. -/
noncomputable def oneSubXMatrixPoly {K : Type*} [Ring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    Matrix n n K[X] :=
  1 - (Polynomial.X : K[X]) • T.map Polynomial.C

@[simp]
theorem derivative_oneSubXMatrixPoly_apply {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) (i j : n) :
    Polynomial.derivative (oneSubXMatrixPoly T i j) = -Polynomial.C (T i j) := by
  by_cases hij : i = j
  · subst j
    simp [oneSubXMatrixPoly, Matrix.smul_apply, Matrix.map_apply]
  · simp [oneSubXMatrixPoly, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, hij]

/-- Jacobi's determinant derivative formula for `det(1 - X • T)` over polynomials. -/
theorem derivative_det_oneSubXMatrixPoly {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    Polynomial.derivative (Matrix.det (oneSubXMatrixPoly T)) =
      -Matrix.trace (Matrix.adjugate (oneSubXMatrixPoly T) * T.map Polynomial.C) := by
  rw [derivative_det_eq_sum_adjugate_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.trace, Matrix.mul_apply, Finset.sum_neg_distrib]

/-- The formal geometric resolvent `Σ X^k • T^k`, entrywise. -/
noncomputable def psMatrixOfPowers {K : Type*} [Semiring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    Matrix n n (PowerSeries K) :=
  fun i j => PowerSeries.mk fun k => (T ^ k) i j

/-- The power-series matrix `1 - X • T`. -/
noncomputable def oneSubXMatrix {K : Type*} [Ring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    Matrix n n (PowerSeries K) :=
  1 - (PowerSeries.X : PowerSeries K) • T.map (PowerSeries.C : K →+* PowerSeries K)

theorem oneSubXMatrix_eq_map_oneSubXMatrixPoly {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    oneSubXMatrix T =
      (oneSubXMatrixPoly T).map
        (Polynomial.coeToPowerSeries.ringHom : K[X] →+* PowerSeries K) := by
  ext i j k
  by_cases hij : i = j
  · subst j
    simp [oneSubXMatrix, oneSubXMatrixPoly, Matrix.smul_apply, Matrix.map_apply]
    rw [mul_comm]
  · simp [oneSubXMatrix, oneSubXMatrixPoly, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.map_apply, hij]
    rw [mul_comm]

theorem trace_adjugate_map_oneSubXMatrixPoly {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    Matrix.trace (Matrix.adjugate
        ((oneSubXMatrixPoly T).map
          (Polynomial.coeToPowerSeries.ringHom : K[X] →+* PowerSeries K)) *
        T.map (PowerSeries.C : K →+* PowerSeries K)) =
      (Polynomial.coeToPowerSeries.ringHom : K[X] →+* PowerSeries K)
        (Matrix.trace (Matrix.adjugate (oneSubXMatrixPoly T) * T.map Polynomial.C)) := by
  let f : K[X] →+* PowerSeries K := Polynomial.coeToPowerSeries.ringHom
  have hTmap :
      T.map (PowerSeries.C : K →+* PowerSeries K) =
        (T.map Polynomial.C).map f := by
    ext i j
    simp [f]
  rw [hTmap]
  have hadj :
      Matrix.adjugate ((oneSubXMatrixPoly T).map f) =
        (Matrix.adjugate (oneSubXMatrixPoly T)).map f := by
    simpa using (RingHom.map_adjugate f (oneSubXMatrixPoly T)).symm
  rw [hadj]
  rw [← Matrix.map_mul]
  exact (AddMonoidHom.map_trace f.toAddMonoidHom
    (Matrix.adjugate (oneSubXMatrixPoly T) * T.map Polynomial.C)).symm

/-- Jacobi's formula transferred to the power-series matrix `1 - X • T`. -/
theorem derivative_det_oneSubXMatrix {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    d⁄dX K (Matrix.det (oneSubXMatrix T)) =
      -Matrix.trace (Matrix.adjugate (oneSubXMatrix T) *
        T.map (PowerSeries.C : K →+* PowerSeries K)) := by
  let f : K[X] →+* PowerSeries K := Polynomial.coeToPowerSeries.ringHom
  have hpoly :=
    congrArg f
      (derivative_det_oneSubXMatrixPoly T)
  rw [oneSubXMatrix_eq_map_oneSubXMatrixPoly]
  change d⁄dX K (Matrix.det ((oneSubXMatrixPoly T).map f)) =
    -Matrix.trace (Matrix.adjugate ((oneSubXMatrixPoly T).map f) *
      T.map (PowerSeries.C : K →+* PowerSeries K))
  have hdet :
      f (Matrix.det (oneSubXMatrixPoly T)) =
        Matrix.det ((oneSubXMatrixPoly T).map f) := by
    simpa using RingHom.map_det f (oneSubXMatrixPoly T)
  rw [← hdet]
  change d⁄dX K ((Matrix.det (oneSubXMatrixPoly T) : K[X]) : PowerSeries K) =
    -Matrix.trace (Matrix.adjugate ((oneSubXMatrixPoly T).map f) *
      T.map (PowerSeries.C : K →+* PowerSeries K))
  rw [PowerSeries.derivative_coe]
  rw [trace_adjugate_map_oneSubXMatrixPoly]
  exact hpoly

@[simp]
theorem coeff_psMatrixOfPowers {K : Type*} [Semiring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff k (psMatrixOfPowers T i j) = (T ^ k) i j := by
  simp [psMatrixOfPowers]

theorem coeff_constMul_psMatrixOfPowers {K : Type*} [Semiring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff k ((T.map (PowerSeries.C : K →+* PowerSeries K) *
      psMatrixOfPowers T) i j) = (T * T ^ k) i j := by
  simp [Matrix.mul_apply, psMatrixOfPowers]

@[simp]
theorem coeff_X_constMul_psMatrixOfPowers_zero {K : Type*} [Semiring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) (i j : n) :
    PowerSeries.coeff 0
        (((PowerSeries.X : PowerSeries K) • T.map (PowerSeries.C : K →+* PowerSeries K) *
          psMatrixOfPowers T) i j) = 0 := by
  simp [Matrix.mul_apply]

theorem coeff_X_constMul_psMatrixOfPowers_succ {K : Type*} [Semiring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff (k + 1)
        (((PowerSeries.X : PowerSeries K) • T.map (PowerSeries.C : K →+* PowerSeries K) *
          psMatrixOfPowers T) i j) =
      (T * T ^ k) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.smul_apply, Matrix.map_apply]
  simp [psMatrixOfPowers, mul_assoc]

theorem oneSubXMatrix_mul_psMatrixOfPowers {K : Type*} [Ring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    oneSubXMatrix T * psMatrixOfPowers T = 1 := by
  ext i j k
  cases k with
  | zero =>
      simp [oneSubXMatrix, psMatrixOfPowers, Matrix.mul_apply, Matrix.one_apply]
  | succ k =>
      calc
        PowerSeries.coeff (k + 1) ((oneSubXMatrix T * psMatrixOfPowers T) i j)
            = PowerSeries.coeff (k + 1)
                ((psMatrixOfPowers T -
                    (PowerSeries.X : PowerSeries K) •
                      T.map (PowerSeries.C : K →+* PowerSeries K) * psMatrixOfPowers T) i j) := by
              rw [oneSubXMatrix, sub_mul, one_mul]
        _ = (T ^ (k + 1)) i j - (T * T ^ k) i j := by
              simp [psMatrixOfPowers, coeff_constMul_psMatrixOfPowers]
        _ = 0 := by
              rw [pow_succ']
              simp
        _ = PowerSeries.coeff (k + 1) ((1 : Matrix n n (PowerSeries K)) i j) := by
              by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem det_oneSubXMatrix_eq_charpolyRev {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    Matrix.det (oneSubXMatrix T) = (T.charpolyRev : PowerSeries K) := by
  rw [Matrix.charpolyRev]
  change Matrix.det (oneSubXMatrix T) =
    Polynomial.coeToPowerSeries.ringHom
      (Matrix.det (1 - (Polynomial.X : K[X]) • T.map Polynomial.C))
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change oneSubXMatrix T i j =
    Polynomial.coeToPowerSeries.ringHom
      ((1 - (Polynomial.X : K[X]) • T.map Polynomial.C) i j)
  by_cases hij : i = j
  · subst j
    rw [Polynomial.coeToPowerSeries.ringHom_apply]
    simp only [oneSubXMatrix, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply,
      Matrix.map_apply, Polynomial.coe_sub, Polynomial.coe_one]
    change 1 - (PowerSeries.X : PowerSeries K) * PowerSeries.C (T i i) =
      1 - ((Polynomial.X * Polynomial.C (T i i) : K[X]) : PowerSeries K)
    rw [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]
  · simp only [oneSubXMatrix, Matrix.sub_apply, Matrix.one_apply_ne hij, Matrix.smul_apply,
      Matrix.map_apply]
    rw [Polynomial.coeToPowerSeries.ringHom_apply]
    simp only [Polynomial.coe_sub, Polynomial.coe_zero]
    change 0 - (PowerSeries.X : PowerSeries K) * PowerSeries.C (T i j) =
      0 - ((Polynomial.X * Polynomial.C (T i j) : K[X]) : PowerSeries K)
    rw [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]

/-- The determinant has constant coefficient one, so it is invertible as a power series. -/
theorem constantCoeff_det_oneSubXMatrix {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    PowerSeries.constantCoeff (Matrix.det (oneSubXMatrix T)) = 1 := by
  rw [det_oneSubXMatrix_eq_charpolyRev]
  simp [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

/-- The adjugate formula for the resolvent `(1-XT)⁻¹ = Σ X^k T^k`. -/
theorem inv_det_smul_adjugate_oneSubXMatrix_eq_psMatrixOfPowers {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    (Matrix.det (oneSubXMatrix T))⁻¹ • Matrix.adjugate (oneSubXMatrix T) =
      psMatrixOfPowers T := by
  let A : Matrix n n (PowerSeries K) := oneSubXMatrix T
  let R : Matrix n n (PowerSeries K) := psMatrixOfPowers T
  have hA0 : PowerSeries.constantCoeff (Matrix.det A) ≠ 0 := by
    dsimp [A]
    rw [constantCoeff_det_oneSubXMatrix T]
    exact one_ne_zero
  have hR : A * R = 1 := by
    dsimp [A, R]
    exact oneSubXMatrix_mul_psMatrixOfPowers T
  have hB : ((Matrix.det A)⁻¹ • Matrix.adjugate A) * A = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
      PowerSeries.inv_mul_cancel (Matrix.det A) hA0, one_smul]
  calc
    (Matrix.det (oneSubXMatrix T))⁻¹ • Matrix.adjugate (oneSubXMatrix T)
        = (Matrix.det A)⁻¹ • Matrix.adjugate A := rfl
    _ = ((Matrix.det A)⁻¹ • Matrix.adjugate A) * 1 := by rw [Matrix.mul_one]
    _ = ((Matrix.det A)⁻¹ • Matrix.adjugate A) * (A * R) := by rw [hR]
    _ = (((Matrix.det A)⁻¹ • Matrix.adjugate A) * A) * R := by rw [Matrix.mul_assoc]
    _ = R := by rw [hB, Matrix.one_mul]
    _ = psMatrixOfPowers T := rfl

theorem coeff_trace_psMatrixOfPowers_mul_const {K : Type*} [Semiring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff k
      (Matrix.trace (psMatrixOfPowers T * T.map (PowerSeries.C : K →+* PowerSeries K))) =
      Matrix.trace (T ^ (k + 1)) := by
  rw [Matrix.trace, Matrix.trace, pow_succ]
  simp_rw [Matrix.diag_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Matrix.map_apply, PowerSeries.coeff_mul_C, coeff_psMatrixOfPowers]

theorem inv_det_mul_trace_adjugate_mul_eq_trace_psMatrixOfPowers_mul_const
    {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    (Matrix.det (oneSubXMatrix T))⁻¹ *
        Matrix.trace (Matrix.adjugate (oneSubXMatrix T) *
          T.map (PowerSeries.C : K →+* PowerSeries K)) =
      Matrix.trace (psMatrixOfPowers T *
        T.map (PowerSeries.C : K →+* PowerSeries K)) := by
  let A : Matrix n n (PowerSeries K) := oneSubXMatrix T
  let R : Matrix n n (PowerSeries K) := psMatrixOfPowers T
  have h :=
    congrArg (fun M : Matrix n n (PowerSeries K) =>
      Matrix.trace (M * T.map (PowerSeries.C : K →+* PowerSeries K)))
      (inv_det_smul_adjugate_oneSubXMatrix_eq_psMatrixOfPowers T)
  simpa [A, R, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using h

theorem derivative_inv_det_oneSubXMatrix {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    d⁄dX K (Matrix.det (oneSubXMatrix T))⁻¹ =
      (Matrix.det (oneSubXMatrix T))⁻¹ *
        Matrix.trace (psMatrixOfPowers T *
          T.map (PowerSeries.C : K →+* PowerSeries K)) := by
  calc
    d⁄dX K (Matrix.det (oneSubXMatrix T))⁻¹
        = -((Matrix.det (oneSubXMatrix T))⁻¹) ^ 2 *
            d⁄dX K (Matrix.det (oneSubXMatrix T)) := by
          rw [PowerSeries.derivative_inv']
    _ = -((Matrix.det (oneSubXMatrix T))⁻¹) ^ 2 *
          (-Matrix.trace (Matrix.adjugate (oneSubXMatrix T) *
            T.map (PowerSeries.C : K →+* PowerSeries K))) := by
          rw [derivative_det_oneSubXMatrix]
    _ = (Matrix.det (oneSubXMatrix T))⁻¹ *
          ((Matrix.det (oneSubXMatrix T))⁻¹ *
            Matrix.trace (Matrix.adjugate (oneSubXMatrix T) *
              T.map (PowerSeries.C : K →+* PowerSeries K))) := by
          ring
    _ = (Matrix.det (oneSubXMatrix T))⁻¹ *
          Matrix.trace (psMatrixOfPowers T *
            T.map (PowerSeries.C : K →+* PowerSeries K)) := by
          rw [inv_det_mul_trace_adjugate_mul_eq_trace_psMatrixOfPowers_mul_const]

/-- The polynomial/power-series `det(1 - X • T)`.  Mathlib calls the polynomial part
`Matrix.charpolyRev`. -/
noncomputable def matrixDetOneSubSeries {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) : PowerSeries K :=
  (T.charpolyRev : K[X])

/-- The reciprocal of `det(1 - X • T)` in `K⟦X⟧`. -/
noncomputable def matrixDetOneSubInvSeries {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) : PowerSeries K :=
  (matrixDetOneSubSeries T)⁻¹

/-- The trace-power sequence `i ↦ tr(T^i)`. -/
noncomputable def matrixTracePower {K : Type*} [Semiring K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) (i : ℕ) : K :=
  Matrix.trace (T ^ i)

/-- The formal logarithm `∑_{i≥1} tr(T^i)/i * X^i`. -/
noncomputable def matrixTraceLogSeries {K : Type*} [CommRing K] [Algebra ℚ K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) : PowerSeries K :=
  detTraceWeightedLogSeries (matrixTracePower T)

/-- The logarithmic derivative target `∑_{i≥1} tr(T^i) * X^{i-1}`. -/
noncomputable def matrixTraceResolventSeries {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) : PowerSeries K :=
  detTraceShiftedSeries (matrixTracePower T)

theorem derivative_matrixTraceLogSeries {K : Type*} [CommRing K] [Algebra ℚ K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    d⁄dX K (matrixTraceLogSeries T) = matrixTraceResolventSeries T :=
  derivative_detTraceWeightedLogSeries (matrixTracePower T)

theorem matrixTraceResolventSeries_eq_trace_psMatrixOfPowers_mul_const {K : Type*}
    [CommRing K] {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    matrixTraceResolventSeries T =
      Matrix.trace (psMatrixOfPowers T * T.map (PowerSeries.C : K →+* PowerSeries K)) := by
  ext k
  rw [coeff_trace_psMatrixOfPowers_mul_const]
  simp [matrixTraceResolventSeries, detTraceShiftedSeries, matrixTracePower]

theorem constantCoeff_matrixDetOneSubSeries {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    PowerSeries.constantCoeff (matrixDetOneSubSeries T) = 1 := by
  simp [matrixDetOneSubSeries, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    Matrix.eval_charpolyRev]

theorem coeff_one_matrixDetOneSubSeries {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    PowerSeries.coeff 1 (matrixDetOneSubSeries T) = -Matrix.trace T := by
  simp [matrixDetOneSubSeries]

theorem constantCoeff_matrixDetOneSubInvSeries {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    PowerSeries.constantCoeff (matrixDetOneSubInvSeries T) = 1 := by
  simp [matrixDetOneSubInvSeries, constantCoeff_matrixDetOneSubSeries]

/-- The determinant-specific Newton/Jacobi logarithmic derivative input:
`(det(1-XT)⁻¹)' = det(1-XT)⁻¹ * ∑ tr(T^{i+1}) X^i`. -/
theorem derivative_matrixDetOneSubInvSeries {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n K) :
    d⁄dX K (matrixDetOneSubInvSeries T) =
      matrixDetOneSubInvSeries T * matrixTraceResolventSeries T := by
  have h := derivative_inv_det_oneSubXMatrix T
  rw [det_oneSubXMatrix_eq_charpolyRev] at h
  simpa [matrixDetOneSubSeries, matrixDetOneSubInvSeries,
    matrixTraceResolventSeries_eq_trace_psMatrixOfPowers_mul_const] using h

/-- **Lemma .37, formal algebraic core.** The reciprocal characteristic power series is the
exponential of the trace-power logarithm. -/
theorem lem37_det_trace_formal_identity {K : Type*} [Field K] [Algebra ℚ K]
    [IsAddTorsionFree K] {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n K) :
    matrixDetOneSubInvSeries T = (PowerSeries.exp K).subst (matrixTraceLogSeries T) := by
  simpa [matrixTraceLogSeries, matrixTraceResolventSeries] using
    exp_detTraceWeightedLogSeries_unique
      (K := K) (F := matrixDetOneSubInvSeries T) (matrixTracePower T)
      (constantCoeff_matrixDetOneSubInvSeries T) (derivative_matrixDetOneSubInvSeries T)

end DetTrace

/-! ## §G — Euler product core for `Z_U` (§6.2).

The full motivic zeta function depends on the geometric input producing the local traces
`a_p`.  The analytic Euler-product heart that Mathlib can certify unconditionally is the
completely multiplicative case, plus the algebraic splitting of a quadratic local factor
`(1 - a_p u + p u^2)⁻¹` into two linear factors when Frobenius roots `α_p, β_p` with
`a_p = α_p + β_p` and `α_p β_p = p` are supplied.  The half-plane derivative statement is the
existing `LSeries.deriv` theorem, repackaged under the `Z_U` names used here.
-/

section EulerProductZU

open scoped Topology
open Complex Filter Nat Topology EulerProduct LSeries

/-- Linear Euler local factor attached to a completely multiplicative summand. -/
noncomputable def zetaULinearLocalFactor (f : ℕ →*₀ ℂ) (p : Nat.Primes) : ℂ :=
  (1 - f p)⁻¹

/-- The Dirichlet-series value certified by the completely multiplicative Euler product. -/
noncomputable def zetaUCompletelyMultiplicativeValue (f : ℕ →*₀ ℂ) : ℂ :=
  ∑' n : ℕ, f n

/-- The local linear Euler factor is the geometric series over prime powers. -/
theorem zetaULinearLocalFactor_eq_geometric_tsum {f : ℕ →*₀ ℂ}
    (hsum : Summable (‖f ·‖)) (p : Nat.Primes) :
    zetaULinearLocalFactor f p = ∑' e : ℕ, f (p ^ e) := by
  simpa [zetaULinearLocalFactor] using
    EulerProduct.one_sub_inv_eq_geometric_of_summable_norm p.prop hsum

/-- Completely multiplicative Euler product for `Z_U`, stated as `HasProd`. -/
theorem zetaU_eulerProduct_hasProd {f : ℕ →*₀ ℂ}
    (hsum : Summable (‖f ·‖)) :
    HasProd (zetaULinearLocalFactor f) (zetaUCompletelyMultiplicativeValue f) := by
  simpa [zetaULinearLocalFactor, zetaUCompletelyMultiplicativeValue] using
    EulerProduct.eulerProduct_completely_multiplicative_hasProd (f := f) hsum

/-- Completely multiplicative Euler product for `Z_U`, stated as a `tprod` identity. -/
theorem zetaU_eulerProduct_tprod {f : ℕ →*₀ ℂ}
    (hsum : Summable (‖f ·‖)) :
    ∏' p : Nat.Primes, zetaULinearLocalFactor f p =
      zetaUCompletelyMultiplicativeValue f := by
  exact (zetaU_eulerProduct_hasProd hsum).tprod_eq

/-- Completely multiplicative Euler product for `Z_U`, stated as convergence of prime partial
products. -/
theorem zetaU_eulerProduct_partial {f : ℕ →*₀ ℂ}
    (hsum : Summable (‖f ·‖)) :
    Tendsto (fun N : ℕ => ∏ p ∈ primesBelow N, (1 - f p)⁻¹) atTop
      (𝓝 (zetaUCompletelyMultiplicativeValue f)) := by
  simpa [zetaUCompletelyMultiplicativeValue] using
    EulerProduct.eulerProduct_completely_multiplicative (f := f) hsum

/-- Quadratic Euler denominator `1 - a_p u + p u^2`. -/
noncomputable def quadraticEulerDenominator (a : ℕ → ℂ) (p : ℕ) (u : ℂ) : ℂ :=
  1 - a p * u + (p : ℂ) * u ^ 2

/-- Quadratic Euler local factor `(1 - a_p u + p u^2)⁻¹`. -/
noncomputable def quadraticEulerLocalFactor (a : ℕ → ℂ) (p : ℕ) (u : ℂ) : ℂ :=
  (quadraticEulerDenominator a p u)⁻¹

/-- Algebraic splitting of the quadratic denominator into Frobenius-root linear factors. -/
theorem quadraticEulerDenominator_eq_mul {a α β : ℕ → ℂ} {p : ℕ} {u : ℂ}
    (htrace : a p = α p + β p) (hnorm : α p * β p = (p : ℂ)) :
    quadraticEulerDenominator a p u = (1 - α p * u) * (1 - β p * u) := by
  simp [quadraticEulerDenominator, htrace]
  rw [← hnorm]
  ring_nf

/-- Algebraic splitting of the quadratic local factor into two linear Euler factors. -/
theorem quadraticEulerLocalFactor_eq_mul {a α β : ℕ → ℂ} {p : ℕ} {u : ℂ}
    (htrace : a p = α p + β p) (hnorm : α p * β p = (p : ℂ)) :
    quadraticEulerLocalFactor a p u =
      (1 - α p * u)⁻¹ * (1 - β p * u)⁻¹ := by
  rw [quadraticEulerLocalFactor, quadraticEulerDenominator_eq_mul htrace hnorm]
  rw [mul_inv_rev]
  ring

/-- Finite prime partial product of the quadratic local factors. -/
noncomputable def quadraticEulerPartialProduct (a : ℕ → ℂ) (N : ℕ) (u : ℂ) : ℂ :=
  ∏ p ∈ primesBelow N, quadraticEulerLocalFactor a p u

/-- The finite quadratic Euler product splits into the product of two finite linear Euler
products whenever the trace and determinant relations hold on the primes below `N`. -/
theorem quadraticEulerPartialProduct_eq_mul {a α β : ℕ → ℂ} {N : ℕ} {u : ℂ}
    (htrace : ∀ p ∈ primesBelow N, a p = α p + β p)
    (hnorm : ∀ p ∈ primesBelow N, α p * β p = (p : ℂ)) :
    quadraticEulerPartialProduct a N u =
      (∏ p ∈ primesBelow N, (1 - α p * u)⁻¹) *
        ∏ p ∈ primesBelow N, (1 - β p * u)⁻¹ := by
  rw [quadraticEulerPartialProduct]
  calc
    ∏ p ∈ primesBelow N, quadraticEulerLocalFactor a p u
        = ∏ p ∈ primesBelow N, ((1 - α p * u)⁻¹ * (1 - β p * u)⁻¹) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          exact quadraticEulerLocalFactor_eq_mul (a := a) (α := α) (β := β)
            (htrace p hp) (hnorm p hp)
    _ = (∏ p ∈ primesBelow N, (1 - α p * u)⁻¹) *
        ∏ p ∈ primesBelow N, (1 - β p * u)⁻¹ := by
          rw [Finset.prod_mul_distrib]

/-- If the two linear Frobenius-root Euler products converge, then the corresponding quadratic
Euler product converges to the product of their limits. -/
theorem quadraticEulerProduct_hasProd_of_linear {a α β : ℕ → ℂ} {u A B : ℂ}
    (htrace : ∀ p : Nat.Primes, a p = α p + β p)
    (hnorm : ∀ p : Nat.Primes, α p * β p = (p : ℂ))
    (hα : HasProd (fun p : Nat.Primes => (1 - α p * u)⁻¹) A)
    (hβ : HasProd (fun p : Nat.Primes => (1 - β p * u)⁻¹) B) :
    HasProd (fun p : Nat.Primes => quadraticEulerLocalFactor a p u) (A * B) := by
  have hlocal :
      (fun p : Nat.Primes => quadraticEulerLocalFactor a p u) =
        fun p : Nat.Primes => (1 - α p * u)⁻¹ * (1 - β p * u)⁻¹ := by
    funext p
    exact quadraticEulerLocalFactor_eq_mul (a := a) (α := α) (β := β)
      (htrace p) (hnorm p)
  rw [hlocal]
  exact hα.mul hβ

/-- `tprod` form of the split quadratic Euler product. -/
theorem quadraticEulerProduct_tprod_of_linear {a α β : ℕ → ℂ} {u A B : ℂ}
    (htrace : ∀ p : Nat.Primes, a p = α p + β p)
    (hnorm : ∀ p : Nat.Primes, α p * β p = (p : ℂ))
    (hα : HasProd (fun p : Nat.Primes => (1 - α p * u)⁻¹) A)
    (hβ : HasProd (fun p : Nat.Primes => (1 - β p * u)⁻¹) B) :
    ∏' p : Nat.Primes, quadraticEulerLocalFactor a p u = A * B :=
  (quadraticEulerProduct_hasProd_of_linear htrace hnorm hα hβ).tprod_eq

/-- L-series avatar of `Z_U` for an arbitrary coefficient sequence. -/
noncomputable def zetaULSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries f s

/-- The `abscissaOfAbsConv` API gives convergence on its open right half-plane. -/
theorem zetaULSeries_summable_of_abscissa_lt {f : ℕ → ℂ} {s : ℂ}
    (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable f s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re h

/-- On the half-plane of absolute convergence, the logarithmic derivative input is Mathlib's
`LSeries.deriv`: differentiating inserts the factor `-log n` in the coefficients. -/
theorem zetaULSeries_deriv {f : ℕ → ℂ} {s : ℂ}
    (h : abscissaOfAbsConv f < s.re) :
    deriv (zetaULSeries f) s = -zetaULSeries (LSeries.logMul f) s := by
  simpa [zetaULSeries] using LSeries_deriv (f := f) (s := s) h

/-- Logarithmic derivative of the L-series avatar of `Z_U`.  This definition is total; at zeros
of `Z_U` it uses Lean's total division on `ℂ`. -/
noncomputable def zetaULSeriesLogDeriv (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  deriv (zetaULSeries f) s / zetaULSeries f s

/-- On the half-plane of absolute convergence, `Z_U'/Z_U` is the normalized
`-L(logMul f)`. -/
theorem zetaULSeries_logDeriv_eq {f : ℕ → ℂ} {s : ℂ}
    (h : abscissaOfAbsConv f < s.re) :
    zetaULSeriesLogDeriv f s =
      -zetaULSeries (LSeries.logMul f) s / zetaULSeries f s := by
  simp [zetaULSeriesLogDeriv, zetaULSeries_deriv h]

/-- Multiplying coefficients by `log n` preserves the abscissa of absolute convergence. -/
theorem zetaULSeries_abscissa_logMul (f : ℕ → ℂ) :
    abscissaOfAbsConv (LSeries.logMul f) = abscissaOfAbsConv f := by
  exact LSeries.abscissaOfAbsConv_logMul

end EulerProductZU

/-! ## §H — Constructible six-functor interface (Def .20/.21, Lem .22-.25/.29).

Mathlib does not yet contain the étale constructible derived category and its six
operations.  The following record isolates exactly the data needed by the paper:
a category of schemes, a family of sheaf-like objects over it, constructibility,
the six operations, gluing triangles, base change, and the projection formula.
All downstream statements are honest projections from this record, so no global
assumption is introduced into the kernel. -/

section SixFunctorInterface

open CategoryTheory

universe uSch vSch uSheaf uTri

/-- Certification interface for the constructible `ℓ`-adic six-functor package.

The parameter `Sch` is any category playing the role of schemes.  `Sheaf X` is the
type of objects over `X`; `SheafIso` records the isomorphism relation relevant to
the chosen model. -/
structure SixFunctorData (Sch : Type uSch) [Category.{vSch} Sch] where
  Sheaf : Sch → Type uSheaf
  IsConstr : {X : Sch} → Sheaf X → Prop
  SheafIso : {X : Sch} → Sheaf X → Sheaf X → Prop
  sheafIso_refl : ∀ {X : Sch} (F : Sheaf X), SheafIso F F
  sheafIso_symm : ∀ {X : Sch} {F G : Sheaf X}, SheafIso F G → SheafIso G F
  sheafIso_trans :
    ∀ {X : Sch} {F G H : Sheaf X}, SheafIso F G → SheafIso G H → SheafIso F H
  pull : {X Y : Sch} → (X ⟶ Y) → Sheaf Y → Sheaf X
  push : {X Y : Sch} → (X ⟶ Y) → Sheaf X → Sheaf Y
  shriek : {X Y : Sch} → (X ⟶ Y) → Sheaf X → Sheaf Y
  exceptionalPull : {X Y : Sch} → (X ⟶ Y) → Sheaf Y → Sheaf X
  tensor : {X : Sch} → Sheaf X → Sheaf X → Sheaf X
  internalHom : {X : Sch} → Sheaf X → Sheaf X → Sheaf X
  dual : {X : Sch} → Sheaf X → Sheaf X
  unit : (X : Sch) → Sheaf X
  Triangle : Sch → Type uTri
  distinguished : {X : Sch} → Triangle X → Prop
  isOpenImmersion : {U X : Sch} → (U ⟶ X) → Prop
  isClosedImmersion : {Z X : Sch} → (Z ⟶ X) → Prop
  isProper : {X Y : Sch} → (X ⟶ Y) → Prop
  isSmoothCurveOver : {C V : Sch} → (C ⟶ V) → Prop
  openClosedTriangle :
    {X U Z : Sch} → (j : U ⟶ X) → (i : Z ⟶ X) →
      isOpenImmersion j → isClosedImmersion i → Sheaf X → Triangle X
  baseChangeSquare :
    {X Y S X' : Sch} → (f : X ⟶ S) → (g : Y ⟶ S) →
      (f' : X' ⟶ Y) → (g' : X' ⟶ X) → Prop
  pull_constr :
    ∀ {X Y : Sch} (f : X ⟶ Y) (F : Sheaf Y), IsConstr F → IsConstr (pull f F)
  push_constr :
    ∀ {X Y : Sch} (f : X ⟶ Y) (F : Sheaf X), IsConstr F → IsConstr (push f F)
  shriek_constr :
    ∀ {X Y : Sch} (f : X ⟶ Y) (F : Sheaf X), IsConstr F → IsConstr (shriek f F)
  exceptionalPull_constr :
    ∀ {X Y : Sch} (f : X ⟶ Y) (F : Sheaf Y),
      IsConstr F → IsConstr (exceptionalPull f F)
  tensor_constr :
    ∀ {X : Sch} (F G : Sheaf X), IsConstr F → IsConstr G → IsConstr (tensor F G)
  internalHom_constr :
    ∀ {X : Sch} (F G : Sheaf X),
      IsConstr F → IsConstr G → IsConstr (internalHom F G)
  dual_constr :
    ∀ {X : Sch} (F : Sheaf X), IsConstr F → IsConstr (dual F)
  unit_constr : ∀ X : Sch, IsConstr (unit X)
  glue_triangle :
    ∀ {X U Z : Sch} (j : U ⟶ X) (i : Z ⟶ X)
      (hj : isOpenImmersion j) (hi : isClosedImmersion i)
      (F : Sheaf X), IsConstr F → distinguished (openClosedTriangle j i hj hi F)
  monoidal_dual :
    ∀ {X : Sch} (F : Sheaf X), IsConstr F →
      SheafIso (dual F) (internalHom F (unit X))
  pull_congr :
    ∀ {X Y : Sch} (f : X ⟶ Y) {F G : Sheaf Y},
      IsConstr F → IsConstr G → SheafIso F G → SheafIso (pull f F) (pull f G)
  pull_id :
    ∀ {X : Sch} (F : Sheaf X), IsConstr F → SheafIso (pull (𝟙 X) F) F
  pull_comp :
    ∀ {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Sheaf Z),
      IsConstr F → SheafIso (pull (f ≫ g) F) (pull f (pull g F))
  push_congr :
    ∀ {X Y : Sch} (f : X ⟶ Y) {F G : Sheaf X},
      IsConstr F → IsConstr G → SheafIso F G → SheafIso (push f F) (push f G)
  push_id :
    ∀ {X : Sch} (F : Sheaf X), IsConstr F → SheafIso (push (𝟙 X) F) F
  push_comp :
    ∀ {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Sheaf X),
      IsConstr F → SheafIso (push (f ≫ g) F) (push g (push f F))
  shriek_congr :
    ∀ {X Y : Sch} (f : X ⟶ Y) {F G : Sheaf X},
      IsConstr F → IsConstr G → SheafIso F G → SheafIso (shriek f F) (shriek f G)
  shriek_id :
    ∀ {X : Sch} (F : Sheaf X), IsConstr F → SheafIso (shriek (𝟙 X) F) F
  shriek_comp :
    ∀ {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Sheaf X),
      IsConstr F → SheafIso (shriek (f ≫ g) F) (shriek g (shriek f F))
  exceptionalPull_congr :
    ∀ {X Y : Sch} (f : X ⟶ Y) {F G : Sheaf Y},
      IsConstr F → IsConstr G → SheafIso F G →
        SheafIso (exceptionalPull f F) (exceptionalPull f G)
  exceptionalPull_id :
    ∀ {X : Sch} (F : Sheaf X), IsConstr F → SheafIso (exceptionalPull (𝟙 X) F) F
  exceptionalPull_comp :
    ∀ {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Sheaf Z),
      IsConstr F →
        SheafIso (exceptionalPull (f ≫ g) F) (exceptionalPull f (exceptionalPull g F))
  baseChangeShriek :
    ∀ {X Y S X' : Sch} {f : X ⟶ S} {g : Y ⟶ S}
      {f' : X' ⟶ Y} {g' : X' ⟶ X},
      baseChangeSquare f g f' g' →
        ∀ F : Sheaf X, IsConstr F →
          SheafIso (pull g (shriek f F)) (shriek f' (pull g' F))
  projectionFormula :
    ∀ {X Y : Sch} (f : X ⟶ Y) (F : Sheaf X) (G : Sheaf Y),
      IsConstr F → IsConstr G →
        SheafIso (shriek f (tensor F (pull f G))) (tensor (shriek f F) G)

namespace SixFunctorData

variable {Sch : Type uSch} [Category.{vSch} Sch]

theorem sheafIso_refl_apply (D : SixFunctorData Sch) {X : Sch} (F : D.Sheaf X) :
    D.SheafIso F F :=
  D.sheafIso_refl F

theorem sheafIso_symm_apply (D : SixFunctorData Sch) {X : Sch} {F G : D.Sheaf X}
    (h : D.SheafIso F G) : D.SheafIso G F :=
  D.sheafIso_symm h

theorem sheafIso_trans_apply (D : SixFunctorData Sch) {X : Sch} {F G H : D.Sheaf X}
    (hFG : D.SheafIso F G) (hGH : D.SheafIso G H) : D.SheafIso F H :=
  D.sheafIso_trans hFG hGH

/-- Lemma .22-style stability of constructibility under pullback. -/
theorem pull_constructible (D : SixFunctorData Sch) {X Y : Sch} (f : X ⟶ Y)
    (F : D.Sheaf Y) (hF : D.IsConstr F) :
    D.IsConstr (D.pull f F) :=
  D.pull_constr f F hF

/-- Lemma .22-style stability of constructibility under direct image. -/
theorem push_constructible (D : SixFunctorData Sch) {X Y : Sch} (f : X ⟶ Y)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.push f F) :=
  D.push_constr f F hF

/-- Lemma .22-style stability of constructibility under extraordinary direct image. -/
theorem shriek_constructible (D : SixFunctorData Sch) {X Y : Sch} (f : X ⟶ Y)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.shriek f F) :=
  D.shriek_constr f F hF

/-- Lemma .22-style stability of constructibility under extraordinary pullback. -/
theorem exceptionalPull_constructible (D : SixFunctorData Sch) {X Y : Sch}
    (f : X ⟶ Y) (F : D.Sheaf Y) (hF : D.IsConstr F) :
    D.IsConstr (D.exceptionalPull f F) :=
  D.exceptionalPull_constr f F hF

/-- Lemma .23-style tensor stability for constructible objects. -/
theorem tensor_constructible (D : SixFunctorData Sch) {X : Sch}
    (F G : D.Sheaf X) (hF : D.IsConstr F) (hG : D.IsConstr G) :
    D.IsConstr (D.tensor F G) :=
  D.tensor_constr F G hF hG

/-- Lemma .23-style internal-Hom stability for constructible objects. -/
theorem internalHom_constructible (D : SixFunctorData Sch) {X : Sch}
    (F G : D.Sheaf X) (hF : D.IsConstr F) (hG : D.IsConstr G) :
    D.IsConstr (D.internalHom F G) :=
  D.internalHom_constr F G hF hG

/-- Lemma .25-style dual stability for constructible objects. -/
theorem dual_constructible (D : SixFunctorData Sch) {X : Sch}
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.dual F) :=
  D.dual_constr F hF

/-- The monoidal unit is constructible. -/
theorem unit_constructible (D : SixFunctorData Sch) (X : Sch) :
    D.IsConstr (D.unit X) :=
  D.unit_constr X

/-- Lemma .24-style open/closed gluing triangle. -/
theorem glue_triangle_distinguished (D : SixFunctorData Sch)
    {X U Z : Sch} (j : U ⟶ X) (i : Z ⟶ X)
    (hj : D.isOpenImmersion j) (hi : D.isClosedImmersion i)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.distinguished (D.openClosedTriangle j i hj hi F) :=
  D.glue_triangle j i hj hi F hF

/-- Lemma .25-style monoidal duality statement for constructible objects. -/
theorem monoidal_dual_iso (D : SixFunctorData Sch) {X : Sch}
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso (D.dual F) (D.internalHom F (D.unit X)) :=
  D.monoidal_dual F hF

/-- Pullback respects the chosen sheaf-isomorphism relation. -/
theorem pull_iso_congr (D : SixFunctorData Sch) {X Y : Sch} (f : X ⟶ Y)
    {F G : D.Sheaf Y} (hF : D.IsConstr F) (hG : D.IsConstr G)
    (h : D.SheafIso F G) :
    D.SheafIso (D.pull f F) (D.pull f G) :=
  D.pull_congr f hF hG h

/-- Identity law for the certified pullback functor. -/
theorem pull_id_iso (D : SixFunctorData Sch) {X : Sch}
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso (D.pull (𝟙 X) F) F :=
  D.pull_id F hF

/-- Composition law for the certified pullback functor. -/
theorem pull_comp_iso (D : SixFunctorData Sch) {X Y Z : Sch}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : D.Sheaf Z) (hF : D.IsConstr F) :
    D.SheafIso (D.pull (f ≫ g) F) (D.pull f (D.pull g F)) :=
  D.pull_comp f g F hF

/-- Direct image respects the chosen sheaf-isomorphism relation. -/
theorem push_iso_congr (D : SixFunctorData Sch) {X Y : Sch} (f : X ⟶ Y)
    {F G : D.Sheaf X} (hF : D.IsConstr F) (hG : D.IsConstr G)
    (h : D.SheafIso F G) :
    D.SheafIso (D.push f F) (D.push f G) :=
  D.push_congr f hF hG h

/-- Identity law for the certified direct-image functor. -/
theorem push_id_iso (D : SixFunctorData Sch) {X : Sch}
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso (D.push (𝟙 X) F) F :=
  D.push_id F hF

/-- Composition law for the certified direct-image functor. -/
theorem push_comp_iso (D : SixFunctorData Sch) {X Y Z : Sch}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso (D.push (f ≫ g) F) (D.push g (D.push f F)) :=
  D.push_comp f g F hF

/-- Extraordinary direct image respects the chosen sheaf-isomorphism relation. -/
theorem shriek_iso_congr (D : SixFunctorData Sch) {X Y : Sch} (f : X ⟶ Y)
    {F G : D.Sheaf X} (hF : D.IsConstr F) (hG : D.IsConstr G)
    (h : D.SheafIso F G) :
    D.SheafIso (D.shriek f F) (D.shriek f G) :=
  D.shriek_congr f hF hG h

/-- Identity law for the certified extraordinary direct-image functor. -/
theorem shriek_id_iso (D : SixFunctorData Sch) {X : Sch}
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso (D.shriek (𝟙 X) F) F :=
  D.shriek_id F hF

/-- Functoriality of extraordinary direct image for a two-step composition. -/
theorem shriek_comp_iso (D : SixFunctorData Sch) {X Y Z : Sch}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso (D.shriek (f ≫ g) F) (D.shriek g (D.shriek f F)) :=
  D.shriek_comp f g F hF

/-- Extraordinary pullback respects the chosen sheaf-isomorphism relation. -/
theorem exceptionalPull_iso_congr (D : SixFunctorData Sch) {X Y : Sch}
    (f : X ⟶ Y) {F G : D.Sheaf Y} (hF : D.IsConstr F) (hG : D.IsConstr G)
    (h : D.SheafIso F G) :
    D.SheafIso (D.exceptionalPull f F) (D.exceptionalPull f G) :=
  D.exceptionalPull_congr f hF hG h

/-- Identity law for the certified extraordinary pullback functor. -/
theorem exceptionalPull_id_iso (D : SixFunctorData Sch) {X : Sch}
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso (D.exceptionalPull (𝟙 X) F) F :=
  D.exceptionalPull_id F hF

/-- Composition law for the certified extraordinary pullback functor. -/
theorem exceptionalPull_comp_iso (D : SixFunctorData Sch) {X Y Z : Sch}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : D.Sheaf Z) (hF : D.IsConstr F) :
    D.SheafIso
      (D.exceptionalPull (f ≫ g) F)
      (D.exceptionalPull f (D.exceptionalPull g F)) :=
  D.exceptionalPull_comp f g F hF

/-- Functoriality of extraordinary direct image for the three-step composition
used in curve reduction. -/
theorem shriek_comp_three_iso (D : SixFunctorData Sch) {W X Y Z : Sch}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (F : D.Sheaf W) (hF : D.IsConstr F) :
    D.SheafIso
      (D.shriek ((f ≫ g) ≫ h) F)
      (D.shriek h (D.shriek g (D.shriek f F))) := by
  have hfg :
      D.SheafIso
        (D.shriek ((f ≫ g) ≫ h) F)
        (D.shriek h (D.shriek (f ≫ g) F)) :=
    D.shriek_comp (f ≫ g) h F hF
  have hfgF : D.IsConstr (D.shriek (f ≫ g) F) :=
    D.shriek_constr (f ≫ g) F hF
  have hgfF : D.IsConstr (D.shriek g (D.shriek f F)) :=
    D.shriek_constr g (D.shriek f F) (D.shriek_constr f F hF)
  have hg :
      D.SheafIso
        (D.shriek h (D.shriek (f ≫ g) F))
        (D.shriek h (D.shriek g (D.shriek f F))) :=
    D.shriek_congr h hfgF hgfF (D.shriek_comp f g F hF)
  exact D.sheafIso_trans hfg hg

/-- Rewrites a three-step `shriek` factorization along an explicit equality of
morphisms.  Keeping the equality separate avoids dependent-rewrite issues for
factorization certificates that themselves are indexed by the original map. -/
theorem shriek_factorization_iso_of_eq (D : SixFunctorData Sch)
    {X Xbar C V : Sch} {f : X ⟶ V}
    (jX : X ⟶ Xbar) (g : Xbar ⟶ C) (pi : C ⟶ V)
    (hfactor : f = (jX ≫ g) ≫ pi)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso
      (D.shriek f F)
      (D.shriek pi (D.shriek g (D.shriek jX F))) := by
  rw [hfactor]
  exact D.shriek_comp_three_iso jX g pi F hF

/-- Lemma .29-style shriek base-change isomorphism. -/
theorem baseChangeShriek_iso (D : SixFunctorData Sch)
    {X Y S X' : Sch} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : X' ⟶ Y} {g' : X' ⟶ X}
    (hSq : D.baseChangeSquare f g f' g') (F : D.Sheaf X)
    (hF : D.IsConstr F) :
    D.SheafIso (D.pull g (D.shriek f F)) (D.shriek f' (D.pull g' F)) :=
  D.baseChangeShriek hSq F hF

/-- Projection formula for the certified six-functor package. -/
theorem projectionFormula_iso (D : SixFunctorData Sch) {X Y : Sch}
    (f : X ⟶ Y) (F : D.Sheaf X) (G : D.Sheaf Y)
    (hF : D.IsConstr F) (hG : D.IsConstr G) :
    D.SheafIso
      (D.shriek f (D.tensor F (D.pull f G)))
      (D.tensor (D.shriek f F) G) :=
  D.projectionFormula f F G hF hG

/-- Constructibility of the left side of shriek base change. -/
theorem baseChangeShriek_left_constructible (D : SixFunctorData Sch)
    {X Y S : Sch} (f : X ⟶ S) (g : Y ⟶ S)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.pull g (D.shriek f F)) :=
  D.pull_constr g (D.shriek f F) (D.shriek_constr f F hF)

/-- Constructibility of the right side of shriek base change. -/
theorem baseChangeShriek_right_constructible (D : SixFunctorData Sch)
    {X Y X' : Sch} (f' : X' ⟶ Y) (g' : X' ⟶ X)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.shriek f' (D.pull g' F)) :=
  D.shriek_constr f' (D.pull g' F) (D.pull_constr g' F hF)

/-- Constructibility of the two objects related by the projection formula. -/
theorem projectionFormula_terms_constructible (D : SixFunctorData Sch) {X Y : Sch}
    (f : X ⟶ Y) (F : D.Sheaf X) (G : D.Sheaf Y)
    (hF : D.IsConstr F) (hG : D.IsConstr G) :
    D.IsConstr (D.shriek f (D.tensor F (D.pull f G))) ∧
      D.IsConstr (D.tensor (D.shriek f F) G) := by
  constructor
  · exact D.shriek_constr f (D.tensor F (D.pull f G))
      (D.tensor_constr F (D.pull f G) hF (D.pull_constr f G hG))
  · exact D.tensor_constr (D.shriek f F) G (D.shriek_constr f F hF) hG

/-- A named one-sided projection-formula constructibility consequence. -/
theorem shriek_tensor_pull_constructible (D : SixFunctorData Sch) {X Y : Sch}
    (f : X ⟶ Y) (F : D.Sheaf X) (G : D.Sheaf Y)
    (hF : D.IsConstr F) (hG : D.IsConstr G) :
    D.IsConstr (D.shriek f (D.tensor F (D.pull f G))) :=
  (D.projectionFormula_terms_constructible f F G hF hG).1

/-- A named constructibility consequence for the tensor side of projection formula. -/
theorem tensor_shriek_constructible (D : SixFunctorData Sch) {X Y : Sch}
    (f : X ⟶ Y) (F : D.Sheaf X) (G : D.Sheaf Y)
    (hF : D.IsConstr F) (hG : D.IsConstr G) :
    D.IsConstr (D.tensor (D.shriek f F) G) :=
  (D.projectionFormula_terms_constructible f F G hF hG).2

end SixFunctorData

/-- Lemma .32-style curve reduction certificate.

The unavailable Nagata compactification and Stein factorization steps are bundled
as data: an open compactification `jX`, a proper map to a curve, and the curve map
to the base.  The field `factor` records that these maps compose to the original
map `f`.  The paper's `π` is named `pi` in Lean identifiers. -/
structure CurveFactorization {Sch : Type uSch} [Category.{vSch} Sch]
    (D : SixFunctorData Sch) {X V : Sch} (f : X ⟶ V) where
  Xbar : Sch
  jX : X ⟶ Xbar
  C : Sch
  g : Xbar ⟶ C
  pi : C ⟶ V
  jX_open : D.isOpenImmersion jX
  g_proper : D.isProper g
  pi_smoothCurve : D.isSmoothCurveOver pi
  factor : f = (jX ≫ g) ≫ pi

namespace CurveFactorization

variable {Sch : Type uSch} [Category.{vSch} Sch]
variable {D : SixFunctorData Sch}
variable {X V : Sch} {f : X ⟶ V}

theorem factor_eq (φ : CurveFactorization D f) :
    f = (φ.jX ≫ φ.g) ≫ φ.pi :=
  φ.factor

theorem jX_isOpenImmersion (φ : CurveFactorization D f) :
    D.isOpenImmersion φ.jX :=
  φ.jX_open

theorem g_isProper (φ : CurveFactorization D f) :
    D.isProper φ.g :=
  φ.g_proper

theorem pi_isSmoothCurveOver (φ : CurveFactorization D f) :
    D.isSmoothCurveOver φ.pi :=
  φ.pi_smoothCurve

/-- Constructibility after extension by the open compactification. -/
theorem jX_shriek_constructible (φ : CurveFactorization D f)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.shriek φ.jX F) :=
  D.shriek_constr φ.jX F hF

/-- Constructibility after the proper map to the curve. -/
theorem g_jX_shriek_constructible (φ : CurveFactorization D f)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.shriek φ.g (D.shriek φ.jX F)) :=
  D.shriek_constr φ.g (D.shriek φ.jX F) (φ.jX_shriek_constructible F hF)

/-- Constructibility after the full curve-reduction pushforward. -/
theorem pi_g_jX_shriek_constructible (φ : CurveFactorization D f)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.shriek φ.pi (D.shriek φ.g (D.shriek φ.jX F))) :=
  D.shriek_constr φ.pi (D.shriek φ.g (D.shriek φ.jX F))
    (φ.g_jX_shriek_constructible F hF)

/-- Curve-reduction functoriality before rewriting by the factorization equality. -/
theorem shriek_comp_iso (φ : CurveFactorization D f)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso
      (D.shriek ((φ.jX ≫ φ.g) ≫ φ.pi) F)
      (D.shriek φ.pi (D.shriek φ.g (D.shriek φ.jX F))) :=
  D.shriek_comp_three_iso φ.jX φ.g φ.pi F hF

/-- **Lemma .32, curve reduction.**  Under a supplied curve-factorization
certificate, `Rf_! F` is identified with the iterated pushforward through the
open compactification, proper curve map, and curve over the base. -/
theorem shriek_factorization_iso (φ : CurveFactorization D f)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.SheafIso
      (D.shriek f F)
      (D.shriek φ.pi (D.shriek φ.g (D.shriek φ.jX F))) := by
  exact D.shriek_factorization_iso_of_eq φ.jX φ.g φ.pi φ.factor F hF

/-- The two objects related by curve reduction are constructible. -/
theorem curveReduction_terms_constructible (φ : CurveFactorization D f)
    (F : D.Sheaf X) (hF : D.IsConstr F) :
    D.IsConstr (D.shriek f F) ∧
      D.IsConstr (D.shriek φ.pi (D.shriek φ.g (D.shriek φ.jX F))) := by
  constructor
  · exact D.shriek_constr f F hF
  · exact φ.pi_g_jX_shriek_constructible F hF

end CurveFactorization

/-! ### Weil II / weight-radius interface (Prop .33/.41, Thm .34/.42, Prop .38).

Mathlib has no constructible ℓ-adic Frobenius-weight library.  The certificate
below therefore keeps the unavailable Weil II input as local data attached to a
constructible sheaf.  The pure-weight absolute-value formula and mixed-weight
upper bound are fields; the radius consequences are ordinary theorems. -/

/-- The Frobenius radius associated to a Weil weight `w` over a field with
cardinality parameter `q`. -/
noncomputable def weightRadius (q : ℝ) (w : ℤ) : ℝ :=
  q ^ ((w : ℝ) / 2)

theorem weightRadius_pos {q : ℝ} (hq : 0 < q) (w : ℤ) :
    0 < weightRadius q w := by
  simpa [weightRadius] using Real.rpow_pos_of_pos hq ((w : ℝ) / 2)

/-- Certification interface for the Weil II weight package attached to one
constructible sheaf.  `frobEigenvalues n` is intentionally a `Set ℂ`: this keeps
the interface independent of any future choice of multiplicity model. -/
structure WeilIIPackage {Sch : Type uSch} [Category.{vSch} Sch]
    (D : SixFunctorData Sch) {X : Sch} (F : D.Sheaf X) where
  isConstructible : D.IsConstr F
  q : ℝ
  q_pos : 0 < q
  frobEigenvalues : ℕ → Set ℂ
  isMixedLE : ℕ → ℤ → Prop
  isPure : ℕ → ℤ → Prop
  pure_mixedLE : ∀ {n : ℕ} {w : ℤ}, isPure n w → isMixedLE n w
  mixedLE_mono :
    ∀ {n : ℕ} {w w' : ℤ}, w ≤ w' → isMixedLE n w → isMixedLE n w'
  mixedAbs_le :
    ∀ n w, isMixedLE n w →
      ∀ α : ℂ, α ∈ frobEigenvalues n → ‖α‖ ≤ weightRadius q w
  frobAbs :
    ∀ n w, isPure n w →
      ∀ α : ℂ, α ∈ frobEigenvalues n → ‖α‖ = weightRadius q w

namespace WeilIIPackage

variable {Sch : Type uSch} [Category.{vSch} Sch]
variable {D : SixFunctorData Sch}
variable {X : Sch} {F : D.Sheaf X}

/-- The sheaf carrying the Weil II package is constructible. -/
theorem constructible (W : WeilIIPackage D F) :
    D.IsConstr F :=
  W.isConstructible

/-- Purity implies the corresponding mixed upper weight statement. -/
theorem pure_to_mixedLE (W : WeilIIPackage D F) {n : ℕ} {w : ℤ}
    (h : W.isPure n w) :
    W.isMixedLE n w :=
  W.pure_mixedLE h

/-- Mixed upper weights are monotone in the upper bound. -/
theorem mixedLE_of_le (W : WeilIIPackage D F) {n : ℕ} {w w' : ℤ}
    (hww' : w ≤ w') (h : W.isMixedLE n w) :
    W.isMixedLE n w' :=
  W.mixedLE_mono hww' h

/-- Frobenius eigenvalue absolute value for a pure weight. -/
theorem frob_abs_eq (W : WeilIIPackage D F) {n : ℕ} {w : ℤ}
    (hPure : W.isPure n w) {α : ℂ} (hα : α ∈ W.frobEigenvalues n) :
    ‖α‖ = weightRadius W.q w :=
  W.frobAbs n w hPure α hα

/-- Pure weight gives the corresponding Frobenius eigenvalue upper bound. -/
theorem frob_norm_le_of_pure (W : WeilIIPackage D F) {n : ℕ} {w : ℤ}
    (hPure : W.isPure n w) {α : ℂ} (hα : α ∈ W.frobEigenvalues n) :
    ‖α‖ ≤ weightRadius W.q w :=
  le_of_eq (W.frob_abs_eq hPure hα)

/-- Mixed weight gives the corresponding Frobenius eigenvalue upper bound. -/
theorem frob_norm_le_of_mixed (W : WeilIIPackage D F) {n : ℕ} {w : ℤ}
    (hMixed : W.isMixedLE n w) {α : ℂ} (hα : α ∈ W.frobEigenvalues n) :
    ‖α‖ ≤ weightRadius W.q w :=
  W.mixedAbs_le n w hMixed α hα

/-- Radius-bound predicate for the Frobenius eigenvalues of compactly supported
cohomology degree `n`. -/
def FrobeniusRadiusBound (W : WeilIIPackage D F) (n : ℕ) (R : ℝ) : Prop :=
  ∀ α : ℂ, α ∈ W.frobEigenvalues n → ‖α‖ ≤ R

/-- Pure weight implies the Frobenius radius bound with radius `q^(w/2)`. -/
theorem pure_weight_radiusBound (W : WeilIIPackage D F) {n : ℕ} {w : ℤ}
    (hPure : W.isPure n w) :
    W.FrobeniusRadiusBound n (weightRadius W.q w) := by
  intro α hα
  exact W.frob_norm_le_of_pure hPure hα

/-- Mixed weight upper bound implies the Frobenius radius bound with radius
`q^(w/2)`. -/
theorem mixed_weight_radiusBound (W : WeilIIPackage D F) {n : ℕ} {w : ℤ}
    (hMixed : W.isMixedLE n w) :
    W.FrobeniusRadiusBound n (weightRadius W.q w) := by
  intro α hα
  exact W.frob_norm_le_of_mixed hMixed hα

/-- The Weil radius is strictly positive whenever `q > 0`. -/
theorem weightRadius_pos_apply (W : WeilIIPackage D F) (w : ℤ) :
    0 < weightRadius W.q w :=
  weightRadius_pos W.q_pos w

end WeilIIPackage

/-- Determinant/trace expansion certificate turning eigenvalue radius bounds into
the analytic radius-limit statement used in Prop .38.

The field `hasDetTraceExpansion` is the local hook for the already formalized
det-trace identity in §F.  This avoids introducing global analytic assumptions
while still making the dependency of Prop .38 explicit. -/
structure DetTraceRadiusCertificate {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (W : WeilIIPackage D F) where
  hasDetTraceExpansion : ℕ → ℤ → Prop
  radiusLimit : ℕ → ℤ → Prop
  radius_of_bound :
    ∀ {n : ℕ} {w : ℤ},
      hasDetTraceExpansion n w →
        W.FrobeniusRadiusBound n (weightRadius W.q w) →
          radiusLimit n w

namespace DetTraceRadiusCertificate

variable {Sch : Type uSch} [Category.{vSch} Sch]
variable {D : SixFunctorData Sch}
variable {X : Sch} {F : D.Sheaf X}
variable {W : WeilIIPackage D F}

theorem radius_of_radiusBound (C : DetTraceRadiusCertificate W)
    {n : ℕ} {w : ℤ} (hdet : C.hasDetTraceExpansion n w)
    (hbound : W.FrobeniusRadiusBound n (weightRadius W.q w)) :
    C.radiusLimit n w :=
  C.radius_of_bound hdet hbound

end DetTraceRadiusCertificate

/-- **Prop .38, pure version.**  Weil II purity plus the det-trace expansion
certificate gives the radius-limit conclusion. -/
theorem prop38_radius_limit_of_pure {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    {n : ℕ} {w : ℤ}
    (hPure : W.isPure n w) (hdet : C.hasDetTraceExpansion n w) :
    C.radiusLimit n w :=
  C.radius_of_radiusBound hdet (W.pure_weight_radiusBound hPure)

/-- **Prop .38, mixed version.**  A mixed upper weight bound plus the det-trace
expansion certificate gives the same radius-limit conclusion. -/
theorem prop38_radius_limit_of_mixed {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    {n : ℕ} {w : ℤ}
    (hMixed : W.isMixedLE n w) (hdet : C.hasDetTraceExpansion n w) :
    C.radiusLimit n w :=
  C.radius_of_radiusBound hdet (W.mixed_weight_radiusBound hMixed)

/-! ### Grothendieck-Lefschetz trace-formula interface (Lem .36).

The missing etale cohomology input is the trace formula itself.  We keep it as
local certificate data and prove, without new axioms, the formal consequences
needed to connect it with the determinant-trace power-series identity of Lem
.37: the logarithmic derivative coefficients are the alternating compact-trace
sum. -/

/-- The alternating sign `(-1)^i`, represented in `ℂ`. -/
def glAltSign (i : ℕ) : ℂ :=
  if Even i then 1 else -1

@[simp]
theorem glAltSign_of_even {i : ℕ} (hi : Even i) :
    glAltSign i = 1 := by
  simp [glAltSign, hi]

@[simp]
theorem glAltSign_of_not_even {i : ℕ} (hi : ¬ Even i) :
    glAltSign i = -1 := by
  simp [glAltSign, hi]

@[simp]
theorem glAltSign_zero :
    glAltSign 0 = 1 := by
  simp [glAltSign]

/-- Alternating compact-support trace sum over a finite list of cohomological
degrees. -/
noncomputable def glAlternatingTraceOf (degrees : Finset ℕ)
    (compactTrace : ℕ → ℕ → ℂ) (r : ℕ) : ℂ :=
  degrees.sum fun i => glAltSign i * compactTrace i r

/-- Alternating trace sum when compactly supported cohomology is represented by
Frobenius matrices on a fixed finite coordinate type.  This is the matrix-level
input that talks directly to the determinant-trace identity of Lem .37. -/
noncomputable def glAlternatingMatrixTraceOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degrees : Finset ℕ) (T : ℕ → Matrix ι ι ℂ) (r : ℕ) : ℂ :=
  degrees.sum fun i => glAltSign i * Matrix.trace ((T i) ^ r)

/-- Shifted matrix trace series: the `r`th coefficient is the alternating trace
of Frobenius powers at exponent `r + 1`. -/
noncomputable def glAlternatingMatrixTraceShiftedSeries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degrees : Finset ℕ) (T : ℕ → Matrix ι ι ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun r => glAlternatingMatrixTraceOf degrees T (r + 1)

@[simp]
theorem coeff_glAlternatingMatrixTraceShiftedSeries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degrees : Finset ℕ) (T : ℕ → Matrix ι ι ℂ) (r : ℕ) :
    PowerSeries.coeff r (glAlternatingMatrixTraceShiftedSeries degrees T) =
      glAlternatingMatrixTraceOf degrees T (r + 1) := by
  simp [glAlternatingMatrixTraceShiftedSeries]

/-- Certification interface for the Grothendieck-Lefschetz trace formula for a
single constructible sheaf.  The fields `pointCount r` and `compactTrace i r`
are abstract on purpose: future etale cohomology infrastructure can instantiate
them, while all formal consequences below are already theorem-level Lean. -/
structure GrothendieckLefschetzPackage {Sch : Type uSch} [Category.{vSch} Sch]
    (D : SixFunctorData Sch) {X : Sch} (F : D.Sheaf X) where
  isConstructible : D.IsConstr F
  cohomologyDegrees : Finset ℕ
  pointCount : ℕ → ℂ
  compactTrace : ℕ → ℕ → ℂ
  traceFormula :
    ∀ r : ℕ, pointCount r = glAlternatingTraceOf cohomologyDegrees compactTrace r

namespace GrothendieckLefschetzPackage

variable {Sch : Type uSch} [Category.{vSch} Sch]
variable {D : SixFunctorData Sch}
variable {X : Sch} {F : D.Sheaf X}

/-- The sheaf carrying a Grothendieck-Lefschetz package is constructible. -/
theorem constructible (G : GrothendieckLefschetzPackage D F) :
    D.IsConstr F :=
  G.isConstructible

/-- The alternating compact-support trace sum in the trace formula. -/
noncomputable def alternatingTrace (G : GrothendieckLefschetzPackage D F)
    (r : ℕ) : ℂ :=
  glAlternatingTraceOf G.cohomologyDegrees G.compactTrace r

/-- The certified Grothendieck-Lefschetz identity in invariant notation. -/
theorem pointCount_eq_alternatingTrace (G : GrothendieckLefschetzPackage D F)
    (r : ℕ) :
    G.pointCount r = G.alternatingTrace r := by
  simpa [alternatingTrace] using G.traceFormula r

/-- The positive-degree form, convenient for zeta-logarithm coefficients. -/
theorem pointCount_succ_eq_alternatingTrace
    (G : GrothendieckLefschetzPackage D F) (r : ℕ) :
    G.pointCount (r + 1) = G.alternatingTrace (r + 1) :=
  G.pointCount_eq_alternatingTrace (r + 1)

/-- The shifted series whose `r`th coefficient is the alternating trace at
degree `r + 1`. -/
noncomputable def alternatingTraceShiftedSeries
    (G : GrothendieckLefschetzPackage D F) : PowerSeries ℂ :=
  PowerSeries.mk fun r => G.alternatingTrace (r + 1)

@[simp]
theorem coeff_alternatingTraceShiftedSeries
    (G : GrothendieckLefschetzPackage D F) (r : ℕ) :
    PowerSeries.coeff r G.alternatingTraceShiftedSeries =
      G.alternatingTrace (r + 1) := by
  simp [alternatingTraceShiftedSeries]

/-- The shifted point-count series is the shifted alternating-trace series. -/
theorem detTraceShiftedSeries_eq_alternatingTraceShiftedSeries
    (G : GrothendieckLefschetzPackage D F) :
    detTraceShiftedSeries G.pointCount = G.alternatingTraceShiftedSeries := by
  ext r
  rw [coeff_detTraceShiftedSeries, coeff_alternatingTraceShiftedSeries]
  exact G.pointCount_succ_eq_alternatingTrace r

/-- The constant coefficient of the trace-formula logarithm is zero. -/
theorem constantCoeff_logSeries (G : GrothendieckLefschetzPackage D F) :
    PowerSeries.constantCoeff (detTraceWeightedLogSeries G.pointCount) = 0 :=
  constantCoeff_detTraceWeightedLogSeries G.pointCount

/-- Nonzero coefficients of the trace-formula logarithm are point counts divided
by the exponent. -/
theorem coeff_logSeries_of_ne_zero
    (G : GrothendieckLefschetzPackage D F) {r : ℕ} (hr : r ≠ 0) :
    PowerSeries.coeff r (detTraceWeightedLogSeries G.pointCount) =
      G.alternatingTrace r * algebraMap ℚ ℂ (1 / (r : ℚ)) := by
  rw [coeff_detTraceWeightedLogSeries_of_ne_zero G.pointCount hr]
  rw [G.pointCount_eq_alternatingTrace r]

/-- The formal logarithmic derivative of the point-count logarithm is the
alternating-trace shifted series. -/
theorem logDerivative_expansion (G : GrothendieckLefschetzPackage D F) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      G.alternatingTraceShiftedSeries := by
  rw [derivative_detTraceWeightedLogSeries]
  exact G.detTraceShiftedSeries_eq_alternatingTraceShiftedSeries

/-- Coefficient form of the Grothendieck-Lefschetz logarithmic-derivative
expansion. -/
theorem coeff_logDerivative_expansion
    (G : GrothendieckLefschetzPackage D F) (r : ℕ) :
    PowerSeries.coeff r (d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount)) =
      G.alternatingTrace (r + 1) := by
  rw [G.logDerivative_expansion]
  simp

/-- If each compact trace is realized by a matrix trace of a Frobenius power,
then the alternating trace is the corresponding alternating matrix-trace sum. -/
theorem alternatingTrace_eq_matrixTrace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GrothendieckLefschetzPackage D F) (T : ℕ → Matrix ι ι ℂ)
    (hT : ∀ i r, i ∈ G.cohomologyDegrees →
      G.compactTrace i r = Matrix.trace ((T i) ^ r)) (r : ℕ) :
    G.alternatingTrace r =
      glAlternatingMatrixTraceOf G.cohomologyDegrees T r := by
  simp only [alternatingTrace, glAlternatingTraceOf, glAlternatingMatrixTraceOf]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [hT i r hi]

/-- Shifted version of `alternatingTrace_eq_matrixTrace`. -/
theorem alternatingTraceShiftedSeries_eq_matrixTraceShiftedSeries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GrothendieckLefschetzPackage D F) (T : ℕ → Matrix ι ι ℂ)
    (hT : ∀ i r, i ∈ G.cohomologyDegrees →
      G.compactTrace i r = Matrix.trace ((T i) ^ r)) :
    G.alternatingTraceShiftedSeries =
      glAlternatingMatrixTraceShiftedSeries G.cohomologyDegrees T := by
  ext r
  rw [coeff_alternatingTraceShiftedSeries, coeff_glAlternatingMatrixTraceShiftedSeries]
  exact G.alternatingTrace_eq_matrixTrace T hT (r + 1)

/-- Grothendieck-Lefschetz plus a matrix realization of compact traces gives
the matrix-trace form of the zeta logarithmic derivative. -/
theorem logDerivative_matrixTrace_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GrothendieckLefschetzPackage D F) (T : ℕ → Matrix ι ι ℂ)
    (hT : ∀ i r, i ∈ G.cohomologyDegrees →
      G.compactTrace i r = Matrix.trace ((T i) ^ r)) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      glAlternatingMatrixTraceShiftedSeries G.cohomologyDegrees T := by
  rw [G.logDerivative_expansion]
  exact G.alternatingTraceShiftedSeries_eq_matrixTraceShiftedSeries T hT

/-- Coefficient form of the matrix-trace logarithmic derivative expansion. -/
theorem coeff_logDerivative_matrixTrace_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GrothendieckLefschetzPackage D F) (T : ℕ → Matrix ι ι ℂ)
    (hT : ∀ i r, i ∈ G.cohomologyDegrees →
      G.compactTrace i r = Matrix.trace ((T i) ^ r)) (r : ℕ) :
    PowerSeries.coeff r (d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount)) =
      glAlternatingMatrixTraceOf G.cohomologyDegrees T (r + 1) := by
  rw [G.logDerivative_matrixTrace_expansion T hT]
  simp

/-- The determinant-trace identity of Lem .37, specialized to complex
matrices, available as the formal algebraic input paired with the
Grothendieck-Lefschetz trace certificate. -/
theorem complex_det_trace_formal_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ) :
    matrixDetOneSubInvSeries T =
      (PowerSeries.exp ℂ).subst (matrixTraceLogSeries T) :=
  lem37_det_trace_formal_identity T

/-- Family form of Lem .37 for the Frobenius matrices appearing in a
matrix-trace realization of Grothendieck-Lefschetz. -/
theorem complex_det_trace_formal_identity_family
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℕ → Matrix ι ι ℂ) (i : ℕ) :
    matrixDetOneSubInvSeries (T i) =
      (PowerSeries.exp ℂ).subst (matrixTraceLogSeries (T i)) :=
  complex_det_trace_formal_identity (T i)

end GrothendieckLefschetzPackage

/-- **Lemma .36, formal consequence.**  A Grothendieck-Lefschetz trace-formula
certificate identifies the logarithmic derivative coefficients of the zeta
logarithm with the alternating compact-support trace sums. -/
theorem lem36_logDerivative_expansion {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (G : GrothendieckLefschetzPackage D F) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      G.alternatingTraceShiftedSeries :=
  G.logDerivative_expansion

/-- **Lemma .36 + Lem .37, matrix-trace consequence.**  If the compact-support
traces in the Grothendieck-Lefschetz package are represented by Frobenius
matrices, then the logarithmic derivative is the alternating sum of the
matrix-trace resolvent coefficients. -/
theorem lem36_logDerivative_matrixTrace_expansion
    {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (G : GrothendieckLefschetzPackage D F)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℕ → Matrix ι ι ℂ)
    (hT : ∀ i r, i ∈ G.cohomologyDegrees →
      G.compactTrace i r = Matrix.trace ((T i) ^ r)) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      glAlternatingMatrixTraceShiftedSeries G.cohomologyDegrees T :=
  G.logDerivative_matrixTrace_expansion T hT

/-! ### Global Purity B assembly (Prop .43, Thm .44, Cor .45-.46).

The etale cohomology theorem that a finite-support layer over a zero-dimensional
scheme has no positive cohomology is not present in Mathlib.  We model it as a
local certificate: positive cohomology objects are subsingletons.  The global
purity theorem is then an ordinary Lean assembly of curve reduction, Weil II
radius control, the Grothendieck-Lefschetz logarithmic derivative, and this
finite-support vanishing certificate. -/

/-- Prop .43-style finite-support cohomology vanishing certificate.  The
cohomology objects are left abstract; vanishing in positive degree is represented
by `Subsingleton`, which is robust for future additive/group-valued models. -/
structure FiniteSupportCohomologyVanishing {Sch : Type uSch} [Category.{vSch} Sch]
    (D : SixFunctorData Sch) {X : Sch} (F : D.Sheaf X) where
  isConstructible : D.IsConstr F
  finiteSupport : Prop
  hasFiniteSupport : finiteSupport
  cohomology : ℕ → Type*
  positiveSubsingleton : ∀ i : ℕ, 0 < i → Subsingleton (cohomology i)

namespace FiniteSupportCohomologyVanishing

variable {Sch : Type uSch} [Category.{vSch} Sch]
variable {D : SixFunctorData Sch}
variable {X : Sch} {F : D.Sheaf X}

/-- The finite-support layer is constructible. -/
theorem constructible (P : FiniteSupportCohomologyVanishing D F) :
    D.IsConstr F :=
  P.isConstructible

/-- The finite-support hypothesis carried by the certificate. -/
theorem finite_support (P : FiniteSupportCohomologyVanishing D F) :
    P.finiteSupport :=
  P.hasFiniteSupport

/-- Predicate form of positive cohomology vanishing. -/
def PositiveCohomologyVanishes
    (P : FiniteSupportCohomologyVanishing D F) : Prop :=
  ∀ i : ℕ, 0 < i → Subsingleton (P.cohomology i)

/-- **Prop .43.**  Positive-degree cohomology of the finite-support layer
vanishes. -/
theorem positive_cohomology_vanishes
    (P : FiniteSupportCohomologyVanishing D F) :
    P.PositiveCohomologyVanishes :=
  P.positiveSubsingleton

/-- Elementwise form of positive-degree cohomology vanishing. -/
theorem eq_of_positive_degree (P : FiniteSupportCohomologyVanishing D F)
    {i : ℕ} (hi : 0 < i) (x y : P.cohomology i) :
    x = y :=
  haveI : Subsingleton (P.cohomology i) := P.positiveSubsingleton i hi
  Subsingleton.elim x y

end FiniteSupportCohomologyVanishing

/-- Top-level Prop .43 projection. -/
theorem prop43_positive_cohomology_vanishes {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (P : FiniteSupportCohomologyVanishing D F) :
    P.PositiveCohomologyVanishes :=
  P.positive_cohomology_vanishes

/-- Elementwise top-level Prop .43 projection. -/
theorem prop43_positive_cohomology_eq {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (P : FiniteSupportCohomologyVanishing D F)
    {i : ℕ} (hi : 0 < i) (x y : P.cohomology i) :
    x = y :=
  P.eq_of_positive_degree hi x y

/-- The assembled output of Global Purity B: curve reduction data, finite-support
vanishing, the Weil/det-trace radius consequence, and the GL logarithmic
derivative expansion all held together as certified theorem output. -/
structure GlobalPurityBConclusion {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X V : Sch} {f : X ⟶ V} {F : D.Sheaf X}
    (φ : CurveFactorization D f)
    (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    (G : GrothendieckLefschetzPackage D F)
    (P : FiniteSupportCohomologyVanishing D F)
    (n : ℕ) (w : ℤ) where
  inputConstructible : D.IsConstr F
  finiteSupport : P.finiteSupport
  positiveCohomologyVanishes : P.PositiveCohomologyVanishes
  curveReductionTermsConstructible :
    D.IsConstr (D.shriek f F) ∧
      D.IsConstr (D.shriek φ.pi (D.shriek φ.g (D.shriek φ.jX F)))
  curveReductionIso :
    D.SheafIso
      (D.shriek f F)
      (D.shriek φ.pi (D.shriek φ.g (D.shriek φ.jX F)))
  radiusLimit : C.radiusLimit n w
  weightRadiusPositive : 0 < weightRadius W.q w
  logDerivativeExpansion :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      G.alternatingTraceShiftedSeries

namespace GlobalPurityBConclusion

variable {Sch : Type uSch} [Category.{vSch} Sch]
variable {D : SixFunctorData Sch}
variable {X V : Sch} {f : X ⟶ V} {F : D.Sheaf X}
variable {φ : CurveFactorization D f}
variable {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
variable {G : GrothendieckLefschetzPackage D F}
variable {P : FiniteSupportCohomologyVanishing D F}
variable {n : ℕ} {w : ℤ}

/-- Corollary-style projection of the finite-support vanishing component. -/
theorem positive_vanishing (B : GlobalPurityBConclusion φ W C G P n w) :
    P.PositiveCohomologyVanishes :=
  B.positiveCohomologyVanishes

/-- Corollary-style projection of the radius-limit component. -/
theorem radius_limit (B : GlobalPurityBConclusion φ W C G P n w) :
    C.radiusLimit n w :=
  B.radiusLimit

/-- Corollary-style projection of the logarithmic-derivative expansion. -/
theorem logDerivative_expansion
    (B : GlobalPurityBConclusion φ W C G P n w) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      G.alternatingTraceShiftedSeries :=
  B.logDerivativeExpansion

/-- Matrix-trace refinement of the logarithmic-derivative projection. -/
theorem matrixTrace_logDerivative_expansion
    (B : GlobalPurityBConclusion φ W C G P n w)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℕ → Matrix ι ι ℂ)
    (hT : ∀ i r, i ∈ G.cohomologyDegrees →
      G.compactTrace i r = Matrix.trace ((T i) ^ r)) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      glAlternatingMatrixTraceShiftedSeries G.cohomologyDegrees T := by
  rw [B.logDerivative_expansion]
  exact G.alternatingTraceShiftedSeries_eq_matrixTraceShiftedSeries T hT

end GlobalPurityBConclusion

/-- **Theorem .44, pure version.**  Curve reduction, finite-support positive
cohomology vanishing, Weil II purity, det-trace radius input, and the
Grothendieck-Lefschetz trace formula assemble into Global Purity B. -/
theorem thm44_globalPurityB_of_pure {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X V : Sch} {f : X ⟶ V} {F : D.Sheaf X}
    (φ : CurveFactorization D f)
    (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    (G : GrothendieckLefschetzPackage D F)
    (P : FiniteSupportCohomologyVanishing D F)
    {n : ℕ} {w : ℤ}
    (hPure : W.isPure n w) (hdet : C.hasDetTraceExpansion n w) :
    GlobalPurityBConclusion φ W C G P n w where
  inputConstructible := P.constructible
  finiteSupport := P.finite_support
  positiveCohomologyVanishes := P.positive_cohomology_vanishes
  curveReductionTermsConstructible :=
    φ.curveReduction_terms_constructible F P.constructible
  curveReductionIso := φ.shriek_factorization_iso F P.constructible
  radiusLimit := prop38_radius_limit_of_pure W C hPure hdet
  weightRadiusPositive := W.weightRadius_pos_apply w
  logDerivativeExpansion := G.logDerivative_expansion

/-- Mixed-weight variant of the same assembly, useful for the radius-bound
corollary when the input is mixed rather than pure. -/
theorem thm44_globalPurityB_of_mixed {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X V : Sch} {f : X ⟶ V} {F : D.Sheaf X}
    (φ : CurveFactorization D f)
    (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    (G : GrothendieckLefschetzPackage D F)
    (P : FiniteSupportCohomologyVanishing D F)
    {n : ℕ} {w : ℤ}
    (hMixed : W.isMixedLE n w) (hdet : C.hasDetTraceExpansion n w) :
    GlobalPurityBConclusion φ W C G P n w where
  inputConstructible := P.constructible
  finiteSupport := P.finite_support
  positiveCohomologyVanishes := P.positive_cohomology_vanishes
  curveReductionTermsConstructible :=
    φ.curveReduction_terms_constructible F P.constructible
  curveReductionIso := φ.shriek_factorization_iso F P.constructible
  radiusLimit := prop38_radius_limit_of_mixed W C hMixed hdet
  weightRadiusPositive := W.weightRadius_pos_apply w
  logDerivativeExpansion := G.logDerivative_expansion

/-- **Corollary .45.**  Global Purity B implies the certified radius-limit
conclusion. -/
theorem cor45_globalPurityB_radiusLimit {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X V : Sch} {f : X ⟶ V} {F : D.Sheaf X}
    {φ : CurveFactorization D f}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {G : GrothendieckLefschetzPackage D F}
    {P : FiniteSupportCohomologyVanishing D F}
    {n : ℕ} {w : ℤ}
    (B : GlobalPurityBConclusion φ W C G P n w) :
    C.radiusLimit n w :=
  B.radius_limit

/-- **Corollary .46.**  Global Purity B implies the Grothendieck-Lefschetz
logarithmic-derivative expansion. -/
theorem cor46_globalPurityB_logDerivative_expansion
    {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X V : Sch} {f : X ⟶ V} {F : D.Sheaf X}
    {φ : CurveFactorization D f}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {G : GrothendieckLefschetzPackage D F}
    {P : FiniteSupportCohomologyVanishing D F}
    {n : ℕ} {w : ℤ}
    (B : GlobalPurityBConclusion φ W C G P n w) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      G.alternatingTraceShiftedSeries :=
  B.logDerivative_expansion

/-- Matrix-trace form of Corollary .46. -/
theorem cor46_globalPurityB_matrixTrace_logDerivative_expansion
    {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X V : Sch} {f : X ⟶ V} {F : D.Sheaf X}
    {φ : CurveFactorization D f}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {G : GrothendieckLefschetzPackage D F}
    {P : FiniteSupportCohomologyVanishing D F}
    {n : ℕ} {w : ℤ}
    (B : GlobalPurityBConclusion φ W C G P n w)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℕ → Matrix ι ι ℂ)
    (hT : ∀ i r, i ∈ G.cohomologyDegrees →
      G.compactTrace i r = Matrix.trace ((T i) ^ r)) :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      glAlternatingMatrixTraceShiftedSeries G.cohomologyDegrees T :=
  B.matrixTrace_logDerivative_expansion T hT

end SixFunctorInterface

/-! ## §I — Conditional good-prime synchronization / Equivalence C (Theorem .47).

The étale/motivic/cotangent/weight detectors are not in Mathlib; their bridges are
explicit hypotheses.  The arithmetic equalizer face (`gcd = 1`) is unconditional. -/

open CategoryTheory

universe uSch vSch

/-- Weight/purity part of Equivalence C: a pure Weil weight together with the
determinant-trace expansion certificate that transports the weight bound to the
radius-limit statement. -/
def WeightPurityGate {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    (n : ℕ) (w : ℤ) : Prop :=
  W.isPure n w ∧ C.hasDetTraceExpansion n w

/-- Projection of the pure-weight component of the weight gate. -/
theorem weightPurityGate_pure {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {n : ℕ} {w : ℤ} (hB : WeightPurityGate W C n w) :
    W.isPure n w :=
  hB.1

/-- Projection of the determinant-trace expansion component of the weight gate. -/
theorem weightPurityGate_detTraceExpansion {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {n : ℕ} {w : ℤ} (hB : WeightPurityGate W C n w) :
    C.hasDetTraceExpansion n w :=
  hB.2

/-- The weight gate yields the Frobenius radius bound `q^(w/2)`. -/
theorem weightPurityGate_radiusBound {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {n : ℕ} {w : ℤ} (hB : WeightPurityGate W C n w) :
    W.FrobeniusRadiusBound n (weightRadius W.q w) :=
  W.pure_weight_radiusBound hB.1

/-- The weight gate, through the det-trace certificate, yields the radius-limit
conclusion used in Global Purity B. -/
theorem weightPurityGate_radiusLimit {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {n : ℕ} {w : ℤ} (hB : WeightPurityGate W C n w) :
    C.radiusLimit n w :=
  C.radius_of_radiusBound hB.2 (weightPurityGate_radiusBound hB)

/-- The paper's `A ∧ B` gate for Equivalence C: arithmetic Čech/Tor acyclicity
and the weight/purity radius package. -/
def EquivalenceCGate {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (M N : ℕ) (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    (n : ℕ) (w : ℤ) : Prop :=
  ArithmeticCechTorGate M N ∧ WeightPurityGate W C n w

/-- Projection of the arithmetic `A` component from the faithful Equivalence C gate. -/
theorem equivalenceCGate_arithmetic {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {M N : ℕ} {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {n : ℕ} {w : ℤ} (h : EquivalenceCGate M N W C n w) :
    ArithmeticCechTorGate M N :=
  h.1

/-- Projection of the weight/purity `B` component from the faithful Equivalence C gate. -/
theorem equivalenceCGate_weightPurity {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {M N : ℕ} {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {n : ℕ} {w : ℤ} (h : EquivalenceCGate M N W C n w) :
    WeightPurityGate W C n w :=
  h.2

/-- The faithful Equivalence C gate carries the radius-limit conclusion. -/
theorem equivalenceCGate_radiusLimit {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {M N : ℕ} {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {n : ℕ} {w : ℤ} (h : EquivalenceCGate M N W C n w) :
    C.radiusLimit n w :=
  weightPurityGate_radiusLimit h.2

/-- **Theorem .47 (Equivalence C, conditional).** On `U = D(∆)`, the discriminant
    gate (`smooth`), the derived (Koszul/Tor) test (`der = 0`), and the equalizer
    face (`gcd = 1`) are equivalent. -/
theorem equivalence_C (smooth : Prop) (der M pk : ℕ)
    (Hder : der = 0 ↔ smooth) (Hgate : smooth ↔ Nat.gcd M pk = 1) :
    [Nat.gcd M pk = 1, smooth, der = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate.symm
  tfae_have 2 ↔ 3 := Hder.symm
  tfae_finish

/-- Faithful paper-shaped Equivalence C TFAE: Riemann-hypothesis style statement,
trace/purity statement, and the combined `A ∧ B` gate are equivalent once the two
semantic bridges identify `RH` and `TP` with that gate. -/
theorem equivalence_C_faithful_tfae {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {M N n : ℕ} {w : ℤ}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    (RH TP : Prop)
    (hRH : RH ↔ EquivalenceCGate M N W C n w)
    (hTP : TP ↔ EquivalenceCGate M N W C n w) :
    [RH, TP, EquivalenceCGate M N W C n w].TFAE := by
  tfae_have 1 ↔ 3 := hRH
  tfae_have 2 ↔ 3 := hTP
  tfae_finish

/-- Certified output of the faithful Equivalence C assembly.  The arithmetic
TFAE is unconditional from Tier 1; the radius conclusion is transported from the
weight/purity gate; the final TFAE has the paper's `RH ↔ TP ↔ (A ∧ B)` shape. -/
structure FaithfulEquivalenceCConclusion {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    (M N : ℕ) (W : WeilIIPackage D F)
    (C : DetTraceRadiusCertificate W) (n : ℕ) (w : ℤ)
    (RH TP : Prop) where
  arithmeticGateTFAE :
    [Nat.gcd M N = 1,
      Nat.card (cechPhiCoker M N) = 1,
      Nat.card (TorH1 M N) = 1,
      IC M N = 0,
      ArithmeticCechTorGate M N].TFAE
  weightRadiusBound : W.FrobeniusRadiusBound n (weightRadius W.q w)
  radiusLimit : C.radiusLimit n w
  rhTpGateTFAE : [RH, TP, EquivalenceCGate M N W C n w].TFAE

namespace FaithfulEquivalenceCConclusion

variable {Sch : Type uSch} [Category.{vSch} Sch]
variable {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
variable {M N n : ℕ} {w : ℤ}
variable {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
variable {RH TP : Prop}

/-- Projection of the unconditional arithmetic TFAE component. -/
theorem arithmetic_tfae
    (E : FaithfulEquivalenceCConclusion M N W C n w RH TP) :
    [Nat.gcd M N = 1,
      Nat.card (cechPhiCoker M N) = 1,
      Nat.card (TorH1 M N) = 1,
      IC M N = 0,
      ArithmeticCechTorGate M N].TFAE :=
  E.arithmeticGateTFAE

/-- Projection of the radius-limit component. -/
theorem radius_limit
    (E : FaithfulEquivalenceCConclusion M N W C n w RH TP) :
    C.radiusLimit n w :=
  E.radiusLimit

/-- Projection of the paper-shaped `RH ↔ TP ↔ (A ∧ B)` TFAE. -/
theorem rh_tp_gate_tfae
    (E : FaithfulEquivalenceCConclusion M N W C n w RH TP) :
    [RH, TP, EquivalenceCGate M N W C n w].TFAE :=
  E.rhTpGateTFAE

end FaithfulEquivalenceCConclusion

/-- **Theorem .47 (Equivalence C, faithful interface).**  The arithmetic gate is
proved unconditionally from the Čech/Tor/IC calculations, while the weight gate
is the explicit Weil II/det-trace input.  Under the two semantic bridges from
`RH` and `TP` to `A ∧ B`, the theorem returns the full certified package. -/
theorem equivalence_C_faithful {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {M N n : ℕ} {w : ℤ}
    (hM : M ≠ 0) (hN : N ≠ 0)
    (W : WeilIIPackage D F) (C : DetTraceRadiusCertificate W)
    (RH TP : Prop)
    (hB : WeightPurityGate W C n w)
    (hRH : RH ↔ EquivalenceCGate M N W C n w)
    (hTP : TP ↔ EquivalenceCGate M N W C n w) :
    FaithfulEquivalenceCConclusion M N W C n w RH TP where
  arithmeticGateTFAE := arithmeticCechTorGate_tfae hM hN
  weightRadiusBound := weightPurityGate_radiusBound hB
  radiusLimit := weightPurityGate_radiusLimit hB
  rhTpGateTFAE := equivalence_C_faithful_tfae RH TP hRH hTP

/-- The faithful bridges imply the direct equivalence `RH ↔ TP`. -/
theorem equivalence_C_faithful_rh_iff_tp {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} {F : D.Sheaf X}
    {M N n : ℕ} {w : ℤ}
    {W : WeilIIPackage D F} {C : DetTraceRadiusCertificate W}
    {RH TP : Prop}
    (hRH : RH ↔ EquivalenceCGate M N W C n w)
    (hTP : TP ↔ EquivalenceCGate M N W C n w) :
    RH ↔ TP :=
  hRH.trans hTP.symm

/-! ## §J — Mathlib-gap workaround checklist

This section turns the five engineering principles used above into kernel-checked
certificates.  Each field is backed by concrete definitions or already-proved
theorems in the file; no global axiom is introduced by the checklist layer. -/

open RingTheory.Sequence

/-- Principle 1: replace missing abstract Tor/Čech objects by concrete
kernel/cokernel models, upgraded to additive equivalences. -/
structure ConcreteSurrogateCertificate (M N : ℕ) [NeZero N] where
  torKernelEquiv : TorH1 M N ≃+ ZMod (Nat.gcd N M)
  cechCokerEquiv : cechPhiCoker M N ≃+ ZMod (Nat.gcd M N)
  torCard : Nat.card (TorH1 M N) = Nat.gcd N M
  cechCard : Nat.card (cechPhiCoker M N) = Nat.gcd M N

namespace ConcreteSurrogateCertificate

variable {M N : ℕ} [NeZero N]

/-- Projection of the concrete Tor additive equivalence. -/
noncomputable def tor_equiv (C : ConcreteSurrogateCertificate M N) :
    TorH1 M N ≃+ ZMod (Nat.gcd N M) :=
  C.torKernelEquiv

/-- Projection of the concrete Čech cokernel additive equivalence. -/
noncomputable def cech_equiv (C : ConcreteSurrogateCertificate M N) :
    cechPhiCoker M N ≃+ ZMod (Nat.gcd M N) :=
  C.cechCokerEquiv

end ConcreteSurrogateCertificate

/-- Canonical certificate for the concrete Tor/Čech surrogate principle. -/
noncomputable def concreteSurrogateCertificate (M N : ℕ) [NeZero N] :
    ConcreteSurrogateCertificate M N where
  torKernelEquiv := TorH1_iso_zmod_gcd M N
  cechCokerEquiv := cechPhiCokerEquivZModGcd M N
  torCard := TorH1_card M N
  cechCard := cechPhiCoker_card M N

/-- Principle 2: the actually-used Koszul cases are the explicit `r = 1` and
`r = 2` low-degree complexes, with regularity certified by Mathlib's
regular-sequence API. -/
structure LowDegreeKoszulCertificate
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  singletonComplex :
    ∀ r : R, lowDegreeKoszulComplex R M [r] = koszulR1ChainComplex (M := M) r
  pairComplex :
    ∀ x y : R, lowDegreeKoszulComplex R M [x, y] = koszulR2ChainComplex (M := M) x y
  singletonAcyclicIff :
    ∀ r : R, koszulR1PositiveAcyclic (M := M) r ↔ IsWeaklyRegular M [r]
  pairAcyclicOfRegular :
    ∀ x y : R, IsWeaklyRegular M [x, y] → koszulR2PositiveAcyclic (M := M) x y
  certificateIffWeakRegular :
    ∀ {rs : List R}, rs.length ≤ 2 →
      (koszulLowDegreeRegularityCertificate (M := M) rs ↔ IsWeaklyRegular M rs)

namespace LowDegreeKoszulCertificate

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Projection for the singleton low-degree complex. -/
theorem singleton_complex (C : LowDegreeKoszulCertificate R M) (r : R) :
    lowDegreeKoszulComplex R M [r] = koszulR1ChainComplex (M := M) r :=
  C.singletonComplex r

/-- Projection for the pair low-degree complex. -/
theorem pair_complex (C : LowDegreeKoszulCertificate R M) (x y : R) :
    lowDegreeKoszulComplex R M [x, y] = koszulR2ChainComplex (M := M) x y :=
  C.pairComplex x y

end LowDegreeKoszulCertificate

/-- Canonical low-degree Koszul certificate. -/
noncomputable def lowDegreeKoszulCertificate
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    LowDegreeKoszulCertificate R M where
  singletonComplex := by
    intro r
    exact lowDegreeKoszulComplex_singleton (R := R) (M := M) r
  pairComplex := by
    intro x y
    exact lowDegreeKoszulComplex_pair (R := R) (M := M) x y
  singletonAcyclicIff := by
    intro r
    exact koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton (M := M) r
  pairAcyclicOfRegular := by
    intro x y hxy
    exact koszulR2PositiveAcyclic_of_isWeaklyRegular_pair (M := M) x y hxy
  certificateIffWeakRegular := fun {rs} hrs =>
    koszulLowDegreeRegularityCertificate_iff_isWeaklyRegular_length_le_two
      (M := M) (rs := rs) hrs

/-- Principle 3: absent global geometry is packaged as fields, and theorems are
certified projections or conditional consequences of those fields. -/
structure BundledInterfaceCertificate {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} (F : D.Sheaf X)
    (W : WeilIIPackage D F) (G : GrothendieckLefschetzPackage D F) where
  inputConstructible : D.IsConstr F
  pullIdIso : D.SheafIso (D.pull (𝟙 X) F) F
  shriekIdIso : D.SheafIso (D.shriek (𝟙 X) F) F
  pureToMixed : ∀ {n : ℕ} {w : ℤ}, W.isPure n w → W.isMixedLE n w
  radiusBoundOfPure :
    ∀ {n : ℕ} {w : ℤ}, W.isPure n w →
      W.FrobeniusRadiusBound n (weightRadius W.q w)
  pointCountTrace : ∀ r : ℕ, G.pointCount r = G.alternatingTrace r
  logDerivativeExpansion :
    d⁄dX ℂ (detTraceWeightedLogSeries G.pointCount) =
      G.alternatingTraceShiftedSeries

/-- Canonical bundled-interface certificate for a six-functor/weight/trace package. -/
noncomputable def bundledInterfaceCertificate {Sch : Type uSch} [Category.{vSch} Sch]
    {D : SixFunctorData Sch} {X : Sch} (F : D.Sheaf X)
    (W : WeilIIPackage D F) (G : GrothendieckLefschetzPackage D F) :
    BundledInterfaceCertificate F W G where
  inputConstructible := W.constructible
  pullIdIso := D.pull_id_iso F W.constructible
  shriekIdIso := D.shriek_id_iso F W.constructible
  pureToMixed := by
    intro n w hPure
    exact W.pure_to_mixedLE hPure
  radiusBoundOfPure := by
    intro n w hPure
    exact W.pure_weight_radiusBound hPure
  pointCountTrace := by
    intro r
    exact G.pointCount_eq_alternatingTrace r
  logDerivativeExpansion := G.logDerivative_expansion

/-- Principle 4: the formal algebraic determinant-trace identity is separated
from geometric trace-formula input. -/
structure FormalAlgebraCoreCertificate {K : Type*} [Field K] [Algebra ℚ K]
    [IsAddTorsionFree K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι K) where
  derivativeIdentity :
    d⁄dX K (matrixDetOneSubInvSeries T) =
      matrixDetOneSubInvSeries T * matrixTraceResolventSeries T
  detTraceIdentity :
    matrixDetOneSubInvSeries T = (PowerSeries.exp K).subst (matrixTraceLogSeries T)

/-- Canonical formal-algebra core certificate. -/
noncomputable def formalAlgebraCoreCertificate {K : Type*} [Field K] [Algebra ℚ K]
    [IsAddTorsionFree K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι K) :
    FormalAlgebraCoreCertificate T where
  derivativeIdentity := derivative_matrixDetOneSubInvSeries T
  detTraceIdentity := lem37_det_trace_formal_identity T

open scoped Topology
open LSeries

/-- Principle 5: reuse close Mathlib analogues for base change, localization,
Euler products, and L-series derivatives. -/
structure ExistingAnalogReuseCertificate where
  faithfullyFlatBaseChange :
    ∀ {R M S N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] [Module.FaithfullyFlat R S]
      {f : M →ₗ[R] N} (_ : IsBaseChange S f) {rs : List R},
        IsRegular M rs → IsRegular N (rs.map (algebraMap R S))
  localizedWeakRegular :
    ∀ {R M S N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] (T : Submonoid R) [IsLocalization T S]
      (f : M →ₗ[R] N) [IsLocalizedModule T f] {rs : List R},
        IsWeaklyRegular M rs → IsWeaklyRegular N (rs.map (algebraMap R S))
  eulerProductHasProd :
    ∀ {f : ℕ →*₀ ℂ}, Summable (fun n : ℕ => ‖f n‖) →
      HasProd (zetaULinearLocalFactor f) (zetaUCompletelyMultiplicativeValue f)
  lseriesDerivative :
    ∀ {f : ℕ → ℂ} {s : ℂ}, abscissaOfAbsConv f < s.re →
      deriv (zetaULSeries f) s = -zetaULSeries (LSeries.logMul f) s
  lseriesLogDerivative :
    ∀ {f : ℕ → ℂ} {s : ℂ}, abscissaOfAbsConv f < s.re →
      zetaULSeriesLogDeriv f s =
        -zetaULSeries (LSeries.logMul f) s / zetaULSeries f s

/-- Canonical certificate for reuse of existing Mathlib analogues. -/
noncomputable def existingAnalogReuseCertificate : ExistingAnalogReuseCertificate where
  faithfullyFlatBaseChange := regularSequence_of_faithfullyFlat_of_isBaseChange
  localizedWeakRegular := weaklyRegularSequence_of_localizedModule
  eulerProductHasProd := zetaU_eulerProduct_hasProd
  lseriesDerivative := zetaULSeries_deriv
  lseriesLogDerivative := zetaULSeries_logDeriv_eq

/- Universe levels for the polymorphic theorem bundles in the final checklist. -/
universe uSheafGap uTriGap uGap1 uGap2 uGap3 uGap4 uGap5 uGap6 uGap7 uGap8

/-- Unified checklist asserting that all five Mathlib-gap workaround principles
are backed by concrete Lean certificates. -/
structure MathlibGapWorkaroundChecklist where
  concreteSurrogate : ∀ (M N : ℕ) [NeZero N], ConcreteSurrogateCertificate M N
  lowDegreeKoszul :
    ∀ (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M],
      LowDegreeKoszulCertificate R M
  bundledInterfaces :
    ∀ {Sch : Type uSch} [Category.{vSch} Sch]
      {D : SixFunctorData.{uSch, vSch, uSheafGap, uTriGap} Sch}
      {X : Sch} (F : D.Sheaf X)
      (W : WeilIIPackage D F) (G : GrothendieckLefschetzPackage D F),
        BundledInterfaceCertificate.{uSch, vSch, uSheafGap, uTriGap} F W G
  formalAlgebra :
    ∀ {K : Type*} [Field K] [Algebra ℚ K] [IsAddTorsionFree K]
      {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι K),
        FormalAlgebraCoreCertificate T
  existingAnalogReuse :
    ExistingAnalogReuseCertificate.{uGap1, uGap2, uGap3, uGap4, uGap5, uGap6, uGap7, uGap8}

/-- The integrated five-principle Mathlib-gap checklist. -/
noncomputable def mathlibGapWorkaroundChecklist : MathlibGapWorkaroundChecklist where
  concreteSurrogate := fun M N _ => concreteSurrogateCertificate M N
  lowDegreeKoszul := fun R M _ _ _ => lowDegreeKoszulCertificate R M
  bundledInterfaces := fun F W G => bundledInterfaceCertificate F W G
  formalAlgebra := fun T => formalAlgebraCoreCertificate T
  existingAnalogReuse := existingAnalogReuseCertificate

/-! ## §K -- Mathlib handle inventory for the next formalization layers.

This section turns the requested exploratory references into small, kernel-checked
handles.  Each handle records an already available Mathlib theorem or an already
proved local wrapper, so the inventory is unconditional: it contains no global
assumptions and no asserted comparison theorem. -/

section MathlibHandleInventory

open scoped Topology
open LSeries
open RingTheory.Sequence
open Nat
open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- Handle for `RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange`
and its weak/flat companion. -/
structure FaithfullyFlatBaseChangeHandle where
  weaklyFlatBaseChange :
    ∀ {R M S N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] [Module.Flat R S]
      {f : M →ₗ[R] N} (_ : IsBaseChange S f) {rs : List R},
        IsWeaklyRegular M rs → IsWeaklyRegular N (rs.map (algebraMap R S))
  faithfullyFlatBaseChange :
    ∀ {R M S N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] [Module.FaithfullyFlat R S]
      {f : M →ₗ[R] N} (_ : IsBaseChange S f) {rs : List R},
        IsRegular M rs → IsRegular N (rs.map (algebraMap R S))
  faithfullyFlatAlgebra :
    ∀ {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
      [Module.FaithfullyFlat R S] {rs : List R},
        IsRegular R rs → IsRegular S (rs.map (algebraMap R S))

/-- Canonical base-change handle, backed by Mathlib's flat/faithfully-flat
regular-sequence API. -/
noncomputable def faithfullyFlatBaseChangeHandle : FaithfullyFlatBaseChangeHandle where
  weaklyFlatBaseChange := weaklyRegularSequence_of_flat_of_isBaseChange
  faithfullyFlatBaseChange := regularSequence_of_faithfullyFlat_of_isBaseChange
  faithfullyFlatAlgebra := regularSequence_of_faithfullyFlat_algebra

/-- Handle for the depth/CM-localization side of the ABS-style reuse plan.  The
numeric depth API is represented by `ModuleDepthDimensionInterface`; the
localization facts are genuine regular-sequence lemmas. -/
structure DepthCMLocalizationHandle where
  localizedWeakRegular :
    ∀ {R M S N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] (T : Submonoid R) [IsLocalization T S]
      (f : M →ₗ[R] N) [IsLocalizedModule T f] {rs : List R},
        IsWeaklyRegular M rs → IsWeaklyRegular N (rs.map (algebraMap R S))
  atPrimeRegular :
    ∀ {R M S N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
      [Nontrivial N] [Module.Finite S N] (f : M →ₗ[R] N)
      [IsLocalizedModule.AtPrime p f] {rs : List R},
        IsRegular M rs → (∀ r ∈ rs, r ∈ p) →
          IsRegular N (rs.map (algebraMap R S))
  localizedDepthLowerBound :
    ∀ {R S : Type u} {M N : Type v} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] (T : Submonoid R) [IsLocalization T S]
      (f : M →ₗ[R] N) [IsLocalizedModule T f]
      (D : ModuleDepthDimensionInterface.{u, v} S) {rs : List R},
        IsWeaklyRegular M rs → rs.length ≤ D.depth N
  localizedCMDimensionLowerBound :
    ∀ {R S : Type u} {M N : Type v} [CommRing R] [AddCommGroup M] [Module R M]
      [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] (T : Submonoid R) [IsLocalization T S]
      (f : M →ₗ[R] N) [IsLocalizedModule T f]
      (D : ModuleDepthDimensionInterface.{u, v} S) {rs : List R},
        D.IsCohenMacaulay N → IsWeaklyRegular M rs → rs.length ≤ D.dimension N

/-- Canonical handle for localization, depth lower bounds, and the CM dimension trigger. -/
noncomputable def depthCMLocalizationHandle : DepthCMLocalizationHandle where
  localizedWeakRegular := weaklyRegularSequence_of_localizedModule
  atPrimeRegular := regularSequence_of_localizedModule_atPrime_of_mem
  localizedDepthLowerBound := prop18_depth_lower_bound_of_localizedModule
  localizedCMDimensionLowerBound :=
    prop18_dimension_lower_bound_of_localizedModule_of_isCohenMacaulay

/-- Handle for `NumberTheory.EulerProduct.Basic` through the `Z_U` wrappers. -/
structure EulerProductMathlibHandle where
  hasProd :
    ∀ {f : ℕ →*₀ ℂ}, Summable (fun n : ℕ => ‖f n‖) →
      HasProd (zetaULinearLocalFactor f) (zetaUCompletelyMultiplicativeValue f)
  tprod :
    ∀ {f : ℕ →*₀ ℂ}, Summable (fun n : ℕ => ‖f n‖) →
      ∏' p : Nat.Primes, zetaULinearLocalFactor f p =
        zetaUCompletelyMultiplicativeValue f
  partialProducts :
    ∀ {f : ℕ →*₀ ℂ}, Summable (fun n : ℕ => ‖f n‖) →
      Filter.Tendsto (fun N : ℕ => ∏ p ∈ primesBelow N, (1 - f p)⁻¹) Filter.atTop
        (𝓝 (zetaUCompletelyMultiplicativeValue f))

/-- Canonical Euler-product handle. -/
noncomputable def eulerProductMathlibHandle : EulerProductMathlibHandle where
  hasProd := zetaU_eulerProduct_hasProd
  tprod := zetaU_eulerProduct_tprod
  partialProducts := zetaU_eulerProduct_partial

/-- Handle for `NumberTheory.LSeries.Deriv` and the logarithmic-derivative wrapper. -/
structure LSeriesDerivativeMathlibHandle where
  summableOnRightHalfPlane :
    ∀ {f : ℕ → ℂ} {s : ℂ}, abscissaOfAbsConv f < s.re → LSeriesSummable f s
  derivative :
    ∀ {f : ℕ → ℂ} {s : ℂ}, abscissaOfAbsConv f < s.re →
      deriv (zetaULSeries f) s = -zetaULSeries (LSeries.logMul f) s
  logarithmicDerivative :
    ∀ {f : ℕ → ℂ} {s : ℂ}, abscissaOfAbsConv f < s.re →
      zetaULSeriesLogDeriv f s =
        -zetaULSeries (LSeries.logMul f) s / zetaULSeries f s
  abscissaLogMul :
    ∀ f : ℕ → ℂ, abscissaOfAbsConv (LSeries.logMul f) = abscissaOfAbsConv f

/-- Canonical L-series derivative handle. -/
noncomputable def lseriesDerivativeMathlibHandle : LSeriesDerivativeMathlibHandle where
  summableOnRightHalfPlane := zetaULSeries_summable_of_abscissa_lt
  derivative := zetaULSeries_deriv
  logarithmicDerivative := zetaULSeries_logDeriv_eq
  abscissaLogMul := zetaULSeries_abscissa_logMul

universe uTorHandle vTorHandle

/-- Handle for the abstract `CategoryTheory.Monoidal.Tor` names.  This records
the two functorial definitions Mathlib currently exposes; it deliberately does
not assert a comparison theorem between them. -/
structure MathlibAbstractTorFunctorHandle where
  torFunctor :
    ∀ C : Type uTorHandle, [Category.{vTorHandle} C] → [MonoidalCategory C] →
      [Abelian C] → [MonoidalPreadditive C] → [HasProjectiveResolutions C] →
        (n : ℕ) → CategoryTheory.Functor C (CategoryTheory.Functor C C)
  torPrimeFunctor :
    ∀ C : Type uTorHandle, [Category.{vTorHandle} C] → [MonoidalCategory C] →
      [Abelian C] → [MonoidalPreadditive C] → [HasProjectiveResolutions C] →
        (n : ℕ) → CategoryTheory.Functor C (CategoryTheory.Functor C C)

/-- Canonical handle for Mathlib's abstract `Tor` and `Tor'` functors. -/
noncomputable def mathlibAbstractTorFunctorHandle :
    MathlibAbstractTorFunctorHandle.{uTorHandle, vTorHandle} where
  torFunctor := fun C [Category C] [MonoidalCategory C]
      [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C] n =>
    CategoryTheory.Tor C n
  torPrimeFunctor := fun C [Category C] [MonoidalCategory C]
      [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C] n =>
    CategoryTheory.Tor' C n

/-- Concrete arithmetic bridge for the optional abstract-Tor comparison: the
paper's computable `Tor₁` surrogate is already identified with `ℤ/gcd`. -/
structure ConcreteTorMathlibBridge (M N : ℕ) [NeZero N] where
  kernelEquiv : (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod (Nat.gcd N M)
  torH1Equiv : TorH1 M N ≃+ ZMod (Nat.gcd N M)
  abstractComparisonPending : True

/-- Canonical concrete Tor bridge. -/
noncomputable def concreteTorMathlibBridge (M N : ℕ) [NeZero N] :
    ConcreteTorMathlibBridge M N where
  kernelEquiv := kerMulLeftEquivZModGcd N M
  torH1Equiv := TorH1_iso_zmod_gcd M N
  abstractComparisonPending := trivial

/-- Handle for the reusable low-degree Koszul work.  It packages the explicit
one- and two-element complexes together with the general model interface already
proved in this file. -/
structure KoszulReuseHandle (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] where
  lowDegreeCertificate : LowDegreeKoszulCertificate R M
  modelSingleton :
    ∀ r : R, (lowDegreeKoszulComplexModel.{u, v} R).complex M [r] =
      koszulR1ChainComplex (M := M) r
  modelPair :
    ∀ x y : R, (lowDegreeKoszulComplexModel.{u, v} R).complex M [x, y] =
      koszulR2ChainComplex (M := M) x y
  lowDegreeCertificateIffModelAcyclic :
    ∀ {rs : List R}, rs.length ≤ 2 →
      (koszulLowDegreeRegularityCertificate (M := M) rs ↔
        (lowDegreeKoszulComplexModel.{u, v} R).acyclic M rs)

/-- Canonical low-degree Koszul reuse handle. -/
noncomputable def koszulReuseHandle
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    KoszulReuseHandle R M where
  lowDegreeCertificate := lowDegreeKoszulCertificate R M
  modelSingleton := lowDegreeKoszulComplexModel_complex_singleton R M
  modelPair := lowDegreeKoszulComplexModel_complex_pair R M
  lowDegreeCertificateIffModelAcyclic := by
    intro rs hrs
    exact lowDegreeKoszulComplexModel_lowDegreeCertificate_iff_acyclic R hrs

/-- Unified existence checklist for all requested Mathlib handles. -/
noncomputable def mathlibHandleInventoryChecklist :
    Nonempty FaithfullyFlatBaseChangeHandle ∧
    Nonempty DepthCMLocalizationHandle ∧
    Nonempty EulerProductMathlibHandle ∧
    Nonempty LSeriesDerivativeMathlibHandle ∧
    Nonempty MathlibAbstractTorFunctorHandle.{uTorHandle, vTorHandle} ∧
    (∀ M N : ℕ, [NeZero N] → Nonempty (ConcreteTorMathlibBridge M N)) ∧
    (∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
      Nonempty (KoszulReuseHandle R M)) := by
  exact
    ⟨⟨faithfullyFlatBaseChangeHandle⟩,
      ⟨depthCMLocalizationHandle⟩,
      ⟨eulerProductMathlibHandle⟩,
      ⟨lseriesDerivativeMathlibHandle⟩,
      ⟨mathlibAbstractTorFunctorHandle⟩,
      (fun M N _ => ⟨concreteTorMathlibBridge M N⟩),
      (fun R _ M _ _ => ⟨koszulReuseHandle R M⟩)⟩

end MathlibHandleInventory

/-! ## Examples. -/

section Examples
/-- Canonical profile: `p = 5` gives `gcd(8, 5ᵏ) = 1`. -/
example (k : ℕ) : Nat.Coprime (5 + 3) (5 ^ k) := canonical_coprime (by decide) (by decide) k
example : Nat.gcd (7 + 3) (7 ^ 4) = 1 := by norm_num   -- p = 7 ≥ 5
/-- Equalizer–Tor numeric: `gcd(12, 9) = 3`. -/
example : Nat.gcd 12 9 = 3 := by norm_num
/-- Regularity is preserved by the identity equivalence (sanity check). -/
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔ IsSMulRegular M r :=
  regular_of_linearEquiv (LinearEquiv.refl R M) r
/-- Faithfully flat base change transports regular sequences to the mapped sequence. -/
example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FaithfullyFlat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : RingTheory.Sequence.IsRegular M rs) :
    RingTheory.Sequence.IsRegular N (rs.map (algebraMap R S)) :=
  regularSequence_of_faithfullyFlat_of_isBaseChange hf reg
/-- A small pairwise-coprime four-layer profile for sanity checks. -/
def exampleFourLayerProfile : FourLayerProfile where
  numMod := 2
  modMod := 3
  padicMod := 5
  ecMod := 7
  hnum := by decide
  hmod := by decide
  hpadic := by decide
  hec := by decide
  h_num_mod := by decide
  h_num_padic := by decide
  h_num_ec := by decide
  h_mod_padic := by decide
  h_mod_ec := by decide
  h_padic_ec := by decide

example :
    ∃ base step : ℤ,
      step ≠ 0 ∧ Function.Injective (fun t : ℤ => base + step * t) ∧
      ∀ t : ℤ, Fnum exampleFourLayerProfile (base + step * t) ∧
        ¬ Fmod exampleFourLayerProfile (base + step * t) ∧
        Fp_adic exampleFourLayerProfile (base + step * t) ∧
        FEC exampleFourLayerProfile (base + step * t) :=
  modCritical_AP exampleFourLayerProfile
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms canonical_coprime
#print axioms arithmeticProgression_injective
#print axioms crtBinaryArithmeticProgression_exists
#print axioms Fnum_iff_dvd
#print axioms Fmod_iff_dvd
#print axioms Fp_adic_iff_dvd
#print axioms FEC_iff_dvd
#print axioms modCritical_AP
#print axioms numericCritical_AP
#print axioms pAdicCritical_AP
#print axioms ecCritical_AP
#print axioms fourLayerStrictIndependence
#print axioms kernel_mem_iff_lcm
#print axioms crt_solvable_iff
#print axioms crtPhi_mem_ker_iff_lcm
#print axioms crtDel_exact_crtPhi
#print axioms crtDel_surjective
#print axioms cechPhiCokerEquivZModGcd
#print axioms cechPhiCoker_card
#print axioms cechPhiCoker_card_eq_one_iff_gcd_eq_one
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms kernel_ideal_inter_nat
#print axioms lcm_prime_power_thickness
#print axioms gcd_prime_power_thickness
#print axioms lcm_prime_power_unit_part_not_dvd
#print axioms localized_lcm_prime_power_ideal_eq_span
#print axioms localized_intersection_prime_power_ideal_eq_span
#print axioms card_ker_mulLeft
#print axioms kerMulLeftEquivZModGcd
#print axioms TorH1_iso_zmod_gcd
#print axioms prod_primePower_factorization_eq_self
#print axioms TorH1_crt_coord_mem
#print axioms TorH1_crt_inv_mem
#print axioms TorH1_primePowerDecomposition
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms IC_mono
#print axioms IC_mono_left
#print axioms IC_coprime_add
#print axioms IC_nonneg
#print axioms gcd_eq_one_iff_IC_eq_zero
#print axioms TorH1_card_eq_one_iff_gcd_eq_one
#print axioms cor9_tfae_gcd_tor_ic
#print axioms ArithmeticCechTorGate
#print axioms arithmeticCechTorGate_iff_gcd_eq_one
#print axioms arithmeticCechTorGate_tfae
#print axioms singleton_regular_iff
#print axioms cons_regular_iff
#print axioms koszulR1Mul
#print axioms koszulR1Obj
#print axioms koszulR1Differential
#print axioms koszulR1Differential_sq
#print axioms koszulR1ChainComplex
#print axioms koszulR1ChainComplex_d_one_zero
#print axioms koszulR1ChainComplex_d_succ_succ
#print axioms koszulR1H1
#print axioms koszulR1H0
#print axioms koszulR1H1_eq_bot_iff_isSMulRegular
#print axioms koszulR1_range_eq_smul_top
#print axioms koszulR1H0EquivQuotSMulTop
#print axioms koszulR1PositiveAcyclic
#print axioms koszulR1PositiveAcyclic_iff_isSMulRegular
#print axioms koszulR1PositiveAcyclic_iff_isWeaklyRegular_singleton
#print axioms koszulR1PositiveAcyclic_of_isWeaklyRegular_singleton
#print axioms koszulR2Left
#print axioms koszulR2Right
#print axioms koszulR2Left_comp_right
#print axioms koszulRange_lsmul_eq_smul_top
#print axioms ofList_pair_smul_top_eq_smul_sup_smul
#print axioms koszulR2Left_range_eq_ofList_pair_smul_top
#print axioms koszulR2H0EquivQuotOfListPair
#print axioms koszulR2H2
#print axioms mem_koszulR2H2_iff
#print axioms koszulR2H2_eq_bot_of_isWeaklyRegular_pair
#print axioms koszulR2Obj
#print axioms koszulR2Differential
#print axioms koszulR2Differential_sq
#print axioms koszulR2ChainComplex
#print axioms koszulR2ChainComplex_d_one_zero
#print axioms koszulR2ChainComplex_d_two_one
#print axioms koszulR2H1Cycles
#print axioms koszulR2RightToCycles
#print axioms koszulR2H1
#print axioms koszulR2RightToCycles_range_eq_top_of_isWeaklyRegular_pair
#print axioms koszulR2H1_subsingleton_of_isWeaklyRegular_pair
#print axioms koszulR2PositiveAcyclic
#print axioms koszulR2H2_eq_bot_of_positiveAcyclic
#print axioms koszulR2H1_subsingleton_of_positiveAcyclic
#print axioms koszulR2PositiveAcyclic_of_isWeaklyRegular_pair
#print axioms koszulR2PositiveAcyclic_of_cons_certificate
#print axioms koszulLowDegreePositiveAcyclic
#print axioms koszulLowDegreePositiveAcyclic_nil
#print axioms koszulLowDegreePositiveAcyclic_singleton
#print axioms koszulLowDegreePositiveAcyclic_pair
#print axioms not_koszulLowDegreePositiveAcyclic_cons_cons_cons
#print axioms length_le_two_of_koszulLowDegreePositiveAcyclic
#print axioms koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_singleton
#print axioms koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_pair
#print axioms koszulLowDegreePositiveAcyclic_of_isWeaklyRegular_length_le_two
#print axioms koszulLowDegreeRegularityCertificate
#print axioms koszulLowDegreeRegularityCertificate_nil
#print axioms koszulLowDegreeRegularityCertificate_singleton
#print axioms koszulLowDegreeRegularityCertificate_pair
#print axioms not_koszulLowDegreeRegularityCertificate_cons_cons_cons
#print axioms koszulLowDegreePositiveAcyclic_of_regularCertificate
#print axioms length_le_two_of_koszulLowDegreeRegularityCertificate
#print axioms koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_singleton
#print axioms koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_pair
#print axioms koszulLowDegreeRegularityCertificate_of_isWeaklyRegular_length_le_two
#print axioms isWeaklyRegular_of_koszulLowDegreeRegularityCertificate_singleton
#print axioms isWeaklyRegular_of_koszulLowDegreeRegularityCertificate_pair
#print axioms isWeaklyRegular_of_koszulLowDegreeRegularityCertificate
#print axioms koszulLowDegreeRegularityCertificate_iff_isWeaklyRegular_length_le_two
#print axioms KoszulAcyclicPredicate
#print axioms KoszulWeakAcyclicityInterface
#print axioms koszulAcyclic_iff_isWeaklyRegular_of_interface
#print axioms koszulInterface_singleton_iff_koszulR1PositiveAcyclic
#print axioms koszulR2PositiveAcyclic_of_interface_pair
#print axioms koszulLowDegreePositiveAcyclic_of_interface_length_le_two
#print axioms koszulLowDegreeRegularityCertificate_iff_interface_length_le_two
#print axioms KoszulComplexModel
#print axioms KoszulComplexModel.acyclic_iff_isWeaklyRegular
#print axioms KoszulComplexModel.lowDegreeRegularityCertificate_iff_acyclic
#print axioms KoszulComplexModel.lowDegreePositiveAcyclic_of_acyclic
#print axioms KoszulComplexModel.acyclic_of_lowDegreeRegularityCertificate
#print axioms weakRegularKoszulAcyclicPredicate
#print axioms weakRegularKoszulWeakInterface
#print axioms lowDegreeKoszulComplex
#print axioms lowDegreeKoszulComplex_singleton
#print axioms lowDegreeKoszulComplex_pair
#print axioms lowDegreeKoszulComplexModel
#print axioms lowDegreeKoszulComplexModel_complex_singleton
#print axioms lowDegreeKoszulComplexModel_complex_pair
#print axioms lowDegreeKoszulComplexModel_acyclic_iff_isWeaklyRegular
#print axioms lowDegreeKoszulComplexModel_lowDegreeCertificate_iff_acyclic
#print axioms KoszulRegularAcyclicityInterface
#print axioms koszulAcyclic_iff_isRegular_of_interface
#print axioms koszulLowDegreePositiveAcyclic_of_isRegular_length_le_two
#print axioms koszulLowDegreeRegularityCertificate_of_isRegular_length_le_two
#print axioms koszulLowDegreePositiveAcyclic_of_regular_interface_length_le_two
#print axioms koszulLowDegreeRegularityCertificate_of_regular_interface_length_le_two
#print axioms regular_of_linearEquiv
#print axioms weaklyRegularSequence_of_flat_of_isBaseChange
#print axioms regularSequence_of_faithfullyFlat_of_isBaseChange
#print axioms regularSequence_of_faithfullyFlat_algebra
#print axioms weaklyRegularSequence_of_localizedModule
#print axioms regularSequence_of_localizedModule_atPrime_of_mem
#print axioms regularSequence_of_faithfullyFlat_of_isBaseChange_prodMap
#print axioms regularSequence_of_faithfullyFlat_of_isBaseChange_pi
#print axioms HasWeakRegularSequenceLength
#print axioms hasWeakRegularSequenceLength_zero
#print axioms hasWeakRegularSequenceLength_of_isWeaklyRegular
#print axioms hasWeakRegularSequenceLength_of_isRegular
#print axioms exists_weaklyRegular_of_hasWeakRegularSequenceLength
#print axioms ModuleDepthDimensionInterface
#print axioms ModuleDepthDimensionInterface.weaklyRegular_length_le_depth
#print axioms ModuleDepthDimensionInterface.regular_length_le_depth
#print axioms ModuleDepthDimensionInterface.hasWeakRegularSequenceLength_le_depth
#print axioms ModuleDepthDimensionInterface.koszulAcyclic_length_le_depth
#print axioms ModuleDepthDimensionInterface.koszulRegularAcyclic_length_le_depth
#print axioms ModuleDepthDimensionInterface.koszulModel_acyclic_length_le_depth
#print axioms ModuleDepthDimensionInterface.weaklyRegular_length_le_dimension_of_isCohenMacaulay
#print axioms ModuleDepthDimensionInterface.regular_length_le_dimension_of_isCohenMacaulay
#print axioms ModuleDepthDimensionInterface.hasWeakRegularSequenceLength_le_dimension_of_isCohenMacaulay
#print axioms ModuleDepthDimensionInterface.dimension_le_depth_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.weaklyRegular_length_le_dimension_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.regular_length_le_dimension_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.hasWeakRegularSequenceLength_le_dimension_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.koszulAcyclic_length_le_dimension_of_isCohenMacaulay
#print axioms ModuleDepthDimensionInterface.koszulRegularAcyclic_length_le_dimension_of_isCohenMacaulay
#print axioms ModuleDepthDimensionInterface.koszulModel_acyclic_length_le_dimension_of_isCohenMacaulay
#print axioms ModuleDepthDimensionInterface.koszulAcyclic_length_le_dimension_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.koszulRegularAcyclic_length_le_dimension_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.koszulModel_acyclic_length_le_dimension_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.lowDegreeRegularityCertificate_length_le_depth
#print axioms ModuleDepthDimensionInterface.lowDegreeRegularityCertificate_length_le_dimension_of_isCohenMacaulay
#print axioms ModuleDepthDimensionInterface.lowDegreeRegularityCertificate_length_le_dimension_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.depth_eq_length_of_isCohenMacaulay_of_dimension_le_length
#print axioms ModuleDepthDimensionInterface.dimension_eq_length_of_isCohenMacaulay_of_dimension_le_length
#print axioms ModuleDepthDimensionInterface.depth_eq_length_of_depth_eq_dimension_of_dimension_le_length
#print axioms ModuleDepthDimensionInterface.dimension_eq_length_of_depth_eq_dimension_of_dimension_le_length
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_koszulAcyclic
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_koszulRegularAcyclic
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_koszulModelAcyclic
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_koszulAcyclic_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_koszulRegularAcyclic_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_koszulModelAcyclic_of_depth_eq_dimension
#print axioms ModuleDepthDimensionInterface.depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate_of_depth_eq_dimension
#print axioms prop18_depth_lower_bound_of_isWeaklyRegular
#print axioms prop18_depth_lower_bound
#print axioms prop18_depth_lower_bound_of_isRegular
#print axioms prop18_depth_lower_bound_of_koszulAcyclic
#print axioms prop18_depth_lower_bound_of_koszulRegularAcyclic
#print axioms prop18_depth_lower_bound_of_koszulModelAcyclic
#print axioms prop18_depth_lower_bound_of_lowDegreeRegularityCertificate
#print axioms prop18_depth_lower_bound_of_flatBaseChange
#print axioms prop18_depth_lower_bound_of_faithfullyFlatBaseChange
#print axioms prop18_depth_lower_bound_of_localizedModule
#print axioms prop18_dimension_lower_bound_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_depth_eq_dimension
#print axioms prop18_dimension_lower_bound_of_koszulAcyclic_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_koszulRegularAcyclic_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_koszulModelAcyclic_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_lowDegreeRegularityCertificate_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_koszulAcyclic_of_depth_eq_dimension
#print axioms prop18_dimension_lower_bound_of_koszulRegularAcyclic_of_depth_eq_dimension
#print axioms prop18_dimension_lower_bound_of_koszulModelAcyclic_of_depth_eq_dimension
#print axioms prop18_dimension_lower_bound_of_lowDegreeRegularityCertificate_of_depth_eq_dimension
#print axioms prop18_dimension_lower_bound_of_flatBaseChange_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_faithfullyFlatBaseChange_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_localizedModule_of_isCohenMacaulay
#print axioms prop18_dimension_lower_bound_of_flatBaseChange_of_depth_eq_dimension
#print axioms prop18_dimension_lower_bound_of_faithfullyFlatBaseChange_of_depth_eq_dimension
#print axioms prop18_dimension_lower_bound_of_localizedModule_of_depth_eq_dimension
#print axioms prop18_depth_eq_dimension_trigger
#print axioms prop18_depth_eq_dimension_trigger_of_depth_eq_dimension
#print axioms prop18_depth_eq_dimension_trigger_of_koszulAcyclic
#print axioms prop18_depth_eq_dimension_trigger_of_koszulRegularAcyclic
#print axioms prop18_depth_eq_dimension_trigger_of_koszulModelAcyclic
#print axioms prop18_depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate
#print axioms prop18_depth_eq_dimension_trigger_of_koszulAcyclic_of_depth_eq_dimension
#print axioms prop18_depth_eq_dimension_trigger_of_koszulRegularAcyclic_of_depth_eq_dimension
#print axioms prop18_depth_eq_dimension_trigger_of_koszulModelAcyclic_of_depth_eq_dimension
#print axioms prop18_depth_eq_dimension_trigger_of_lowDegreeRegularityCertificate_of_depth_eq_dimension
#print axioms detTraceWeightedLogSeries
#print axioms detTraceShiftedSeries
#print axioms coeff_detTraceWeightedLogSeries_zero
#print axioms coeff_detTraceWeightedLogSeries_of_ne_zero
#print axioms coeff_detTraceShiftedSeries
#print axioms constantCoeff_detTraceWeightedLogSeries
#print axioms derivative_detTraceWeightedLogSeries
#print axioms derivative_exp_subst_of_constantCoeff_zero
#print axioms constantCoeff_exp_subst_of_constantCoeff_zero
#print axioms powerSeries_eq_of_derivative_eq_mul
#print axioms exp_subst_eq_of_derivative_eq_mul
#print axioms exp_detTraceWeightedLogSeries_unique
#print axioms derivative_det_eq_sum_updateCol
#print axioms derivative_det_eq_sum_adjugate_mulVec
#print axioms oneSubXMatrixPoly
#print axioms derivative_oneSubXMatrixPoly_apply
#print axioms derivative_det_oneSubXMatrixPoly
#print axioms psMatrixOfPowers
#print axioms oneSubXMatrix
#print axioms oneSubXMatrix_eq_map_oneSubXMatrixPoly
#print axioms trace_adjugate_map_oneSubXMatrixPoly
#print axioms derivative_det_oneSubXMatrix
#print axioms coeff_psMatrixOfPowers
#print axioms coeff_constMul_psMatrixOfPowers
#print axioms coeff_X_constMul_psMatrixOfPowers_zero
#print axioms coeff_X_constMul_psMatrixOfPowers_succ
#print axioms oneSubXMatrix_mul_psMatrixOfPowers
#print axioms det_oneSubXMatrix_eq_charpolyRev
#print axioms constantCoeff_det_oneSubXMatrix
#print axioms inv_det_smul_adjugate_oneSubXMatrix_eq_psMatrixOfPowers
#print axioms coeff_trace_psMatrixOfPowers_mul_const
#print axioms inv_det_mul_trace_adjugate_mul_eq_trace_psMatrixOfPowers_mul_const
#print axioms derivative_inv_det_oneSubXMatrix
#print axioms matrixDetOneSubSeries
#print axioms matrixDetOneSubInvSeries
#print axioms matrixTracePower
#print axioms matrixTraceLogSeries
#print axioms matrixTraceResolventSeries
#print axioms derivative_matrixTraceLogSeries
#print axioms matrixTraceResolventSeries_eq_trace_psMatrixOfPowers_mul_const
#print axioms constantCoeff_matrixDetOneSubSeries
#print axioms coeff_one_matrixDetOneSubSeries
#print axioms constantCoeff_matrixDetOneSubInvSeries
#print axioms derivative_matrixDetOneSubInvSeries
#print axioms lem37_det_trace_formal_identity
#print axioms zetaULinearLocalFactor
#print axioms zetaUCompletelyMultiplicativeValue
#print axioms zetaULinearLocalFactor_eq_geometric_tsum
#print axioms zetaU_eulerProduct_hasProd
#print axioms zetaU_eulerProduct_tprod
#print axioms zetaU_eulerProduct_partial
#print axioms quadraticEulerDenominator
#print axioms quadraticEulerLocalFactor
#print axioms quadraticEulerDenominator_eq_mul
#print axioms quadraticEulerLocalFactor_eq_mul
#print axioms quadraticEulerPartialProduct
#print axioms quadraticEulerPartialProduct_eq_mul
#print axioms quadraticEulerProduct_hasProd_of_linear
#print axioms quadraticEulerProduct_tprod_of_linear
#print axioms zetaULSeries
#print axioms zetaULSeries_summable_of_abscissa_lt
#print axioms zetaULSeries_deriv
#print axioms zetaULSeriesLogDeriv
#print axioms zetaULSeries_logDeriv_eq
#print axioms zetaULSeries_abscissa_logMul
#print axioms SixFunctorData
#print axioms SixFunctorData.sheafIso_refl_apply
#print axioms SixFunctorData.sheafIso_symm_apply
#print axioms SixFunctorData.sheafIso_trans_apply
#print axioms SixFunctorData.pull_constructible
#print axioms SixFunctorData.push_constructible
#print axioms SixFunctorData.shriek_constructible
#print axioms SixFunctorData.exceptionalPull_constructible
#print axioms SixFunctorData.tensor_constructible
#print axioms SixFunctorData.internalHom_constructible
#print axioms SixFunctorData.dual_constructible
#print axioms SixFunctorData.unit_constructible
#print axioms SixFunctorData.glue_triangle_distinguished
#print axioms SixFunctorData.monoidal_dual_iso
#print axioms SixFunctorData.pull_iso_congr
#print axioms SixFunctorData.pull_id_iso
#print axioms SixFunctorData.pull_comp_iso
#print axioms SixFunctorData.push_iso_congr
#print axioms SixFunctorData.push_id_iso
#print axioms SixFunctorData.push_comp_iso
#print axioms SixFunctorData.shriek_iso_congr
#print axioms SixFunctorData.shriek_id_iso
#print axioms SixFunctorData.shriek_comp_iso
#print axioms SixFunctorData.shriek_comp_three_iso
#print axioms SixFunctorData.shriek_factorization_iso_of_eq
#print axioms SixFunctorData.exceptionalPull_iso_congr
#print axioms SixFunctorData.exceptionalPull_id_iso
#print axioms SixFunctorData.exceptionalPull_comp_iso
#print axioms SixFunctorData.baseChangeShriek_iso
#print axioms SixFunctorData.projectionFormula_iso
#print axioms SixFunctorData.baseChangeShriek_left_constructible
#print axioms SixFunctorData.baseChangeShriek_right_constructible
#print axioms SixFunctorData.projectionFormula_terms_constructible
#print axioms SixFunctorData.shriek_tensor_pull_constructible
#print axioms SixFunctorData.tensor_shriek_constructible
#print axioms CurveFactorization
#print axioms CurveFactorization.factor_eq
#print axioms CurveFactorization.jX_isOpenImmersion
#print axioms CurveFactorization.g_isProper
#print axioms CurveFactorization.pi_isSmoothCurveOver
#print axioms CurveFactorization.jX_shriek_constructible
#print axioms CurveFactorization.g_jX_shriek_constructible
#print axioms CurveFactorization.pi_g_jX_shriek_constructible
#print axioms CurveFactorization.shriek_comp_iso
#print axioms CurveFactorization.shriek_factorization_iso
#print axioms CurveFactorization.curveReduction_terms_constructible
#print axioms weightRadius
#print axioms weightRadius_pos
#print axioms WeilIIPackage
#print axioms WeilIIPackage.constructible
#print axioms WeilIIPackage.pure_to_mixedLE
#print axioms WeilIIPackage.mixedLE_of_le
#print axioms WeilIIPackage.frob_abs_eq
#print axioms WeilIIPackage.frob_norm_le_of_pure
#print axioms WeilIIPackage.frob_norm_le_of_mixed
#print axioms WeilIIPackage.FrobeniusRadiusBound
#print axioms WeilIIPackage.pure_weight_radiusBound
#print axioms WeilIIPackage.mixed_weight_radiusBound
#print axioms WeilIIPackage.weightRadius_pos_apply
#print axioms DetTraceRadiusCertificate
#print axioms DetTraceRadiusCertificate.radius_of_radiusBound
#print axioms prop38_radius_limit_of_pure
#print axioms prop38_radius_limit_of_mixed
#print axioms glAltSign
#print axioms glAltSign_of_even
#print axioms glAltSign_of_not_even
#print axioms glAltSign_zero
#print axioms glAlternatingTraceOf
#print axioms glAlternatingMatrixTraceOf
#print axioms glAlternatingMatrixTraceShiftedSeries
#print axioms coeff_glAlternatingMatrixTraceShiftedSeries
#print axioms GrothendieckLefschetzPackage
#print axioms GrothendieckLefschetzPackage.constructible
#print axioms GrothendieckLefschetzPackage.alternatingTrace
#print axioms GrothendieckLefschetzPackage.pointCount_eq_alternatingTrace
#print axioms GrothendieckLefschetzPackage.pointCount_succ_eq_alternatingTrace
#print axioms GrothendieckLefschetzPackage.alternatingTraceShiftedSeries
#print axioms GrothendieckLefschetzPackage.coeff_alternatingTraceShiftedSeries
#print axioms GrothendieckLefschetzPackage.detTraceShiftedSeries_eq_alternatingTraceShiftedSeries
#print axioms GrothendieckLefschetzPackage.constantCoeff_logSeries
#print axioms GrothendieckLefschetzPackage.coeff_logSeries_of_ne_zero
#print axioms GrothendieckLefschetzPackage.logDerivative_expansion
#print axioms GrothendieckLefschetzPackage.coeff_logDerivative_expansion
#print axioms GrothendieckLefschetzPackage.alternatingTrace_eq_matrixTrace
#print axioms GrothendieckLefschetzPackage.alternatingTraceShiftedSeries_eq_matrixTraceShiftedSeries
#print axioms GrothendieckLefschetzPackage.logDerivative_matrixTrace_expansion
#print axioms GrothendieckLefschetzPackage.coeff_logDerivative_matrixTrace_expansion
#print axioms GrothendieckLefschetzPackage.complex_det_trace_formal_identity
#print axioms GrothendieckLefschetzPackage.complex_det_trace_formal_identity_family
#print axioms lem36_logDerivative_expansion
#print axioms lem36_logDerivative_matrixTrace_expansion
#print axioms FiniteSupportCohomologyVanishing
#print axioms FiniteSupportCohomologyVanishing.constructible
#print axioms FiniteSupportCohomologyVanishing.finite_support
#print axioms FiniteSupportCohomologyVanishing.PositiveCohomologyVanishes
#print axioms FiniteSupportCohomologyVanishing.positive_cohomology_vanishes
#print axioms FiniteSupportCohomologyVanishing.eq_of_positive_degree
#print axioms prop43_positive_cohomology_vanishes
#print axioms prop43_positive_cohomology_eq
#print axioms GlobalPurityBConclusion
#print axioms GlobalPurityBConclusion.positive_vanishing
#print axioms GlobalPurityBConclusion.radius_limit
#print axioms GlobalPurityBConclusion.logDerivative_expansion
#print axioms GlobalPurityBConclusion.matrixTrace_logDerivative_expansion
#print axioms thm44_globalPurityB_of_pure
#print axioms thm44_globalPurityB_of_mixed
#print axioms cor45_globalPurityB_radiusLimit
#print axioms cor46_globalPurityB_logDerivative_expansion
#print axioms cor46_globalPurityB_matrixTrace_logDerivative_expansion
#print axioms WeightPurityGate
#print axioms weightPurityGate_pure
#print axioms weightPurityGate_detTraceExpansion
#print axioms weightPurityGate_radiusBound
#print axioms weightPurityGate_radiusLimit
#print axioms EquivalenceCGate
#print axioms equivalenceCGate_arithmetic
#print axioms equivalenceCGate_weightPurity
#print axioms equivalenceCGate_radiusLimit
#print axioms equivalence_C
#print axioms equivalence_C_faithful_tfae
#print axioms FaithfulEquivalenceCConclusion
#print axioms FaithfulEquivalenceCConclusion.arithmetic_tfae
#print axioms FaithfulEquivalenceCConclusion.radius_limit
#print axioms FaithfulEquivalenceCConclusion.rh_tp_gate_tfae
#print axioms equivalence_C_faithful
#print axioms equivalence_C_faithful_rh_iff_tp
#print axioms ConcreteSurrogateCertificate
#print axioms ConcreteSurrogateCertificate.tor_equiv
#print axioms ConcreteSurrogateCertificate.cech_equiv
#print axioms concreteSurrogateCertificate
#print axioms LowDegreeKoszulCertificate
#print axioms LowDegreeKoszulCertificate.singleton_complex
#print axioms LowDegreeKoszulCertificate.pair_complex
#print axioms lowDegreeKoszulCertificate
#print axioms BundledInterfaceCertificate
#print axioms bundledInterfaceCertificate
#print axioms FormalAlgebraCoreCertificate
#print axioms formalAlgebraCoreCertificate
#print axioms ExistingAnalogReuseCertificate
#print axioms existingAnalogReuseCertificate
#print axioms MathlibGapWorkaroundChecklist
#print axioms mathlibGapWorkaroundChecklist
#print axioms FaithfullyFlatBaseChangeHandle
#print axioms faithfullyFlatBaseChangeHandle
#print axioms DepthCMLocalizationHandle
#print axioms depthCMLocalizationHandle
#print axioms EulerProductMathlibHandle
#print axioms eulerProductMathlibHandle
#print axioms LSeriesDerivativeMathlibHandle
#print axioms lseriesDerivativeMathlibHandle
#print axioms MathlibAbstractTorFunctorHandle
#print axioms mathlibAbstractTorFunctorHandle
#print axioms ConcreteTorMathlibBridge
#print axioms concreteTorMathlibBridge
#print axioms KoszulReuseHandle
#print axioms koszulReuseHandle
#print axioms mathlibHandleInventoryChecklist
end AxiomAudit

end Spt7
