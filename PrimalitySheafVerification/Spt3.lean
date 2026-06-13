/-
================================================================================
  Spt3Unified.lean — INTEGRATED, sorry-free, axiom-free formalization of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification" (spt3).

  This single file merges the three verified fragments
      Spt3.lean  +  Spt3Sheaf.lean  +  Spt3Cert.lean
  and adds the full additional-checklist formalization (Categories A-F).
  Every result is kernel-checked; the AxiomAudit sections confirm dependence
  only on [propext, Classical.choice, Quot.sound] (never sorryAx).
================================================================================
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-
================================================================================
  Spt3.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification".

  Every theorem is machine-checked by the Lean 4 kernel against Mathlib, with NO
  `sorry` and NO new global `axiom`.  The `AxiomAudit` section runs `#print axioms`
  on each result: they depend only on `[propext, Classical.choice, Quot.sound]`
  (never `sorryAx`); the conditional results (§G) carry their assumptions as
  EXPLICIT HYPOTHESES, visible in the signature.

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    §2.2/3.3/3.5, Lem 5, Prop(2171)  kernel = (M)∩(N) = (lcm)
                                      ↦ kernel_mem_iff_lcm, kernel_ideal_inter PROVED
    §3.4(3) Zero-Class rule (CORRECTED) T∈(M)∩(N) ⇔ lcm∣T ⇔ vp≥max
                                      ↦ zeroClass_mem_iff_lcm, lcm_dvd_iff_max  PROVED
    §3.4/3.5, Prop 7  thickness (CORRECTED)  gcd→min, lcm→max
                                      ↦ factorization_gcd_apply / lcm_apply     PROVED
    Lem 6/12, Cor(2721)  Tor₁(ℤ/M,ℤ/pᵏ) ≅ ℤ/gcd, order = gcd
                                      ↦ card_ker_mulLeft, commonResidueFiber_card,
                                        obstructionFree_iff_card/coprime         PROVED
    Thm 4.1, Lem 6/12 (§4.4) Tor as a GROUP iso  ker(×M on ℤ/N) ≅ ℤ/gcd
                                      ↦ ker_mulLeft_addEquiv,
                                        ker_trivial_of_coprime          PROVED (group level)
    Lem A/10/11, Thm 14, Rem 19  CRT split, primewise, |Tor| = ∏ qᵃ
                                      ↦ crt_iso, gcd_eq_prod_primeFactors        PROVED
    Lem A/10 (§4.4)  n-fold CRT  ℤ/N ≅ Π_{q∣N} ℤ/q^{v_q(N)}
                                      ↦ crt_pi_iso  (= ZMod.equivPi)            PROVED
    §3.4(7), Cor(2777), Lem 15/16  IC = ∑ min·log q, |Tor| = exp(IC), mono, add
                                      ↦ IC, card_Tor_eq_exp_IC, IC_mono,
                                        IC_coprime_add                           PROVED
    Prop 17 (§4.6)  affine bit-cost bound  Cost ≤ C₁·IC/log2 + C₂
                                      ↦ log2_mul_sum_min_le_IC, sum_min_le_IC_div_log2,
                                        cost_affine_bound                        PROVED
    Prop 8/Cor 9  stability under CRT refinement
                                      ↦ thickness_stable_coprime                PROVED
    Thm 20, Cor(D(∆))  derived equalizer = cotangent test (CONDITIONAL)
                                      ↦ derived_equalizer_tfae                  PROVED (cond.)
    Cor 2777 (group form)  |ker| = exp(IC) via the §I group iso
                                      ↦ card_ker_eq_exp_IC                       PROVED
    Thm 1/18  X prime ⇔ ∃ global section
                                      ↦ overlap_glue_iff_lcm (gluing core only)  PARTIAL
                                        certification_iff_of_complete  CONDITIONAL (skeleton)

  ⚠ CORRECTIONS found while formalizing:
    • §3.4(3) "Zero-Class Decision Rule" states T ∈ (M)∩(pᵏ) ⇔ gcd(M,pᵏ)∣T ⇔
      vp(T) ≥ min{vp M, k}.  This is FALSE: (M)∩(pᵏ) = (lcm), so the correct rule
      is `lcm∣T ⇔ vp(T) ≥ max{vp M, k}`.  The `gcd`/`min` belongs to the common
      residue fiber `ℤ/gcd` (and Tor₁), NOT to the intersection.  We prove the
      corrected rule (`zeroClass_mem_iff_lcm`, `lcm_dvd_iff_max`) and the gcd/min
      facts separately so the distinction is explicit.
    • The "localized thickness `((M)∩(pᵏ))_(p) = p^{min}`" (eq. (4), §3.5, Prop 7)
      is the same conflation: the intersection localises to `p^{max}`; `min` is
      the gcd/Tor thickness.

  HONEST SCOPE of Theorem 18 (X prime ⇔ ∃ global section):  this is the
  framework's SOUNDNESS + COMPLETENESS claim.  Its `(⇐)` direction asserts that
  the four layers (incl. the EC/AKS regularity layer) exclude every composite —
  a deep claim that is NOT an elementary arithmetic fact and that would be
  CIRCULAR to assume as a hypothesis.  So we do NOT certify "prime ⇔ certificate".
  We formalize only the gluing MECHANISM the proof uses (overlap equalizer = lcm,
  CRT), which is genuine.  Likewise the p-adic log bridge and the EC/étale/motivic
  detectors are omitted (Mathlib lacks the infrastructure).
================================================================================
-/

open scoped BigOperators

namespace Spt3

/-! ## §A — Equalizer kernel = ideal intersection = lcm (Lem 5, §3.3/3.5). -/

/-- `ker(ℤ → ℤ/M × ℤ/N) = (M)∩(N) = (lcm)` (membership form). -/
theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a :=
  lcm_dvd_iff.symm

/-- Ideal form. -/
theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-! ## §B — Zero-Class rule (CORRECTED) and thickness (Prop 7, §3.4/3.5).

The paper's §3.4(3) attaches `gcd`/`min` to the intersection; the truth is
`lcm`/`max`.  Both are proved here so the distinction is explicit. -/

/-- **Zero-Class rule, CORRECTED.** `T ∈ (M)∩(N) ↔ lcm M N ∣ T` (not `gcd ∣ T`). -/
theorem zeroClass_mem_iff_lcm (M N T : ℤ) :
    (T ∈ Ideal.span {M} ⊓ Ideal.span {N}) ↔ lcm M N ∣ T := by
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- `v_p(gcd M N) = min(v_p M, v_p N)` — the common-residue-fiber / Tor thickness. -/
theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

/-- `v_p(lcm M N) = max(v_p M, v_p N)` — the *intersection* thickness (CORRECTED). -/
theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

/-- The valuation form of the corrected Zero-Class rule:
    `lcm M N ∣ T ↔ ∀ p, max(v_p M, v_p N) ≤ v_p T`. -/
theorem lcm_dvd_iff_max {M N T : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hT : T ≠ 0) :
    Nat.lcm M N ∣ T ↔ ∀ p, max (M.factorization p) (N.factorization p) ≤ T.factorization p := by
  rw [← Nat.factorization_le_iff_dvd (Nat.lcm_ne_zero hM hN) hT]
  constructor
  · intro h p; have := h p; rwa [Nat.factorization_lcm hM hN, Finsupp.sup_apply] at this
  · intro h p; rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]; exact h p

/-- The gcd/min fact, kept separate: `gcd M N ∣ T ↔ ∀ p, min(v_p M, v_p N) ≤ v_p T`. -/
theorem gcd_dvd_iff_min {M N T : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hT : T ≠ 0) :
    Nat.gcd M N ∣ T ↔ ∀ p, min (M.factorization p) (N.factorization p) ≤ T.factorization p := by
  rw [← Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hM) hT]
  constructor
  · intro h p; have := h p; rwa [Nat.factorization_gcd hM hN, Finsupp.inf_apply] at this
  · intro h p; rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]; exact h p

/-! ## §C — Derived/Tor readout (Lem 6/12, Cor 2721): Tor₁ ≅ ℤ/gcd. -/

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

/-- **Lemma 6/12.** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = |ker(×M on ℤ/N)| = gcd(N, M)`. -/
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

/-- Order of the common residue fiber `ℤ/gcd`. -/
theorem commonResidueFiber_card {g : ℕ} [NeZero g] : Fintype.card (ZMod g) = g := ZMod.card g

/-- **Cor 2721.** Obstruction-free ⟺ Tor vanishes (fiber is a point). -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N := Iff.rfl

/-! ## §D — CRT / primewise decomposition (Lem A/10/11, Thm 14). -/

/-- **Lemma A / 10 (CRT split).** `ℤ/(ab) ≅ ℤ/a × ℤ/b` for coprime `a, b`. -/
noncomputable def crt_iso {a b : ℕ} (h : Nat.Coprime a b) :
    ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder h

/-- **Theorem 14.** Primewise factorisation of the obstruction `gcd(M, N)`. -/
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

/-! ## §E — Indicator complexity (§3.4(7), Cor 2777, Lem 15/16). -/

/-- **Definition (IC).** `IC(M;N) = ∑_{q∣N} min(v_q M, v_q N)·log q`. -/
noncomputable def IC (M N : ℕ) : ℝ :=
  ∑ q ∈ N.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q

/-- **Cor 2777.** `|Tor₁| = gcd(M,N) = exp(IC(M;N))`. -/
theorem card_Tor_eq_exp_IC {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    (Nat.gcd M N : ℝ) = Real.exp (IC M N) := by
  rw [IC, Real.exp_sum, gcd_eq_prod_primeFactors hM hN, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
  rw [Nat.cast_pow, ← Nat.cast_min, ← Real.log_pow, Real.exp_log (by positivity)]

/-- **Lemma 15 (monotonicity).** If `N' ∣ N` then `IC(M;N') ≤ IC(M;N)`. -/
theorem IC_mono {M N' N : ℕ} (hN : N ≠ 0) (hdvd : N' ∣ N) : IC M N' ≤ IC M N := by
  have hN' : N' ≠ 0 := fun h => hN (by simpa [h] using hdvd)
  have hle : N'.factorization ≤ N.factorization := (Nat.factorization_le_iff_dvd hN' hN).mpr hdvd
  calc IC M N'
      ≤ ∑ q ∈ N'.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        apply mul_le_mul_of_nonneg_right _ hlog
        exact min_le_min le_rfl (by exact_mod_cast hle q)
    _ ≤ IC M N := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hdvd hN)
        intro q hq _
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        exact mul_nonneg (by positivity) hlog

/-- **Lemma 16 (additivity on coprime factors).** -/
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

/-! ## §F — Stability under CRT refinement (Prop 8, Cor 9). -/

/-- The per-prime obstruction exponent is invariant under enlarging `N` by a
    factor coprime to `q`. -/
theorem thickness_stable_coprime {M N c : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hc : c ≠ 0)
    {q : ℕ} (hq : ¬ q ∣ c) :
    (Nat.gcd M (N * c)).factorization q = (Nat.gcd M N).factorization q := by
  rw [factorization_gcd_apply hM (Nat.mul_ne_zero hN hc),
      factorization_gcd_apply hM hN, Nat.factorization_mul hN hc]
  have hcq : c.factorization q = 0 :=
    (Nat.factorization_eq_zero_iff c q).mpr (Or.inr (Or.inl hq))
  simp [Finsupp.add_apply, hcq]

/-! ## §G — Conditional derived equalizer = cotangent test (Theorem 20).

The bridge `H¹(L_{X_p}) = 0 ↔ smooth` (two-term model, Mathlib lacks the cotangent
complex) and `smooth ↔ gcd = 1` (good-prime gate) are taken as EXPLICIT
hypotheses; the elementary `gcd = 1 ↔ Tor = 0` is unconditional.  `#print axioms`
shows no `sorryAx` and no new global axiom. -/

/-- **Theorem 20 (conditional).** On overlaps above `p`, the derived equalizer
(`gcd = 1`), smoothness, and the cotangent test (`der = 0`) are equivalent. -/
theorem derived_equalizer_tfae (smooth : Prop) (der M pk : ℕ)
    (Hder : der = 0 ↔ smooth)
    (Hgate : smooth ↔ Nat.gcd M pk = 1) :
    [Nat.gcd M pk = 1, smooth, der = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate.symm
  tfae_have 2 ↔ 3 := Hder.symm
  tfae_finish

/-! ## §H — Global certification (Theorem 1/18): the gluing mechanism only.

We do NOT certify "X prime ⇔ ∃ global section" (the framework's soundness +
completeness claim, which rests on the non-elementary EC/AKS layer).  We formalize
the equalizer gluing it uses: two local witnesses `a, b` agree on a modular/p-adic
overlap iff their difference lies in `(M)∩(N) = (lcm)`. -/

/-- Overlap gluing condition: local witnesses `a, b` are compatible on the
    `(M, N)` overlap iff `lcm M N ∣ (a - b)`. -/
theorem overlap_glue_iff_lcm (M N a b : ℤ) :
    (M ∣ (a - b) ∧ N ∣ (a - b)) ↔ lcm M N ∣ (a - b) :=
  lcm_dvd_iff.symm

/-! ## §I — Tor as a GROUP isomorphism (Thm 4.1 / Lem 6,12, §4.4 "Complete Proofs").

The core file proves only the *cardinality* `|ker(×M on ℤ/N)| = gcd(N,M)`
(`card_ker_mulLeft`).  §4.4 of the paper is titled "Complete Proofs" and proves a
genuine group isomorphism, so for literal fidelity we upgrade the equicardinality
to an honest additive group isomorphism `ker(×M on ℤ/N) ≃+ ℤ/gcd(N,M)`.

Argument: the kernel is an additive subgroup of the cyclic group `ℤ/N`, hence
cyclic (`AddSubgroup.isAddCyclic`); `ℤ/gcd` is cyclic (`ZMod.instIsAddCyclic`); two
finite cyclic groups of equal order are isomorphic (`addEquivOfAddCyclicCardEq`),
and the orders agree by `card_ker_mulLeft`. -/

/-- **Theorem 4.1 / Lemma 6,12 (GROUP isomorphism).** The derived obstruction is
not merely equinumerous with `ℤ/gcd` — there is a genuine additive group
isomorphism `ker(×M on ℤ/N) ≃+ ℤ/gcd(N,M)`. -/
noncomputable def ker_mulLeft_addEquiv (N : ℕ) [NeZero N] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod (Nat.gcd N M) := by
  haveI : NeZero (Nat.gcd N M) := ⟨Nat.gcd_ne_zero_left (NeZero.ne N)⟩
  apply addEquivOfAddCyclicCardEq
  rw [card_ker_mulLeft, Nat.card_eq_fintype_card, ZMod.card]

/-- **Cor (obstruction-free, GROUP form).** No obstruction (`gcd N M = 1`) iff the
derived group `ker(×M on ℤ/N)` is trivial, i.e. isomorphic to `0 = ℤ/1`. -/
noncomputable def ker_trivial_of_coprime (N : ℕ) [NeZero N] (M : ℕ)
    (h : Nat.gcd N M = 1) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod 1 := by
  have e := ker_mulLeft_addEquiv N M
  rwa [h] at e

/-! ## §J — n-fold CRT decomposition of `ℤ/N` (Lemma A / 10). -/

/-- **Lemma A / 10 (n-fold CRT).** The full primewise decomposition
`ℤ/N ≃+* Π_{q ∣ N} ℤ/q^{v_q(N)}` — the ring-level statement behind the binary
`crt_iso`, supplied by Mathlib's `ZMod.equivPi`.  Combined with §I this realises
the paper's `Tor₁(ℤ/M, ℤ/N) ≅ ⊕_{q∣N} ℤ/q^{min}` at the group level. -/
noncomputable def crt_pi_iso {N : ℕ} (hN : N ≠ 0) :
    ZMod N ≃+* Π (q : N.primeFactors), ZMod (q ^ (N.factorization q)) :=
  ZMod.equivPi N hN

/-! ## §K — Affine bit-cost bound in IC (Proposition 17, §4.6). -/

/-- For a prime `q`, `log 2 ≤ log q`, so the unweighted thickness count is
dominated termwise by `IC`: `(log 2)·∑_{q∣N} min{v_q M, v_q N} ≤ IC(M;N)`. -/
theorem log2_mul_sum_min_le_IC (M N : ℕ) :
    Real.log 2 * (∑ q ∈ N.primeFactors,
        (min (M.factorization q) (N.factorization q) : ℝ)) ≤ IC M N := by
  rw [IC, Finset.mul_sum]
  refine Finset.sum_le_sum (fun q hq => ?_)
  have hqp : Nat.Prime q := (Nat.mem_primeFactors.mp hq).1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
  have hlog : Real.log 2 ≤ Real.log q :=
    (Real.log_le_log_iff (by norm_num) hqpos).mpr (by exact_mod_cast hqp.two_le)
  have hmin : (0 : ℝ) ≤ (min (M.factorization q) (N.factorization q) : ℝ) := by positivity
  rw [mul_comm ((min (M.factorization q) (N.factorization q) : ℝ)) (Real.log q)]
  exact mul_le_mul_of_nonneg_right hlog hmin

/-- Consequently `∑_{q∣N} min{v_q M, v_q N} ≤ IC(M;N) / log 2`. -/
theorem sum_min_le_IC_div_log2 (M N : ℕ) :
    (∑ q ∈ N.primeFactors,
        (min (M.factorization q) (N.factorization q) : ℝ)) ≤ IC M N / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num)), mul_comm]
  exact log2_mul_sum_min_le_IC M N

/-- **Proposition 17 (affine bound in IC).** Any cost that is bounded per-prime by
the local thicknesses (the S1–S3 unit-charge accounting of §4.6) satisfies an
affine bound in `IC/log 2`:  `Cost ≤ C₁·IC(M;N)/log 2 + C₂`.  The constants are
the cost-model parameters; the arithmetic content is `∑ min ≤ IC/log 2`. -/
theorem cost_affine_bound {M N : ℕ} (cost C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁)
    (hcost : cost ≤ C₁ * (∑ q ∈ N.primeFactors,
        (min (M.factorization q) (N.factorization q) : ℝ)) + C₂) :
    cost ≤ C₁ * (IC M N / Real.log 2) + C₂ := by
  have h := mul_le_mul_of_nonneg_left (sum_min_le_IC_div_log2 M N) hC₁
  linarith

/-! ## §L — Worked examples at the GROUP level (Examples 1–3, §4.4.5). -/
section GroupExamples
/-- **Example 1 (§4.4.5).** `M = 24 = 2³·3`, `N = 1440 = 2⁵·3²·5`.
`Tor ≅ ℤ/2³ ⊕ ℤ/3 ≅ ℤ/24` as an additive GROUP (not just `|Tor| = 24`). -/
example : Nonempty ((AddMonoidHom.mulLeft ((24 : ℕ) : ZMod 1440)).ker ≃+ ZMod 24) := by
  haveI : NeZero (1440 : ℕ) := ⟨by norm_num⟩
  have e := ker_mulLeft_addEquiv 1440 24
  rw [show Nat.gcd 1440 24 = 24 from by norm_num] at e
  exact ⟨e⟩
/-- The same modulus splits primewise by the n-fold CRT: `ℤ/1440 ≅ Π_q ℤ/q^{v_q}`. -/
example : Nonempty (ZMod 1440 ≃+*
    Π (q : (1440 : ℕ).primeFactors), ZMod (q ^ ((1440 : ℕ).factorization q))) :=
  ⟨crt_pi_iso (by norm_num)⟩
/-- **Example 2 (coprime).** `gcd(24,35) = 1`, so `Tor = 0`: `ker ≅ ℤ/1`. -/
example : Nonempty ((AddMonoidHom.mulLeft ((35 : ℕ) : ZMod 24)).ker ≃+ ZMod 1) := by
  haveI : NeZero (24 : ℕ) := ⟨by norm_num⟩
  have e := ker_mulLeft_addEquiv 24 35
  rw [show Nat.gcd 24 35 = 1 from by norm_num] at e
  exact ⟨e⟩
/-- **Example 3 (single prime power).** `N = 9, M = 12`: `ker(×12 on ℤ/9) ≅ ℤ/3`. -/
example : Nonempty ((AddMonoidHom.mulLeft ((12 : ℕ) : ZMod 9)).ker ≃+ ZMod 3) := by
  haveI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  have e := ker_mulLeft_addEquiv 9 12
  rw [show Nat.gcd 9 12 = 3 from by norm_num] at e
  exact ⟨e⟩
end GroupExamples

/-! ## §M — IC readout through the group isomorphism (Cor 2777, group form). -/

/-- **Cor (group-level IC readout).** Routed through the group isomorphism
`ker(×M on ℤ/N) ≃+ ℤ/gcd(N,M)` (§I), the *order of the derived obstruction group*
equals `exp(IC(M;N))` — upgrading `card_Tor_eq_exp_IC` from the bare `gcd` to the
actual group `ker`. -/
theorem card_ker_eq_exp_IC (N : ℕ) [NeZero N] (M : ℕ) (hM : M ≠ 0) :
    (Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker : ℝ) = Real.exp (IC M N) := by
  haveI : NeZero (Nat.gcd N M) := ⟨Nat.gcd_ne_zero_left (NeZero.ne N)⟩
  rw [Nat.card_congr (ker_mulLeft_addEquiv N M).toEquiv, Nat.card_eq_fintype_card, ZMod.card,
      Nat.gcd_comm, card_Tor_eq_exp_IC hM (NeZero.ne N)]

/-- **Example 1, symbolic IC (§4.4.5).** `IC(24;1440) = 3·log 2 + log 3`, obtained
robustly from `gcd(24,1440) = 24 = 2³·3` via `card_Tor_eq_exp_IC`. -/
example : IC 24 1440 = 3 * Real.log 2 + Real.log 3 := by
  have h := card_Tor_eq_exp_IC (M := 24) (N := 1440) (by norm_num) (by norm_num)
  rw [show Nat.gcd 24 1440 = 24 from by norm_num] at h
  have h24 : IC 24 1440 = Real.log 24 := by
    rw [← Real.log_exp (IC 24 1440), ← h]; norm_num
  rw [h24, show (24 : ℝ) = 2 ^ 3 * 3 from by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  push_cast; ring

/-! ## §N — Global certification (Theorem 1/18), CONDITIONAL skeleton.

The core file (§H) formalizes only the gluing *mechanism* and deliberately does NOT
certify "prime ⇔ global section", because the `(⇐)` completeness direction — that
the four layers (in particular the EC/AKS regularity layer) exclude every composite
— is a deep claim, NOT an elementary arithmetic fact, and the supporting machinery
(AKS/ECPP primality, the sheaf/site model, p-adic-log/Baker bounds, étale/motivic
detectors) is ABSENT from Mathlib.  Assuming the certification as a bare hypothesis
on the conclusion would be circular.

Here we record Theorem 18's logical ARCHITECTURE honestly: a global section is
membership in all four layer-predicates; *soundness* of the EC layer yields the
`(⇐)` direction automatically, while *completeness* is isolated as the single
EXPLICIT hypothesis `Hcomplete` (the paper's EC/AKS content, NOT proved here).  This
is the same conditional style as `derived_equalizer_tfae` (Thm 20).  ⚠ It does NOT
prove primality certification; it makes precise WHERE the unproved content sits. -/

/-- **Theorem 1 / 18 (CONDITIONAL).** With the four layers as predicates and the EC
layer sound (`FEC X → X.Prime`), `X` is prime iff it carries a global section (lies
in all four layers), GIVEN the completeness hypothesis `Hcomplete`.  Soundness is
discharged here; completeness remains the paper's deep, unformalized input. -/
theorem certification_iff_of_complete
    (Fnum Fmod Fpadic FEC : ℕ → Prop) (X : ℕ)
    (Hsound : FEC X → X.Prime)
    (Hcomplete : X.Prime → Fnum X ∧ Fmod X ∧ Fpadic X ∧ FEC X) :
    X.Prime ↔ (Fnum X ∧ Fmod X ∧ Fpadic X ∧ FEC X) :=
  ⟨Hcomplete, fun ⟨_, _, _, hEC⟩ => Hsound hEC⟩

/-! ## §O — Functoriality / naturality of the obstruction (partial: M-tower + order).

The paper states the primewise decomposition is "natural in M and in the
factorization of N".  The BINARY group-level additivity (Lemma B/11) is now
formalized via `kerTransport`/`ker_additivity_coprime` below.  ⚠ Still open: full
naturality of `Tor₁(ℤ/M, -)` as a NATURAL transformation (needs the Tor FUNCTOR,
absent here by design — kernels are proxies) and the n-fold `Tor(⊕ᵢBᵢ) ≅ ⊕ᵢTor(Bᵢ)`
(needs iterating `ker_additivity_coprime` over the prime factorisation). -/

/-- Functoriality of the obstruction in `M`: multiplication-by-`M` is a composition
tower, `×(M₁·M₂) = ×M₁ ∘ ×M₂` on `ℤ/N`.  (So obstruction kernels are nested along
divisibility of `M`.) -/
theorem mulLeft_mul_comp (N : ℕ) [NeZero N] (M₁ M₂ : ℕ) :
    AddMonoidHom.mulLeft ((M₁ : ZMod N) * (M₂ : ZMod N))
      = (AddMonoidHom.mulLeft (M₁ : ZMod N)).comp (AddMonoidHom.mulLeft (M₂ : ZMod N)) := by
  ext x; exact mul_assoc (M₁ : ZMod N) (M₂ : ZMod N) x

/-- Order-level additivity (the `|Tor|` shadow of Lemma B/11): the order of the
derived obstruction is multiplicative over coprime CRT factors, i.e. `exp(IC)` is
multiplicative — `|Tor|(N₁N₂) = |Tor|(N₁)·|Tor|(N₂)` for `gcd(N₁,N₂)=1`. -/
theorem exp_IC_coprime_mul {M N₁ N₂ : ℕ} (hN₁ : N₁ ≠ 0) (hN₂ : N₂ ≠ 0)
    (h : Nat.Coprime N₁ N₂) :
    Real.exp (IC M (N₁ * N₂)) = Real.exp (IC M N₁) * Real.exp (IC M N₂) := by
  rw [IC_coprime_add hN₁ hN₂ h, Real.exp_add]

/-- gcd is multiplicative over coprime moduli (per-prime, via disjoint supports):
`gcd(N₁N₂, M) = gcd(N₁,M)·gcd(N₂,M)` when `gcd(N₁,N₂)=1`. -/
theorem gcd_mul_coprime {N₁ N₂ M : ℕ} (hN₁ : N₁ ≠ 0) (hN₂ : N₂ ≠ 0) (h : Nat.Coprime N₁ N₂) :
    Nat.gcd (N₁ * N₂) M = Nat.gcd N₁ M * Nat.gcd N₂ M := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp
  refine Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left (Nat.mul_ne_zero hN₁ hN₂))
      (Nat.mul_ne_zero (Nat.gcd_ne_zero_left hN₁) (Nat.gcd_ne_zero_left hN₂)) (fun p => ?_)
  rw [factorization_gcd_apply (Nat.mul_ne_zero hN₁ hN₂) hM,
      Nat.factorization_mul (Nat.gcd_ne_zero_left hN₁) (Nat.gcd_ne_zero_left hN₂),
      Finsupp.add_apply, factorization_gcd_apply hN₁ hM, factorization_gcd_apply hN₂ hM,
      Nat.factorization_mul hN₁ hN₂, Finsupp.add_apply]
  have hdisj : N₁.factorization p = 0 ∨ N₂.factorization p = 0 := by
    by_contra hc
    push_neg at hc
    have m1 : p ∈ N₁.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hc.1
    have m2 : p ∈ N₂.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hc.2
    exact (Finset.disjoint_left.mp h.disjoint_primeFactors m1) m2
  rcases hdisj with h0 | h0 <;> rw [h0] <;> simp

/-- **Order-level additivity (Lemma B/11, binary shadow).** The order of the derived
obstruction group is multiplicative over coprime CRT factors:
`|ker(×M on ℤ/N₁N₂)| = |ker(×M on ℤ/N₁)|·|ker(×M on ℤ/N₂)|`.  (Upgraded to a genuine
group isomorphism by `ker_additivity_coprime` below.) -/
theorem card_ker_mul_coprime {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (M : ℕ)
    (h : Nat.Coprime N₁ N₂) :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod (N₁ * N₂))).ker
      = Nat.card (AddMonoidHom.mulLeft (M : ZMod N₁)).ker
        * Nat.card (AddMonoidHom.mulLeft (M : ZMod N₂)).ker := by
  haveI : NeZero (N₁ * N₂) := ⟨Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne N₂)⟩
  rw [card_ker_mulLeft, card_ker_mulLeft, card_ker_mulLeft,
      gcd_mul_coprime (NeZero.ne N₁) (NeZero.ne N₂) h]

/-- **Transport of the obstruction across an additive iso (naturality core).**
If `e : A ≃+ B` intertwines two additive endomorphisms, `e ∘ f = g ∘ e`, then the
obstruction kernels are isomorphic *as groups*, `ker f ≃+ ker g`.  This is the
transport lemma that the GROUP-level Tor additivity (Lemma B/11) requires. -/
def kerTransport {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (f : A →+ A) (g : B →+ B) (h : ∀ a, e (f a) = g (e a)) : f.ker ≃+ g.ker where
  toFun x := ⟨e x.1, by
    rw [AddMonoidHom.mem_ker, ← h x.1, AddMonoidHom.mem_ker.mp x.2, map_zero]⟩
  invFun y := ⟨e.symm y.1, by
    rw [AddMonoidHom.mem_ker]; apply e.injective
    rw [h, e.apply_symm_apply, AddMonoidHom.mem_ker.mp y.2, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)

/-- **Lemma B/11 at the GROUP level (binary, step 1).** Via the binary CRT ring iso,
the obstruction group transports: `ker(×M on ℤ/N₁N₂) ≃+ ker(×M on ℤ/N₁ × ℤ/N₂)`. -/
noncomputable def ker_crt_transport {N₁ N₂ : ℕ} (M : ℕ) (h : Nat.Coprime N₁ N₂) :
    (AddMonoidHom.mulLeft (M : ZMod (N₁ * N₂))).ker ≃+
      (AddMonoidHom.mulLeft (M : ZMod N₁ × ZMod N₂)).ker := by
  refine kerTransport (ZMod.chineseRemainder h).toAddEquiv _ _ (fun a => ?_)
  show (ZMod.chineseRemainder h) ((M : ZMod (N₁ * N₂)) * a)
      = (M : ZMod N₁ × ZMod N₂) * (ZMod.chineseRemainder h) a
  rw [map_mul, map_natCast]

/-- **Lemma B/11 at the GROUP level (binary, step 2).** The obstruction on a product
ring splits as the product of obstructions:
`ker(×M on A × B) ≃+ ker(×M on A) × ker(×M on B)`. -/
def ker_mulLeft_prod {A B : Type*} [Ring A] [Ring B] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : A × B)).ker ≃+
      (AddMonoidHom.mulLeft (M : A)).ker × (AddMonoidHom.mulLeft (M : B)).ker := by
  have hset : (AddMonoidHom.mulLeft (M : A × B)).ker
      = (AddMonoidHom.mulLeft (M : A)).ker.prod (AddMonoidHom.mulLeft (M : B)).ker := by
    ext ⟨a, b⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    show (M : A × B) * (a, b) = 0 ↔ (M : A) * a = 0 ∧ (M : B) * b = 0
    rw [show ((M : A × B)) = ((M : A), (M : B)) from rfl, Prod.mk_mul_mk, Prod.mk_eq_zero]
  rw [hset]
  exact AddSubgroup.prodEquiv _ _

/-- **Lemma B/11 at the GROUP level (binary).** Composing the two steps: the derived
obstruction is additive over coprime CRT factors *as a group*,
`ker(×M on ℤ/N₁N₂) ≃+ ker(×M on ℤ/N₁) × ker(×M on ℤ/N₂)`. -/
noncomputable def ker_additivity_coprime {N₁ N₂ : ℕ} (M : ℕ) (h : Nat.Coprime N₁ N₂) :
    (AddMonoidHom.mulLeft (M : ZMod (N₁ * N₂))).ker ≃+
      (AddMonoidHom.mulLeft (M : ZMod N₁)).ker × (AddMonoidHom.mulLeft (M : ZMod N₂)).ker :=
  (ker_crt_transport M h).trans (ker_mulLeft_prod M)

/-! ## §P — Amalgam as sectionwise intersection (Group-2 fragment, NOT the full site).

⚠ The paper's Group 2 asks for the principal-open site on `Spec ℤ` with a Grothendieck
topology and four layer SUBSHEAVES — a large `CategoryTheory.Sites` construction that
is NOT done here.  What we record unconditionally is only the *sectionwise* algebra the
proof uses: over a fixed open, the amalgam section set is the intersection of the four
layer section sets, `Γ(U,F) = Γ(U,Fnum) ∩ Γ(U,Fmod) ∩ Γ(U,Fp) ∩ Γ(U,FEC)`. -/

/-- Sectionwise amalgam: membership in the fiber-product section set is the
conjunction of the four layer memberships. -/
theorem amalgam_mem_iff (Fnum Fmod Fpadic FEC : Set ℕ) (X : ℕ) :
    X ∈ Fnum ∩ Fmod ∩ Fpadic ∩ FEC
      ↔ X ∈ Fnum ∧ X ∈ Fmod ∧ X ∈ Fpadic ∧ X ∈ FEC := by
  simp only [Set.mem_inter_iff]; tauto

/-! ## Examples (Examples 1–3 of §4.3) and the corrected discrepancy. -/

section Examples
/-- Example 1 (mixed composite): `M = 2³·3 = 24`, `N = 2⁵·3²·5 = 1440`; `gcd = 24`. -/
example : Nat.gcd 24 1440 = 24 := by norm_num
/-- Example 2 (coprime): `gcd(35, 24) = 1`, so `Tor₁ = 0`. -/
example : Nat.gcd 35 24 = 1 := by norm_num
/-- Example 3 (single prime power): `gcd(12, 9) = 3`, so `Tor₁ ≅ ℤ/3`. -/
example : Nat.gcd 12 (3 ^ 2) = 3 := by norm_num
/-- The corrected Zero-Class discrepancy on `M=12, N=9`: the intersection is
    `(lcm 12 9) = (36)`, with `36 ∣ T` (not `gcd 3 ∣ T`) the true membership test. -/
example : Nat.lcm 12 9 = 36 := by norm_num
example : (9 : ℕ) ∣ Nat.lcm 12 9 := by norm_num     -- v₃(intersection) = 2 = max
example : ¬ (27 : ℕ) ∣ Nat.lcm 12 9 := by norm_num
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms kernel_mem_iff_lcm
#print axioms zeroClass_mem_iff_lcm
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms lcm_dvd_iff_max
#print axioms card_ker_mulLeft
#print axioms obstructionFree_iff_card
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms IC_mono
#print axioms IC_coprime_add
#print axioms thickness_stable_coprime
#print axioms derived_equalizer_tfae
#print axioms overlap_glue_iff_lcm
#print axioms ker_mulLeft_addEquiv
#print axioms ker_trivial_of_coprime
#print axioms crt_pi_iso
#print axioms log2_mul_sum_min_le_IC
#print axioms sum_min_le_IC_div_log2
#print axioms cost_affine_bound
#print axioms card_ker_eq_exp_IC
#print axioms certification_iff_of_complete
#print axioms mulLeft_mul_comp
#print axioms exp_IC_coprime_mul
#print axioms gcd_mul_coprime
#print axioms card_ker_mul_coprime
#print axioms kerTransport
#print axioms ker_crt_transport
#print axioms ker_mulLeft_prod
#print axioms ker_additivity_coprime
#print axioms amalgam_mem_iff
end AxiomAudit

end Spt3

/-
================================================================================
  Spt3Sheaf.lean — Group-2 fragment of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification".

  A GENUINE site + constant presheaf + fiber-product subpresheaf, kernel-checked
  against Mathlib (sorry-free, axiom-free).  This realises §2.1 / §3.2 / §4.5 at
  the PRESHEAF level:

    • the site  S = Spec ℤ  with its open-cover Grothendieck topology
      (`Opens.grothendieckTopology`);
    • the ambient constant presheaf  B := ℕ  of candidate integers;
    • the four decision layers  Fnum, Fmod, Fp-adic, FEC ⊆ B  as genuine
      sub-presheaves (`CategoryTheory.Subfunctor`, the de-deprecated `Subpresheaf`);
    • their amalgam  F := Fnum ×_B Fmod ×_B Fp-adic ×_B FEC  as the lattice meet
      `⊓` of subpresheaves — a real fiber product over `B`;
    • the sectionwise identity  Γ(U,F) = ⋂ᵢ Γ(U,Fᵢ)  and restriction-as-inclusion
      `F ↪ B`.

  ⚠ HONEST SCOPE.  This is the PRESHEAF skeleton of the four-layer amalgam, which is
  exactly what the paper's "sections are computed sectionwise" claim uses.  It does
  NOT include: the SHEAF condition / sheafification of `B` and the layers (the
  constant presheaf is not a sheaf), the specific arithmetic CONTENT of each layer
  (`Fnum`,…,`FEC` are taken as arbitrary subpresheaves here), nor the terminal/
  minimality/independence claims (§2.3).  Those remain future work.
================================================================================
-/

open CategoryTheory TopologicalSpace

namespace Spt3Sheaf

/-- The arithmetic base `S = Spec ℤ`, as a topological space (Zariski topology). -/
abbrev S : Type := PrimeSpectrum ℤ

/-- **The site (§2.1).** The open-cover Grothendieck topology on the opens of
`Spec ℤ` — the principal-open basis generates this same topology. -/
abbrev siteJ : GrothendieckTopology (Opens S) := Opens.grothendieckTopology S

/-- **The ambient constant presheaf `B := ℕ` (§3.2).** Candidate integers on `S`. -/
abbrev B : (Opens S)ᵒᵖ ⥤ Type := (Functor.const (Opens S)ᵒᵖ).obj ℕ

variable (Fnum Fmod Fpadic FEC : Subfunctor B)

/-- **The amalgam `F := Fnum ×_B Fmod ×_B Fp-adic ×_B FEC` (§3.2).** The fiber
product over `B` of the four layers, realised as the lattice meet of subpresheaves. -/
abbrev amalgam : Subfunctor B := Fnum ⊓ Fmod ⊓ Fpadic ⊓ FEC

/-- **Sectionwise sections (§4.5).**
`Γ(U,F) = Γ(U,Fnum) ∩ Γ(U,Fmod) ∩ Γ(U,Fp-adic) ∩ Γ(U,FEC)`. -/
theorem amalgam_obj (U : (Opens S)ᵒᵖ) :
    (amalgam Fnum Fmod Fpadic FEC).obj U
      = Fnum.obj U ∩ Fmod.obj U ∩ Fpadic.obj U ∩ FEC.obj U := by
  simp only [amalgam, Subfunctor.min_obj]

/-- Membership form: a section is a global/local section of the amalgam iff it
satisfies all four layer predicates simultaneously. -/
theorem mem_amalgam {U : (Opens S)ᵒᵖ} (s : B.obj U) :
    s ∈ (amalgam Fnum Fmod Fpadic FEC).obj U
      ↔ s ∈ Fnum.obj U ∧ s ∈ Fmod.obj U ∧ s ∈ Fpadic.obj U ∧ s ∈ FEC.obj U := by
  rw [amalgam_obj]; simp only [Set.mem_inter_iff]; tauto

/-- **Restriction is inclusion (§4.5).** The amalgam is a genuine subpresheaf of the
ambient `B`: there is a canonical monomorphism `F ↪ B` whose components are the
inclusions of section sets, so restriction along `V ⊆ U` is inclusion. -/
def amalgamι : (amalgam Fnum Fmod Fpadic FEC).toFunctor ⟶ B :=
  (amalgam Fnum Fmod Fpadic FEC).ι

/-- The amalgam sits below each layer in the subpresheaf lattice (it refines each
gate): `F ≤ Fnum`, `F ≤ Fmod`, `F ≤ Fp-adic`, `F ≤ FEC`. -/
theorem amalgam_le_FEC : amalgam Fnum Fmod Fpadic FEC ≤ FEC := by
  simp only [amalgam]; exact inf_le_right
theorem amalgam_le_Fnum : amalgam Fnum Fmod Fpadic FEC ≤ Fnum := by
  simp only [amalgam]
  exact le_trans inf_le_left (le_trans inf_le_left inf_le_left)

section AxiomAudit
#print axioms amalgam_obj
#print axioms mem_amalgam
#print axioms amalgamι
#print axioms amalgam_le_FEC
#print axioms amalgam_le_Fnum
end AxiomAudit

end Spt3Sheaf

/-
================================================================================
  Spt3Cert.lean — Group-4 fragment (the EC/AKS completeness layer) of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification".

  Theorem 18's hard `(⇐)` direction needs the EC/AKS layer `FEC` to be a SOUND +
  COMPLETE primality certificate.  Mathlib has NO AKS and NO ECPP.  But it DOES have
  the Lucas–Pratt certificate (`lucas_primality_iff`), which is genuinely sound and
  complete.  We use it as a concrete, fully-proved stand-in for `FEC` to show that
  the §5 global-section certification provably CLOSES once `FEC` is any sound+complete
  certificate — and we name the missing AKS input precisely.

  sorry-free, axiom-free.

  ⚠ HONEST SCOPE.  `LucasCert` is NOT the paper's EC/AKS gate; it is a different
  (also complete) certificate that Mathlib actually proves.  Replacing it by a real
  formalized AKS is the open problem `AKSIsComplete` named below.
================================================================================
-/

namespace Spt3Cert

/-- The Lucas–Pratt certificate predicate, used as a concrete sound+complete `FEC`. -/
def LucasCert (p : ℕ) : Prop :=
  ∃ a : ZMod p, a ^ (p - 1) = 1 ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1

/-- **Soundness** of the Lucas layer: a certificate forces primality. -/
theorem LucasCert_sound {p : ℕ} (h : LucasCert p) : p.Prime :=
  (lucas_primality_iff p).mpr h

/-- **Completeness** of the Lucas layer: every prime carries a certificate.  This is
exactly the deep `Hcomplete` the paper ASSUMES for EC/AKS — here it is a THEOREM. -/
theorem LucasCert_complete {p : ℕ} (h : p.Prime) : LucasCert p :=
  (lucas_primality_iff p).mp h

/-- **Certification, instantiated and UNCONDITIONALLY proved.** With the three
elementary layers trivial and `FEC := LucasCert`, the global-section certification
"prime ⇔ ∃ section" holds with BOTH directions proved, because the Lucas/Pratt
certificate is a genuine sound+complete primality certificate.  This is the honest
realisation of Theorem 18's architecture with a real (non-AKS) complete layer. -/
theorem prime_iff_section (X : ℕ) :
    X.Prime ↔ (True ∧ True ∧ True ∧ LucasCert X) :=
  ⟨fun h => ⟨trivial, trivial, trivial, LucasCert_complete h⟩,
   fun ⟨_, _, _, h⟩ => LucasCert_sound h⟩

/-- The single missing input for the paper's own layer, named as a Prop (NOT proved):
"a formalized AKS gate is a sound+complete primality certificate". -/
def AKSIsComplete (FEC_AKS : ℕ → Prop) : Prop := ∀ X, X.Prime ↔ FEC_AKS X

/-- Given ANY sound+complete layer (e.g. a future formalized AKS satisfying
`AKSIsComplete`), the certification closes.  This isolates the exact deep input. -/
theorem prime_iff_section_of_complete (FEC : ℕ → Prop)
    (hFEC : AKSIsComplete FEC) (X : ℕ) : X.Prime ↔ FEC X := hFEC X

section AxiomAudit
#print axioms LucasCert_sound
#print axioms LucasCert_complete
#print axioms prime_iff_section
#print axioms prime_iff_section_of_complete
end AxiomAudit

end Spt3Cert


/-! ============================================================================
    CHECKLIST ADDITIONS (Categories A–F) — integrated with Spt3 / Spt3Sheaf /
    Spt3Cert above.  sorry-free, axiom-free (audited at the end).

    Several checklist statements are mathematically FALSE as written; consistent
    with the existing file's "corrections" philosophy we prove the CORRECT version
    and flag the error.  The four corrections are:
      • A-3 / F-1 : the inclusion direction is `ker(×M₁) ≤ ker(×M₂)` for `M₁ ∣ M₂`
                    (the checklist's `ker(×M₂) ≤ ker(×M₁)` is false — `ker_mono_dvd_false`).
      • A-8       : the *localized intersection* thickness is `max`, not `min`
                    (same min/max conflation the file already corrects).
      • B-5       : the triple-overlap cocycle gives `b ∣ s₁-s₃`, not the full
                    `lcm(lcm a b)c ∣ s₁-s₃` (which is false).
      • C-1       : `V(kernel) = V(lcm)`, and `V(lcm) ≠ V(gcd)` in general (the
                    checklist's `V(gcd)` is the *support of the Tor module*, a
                    different object).
============================================================================ -/

namespace Spt3

/-! ### Category A — algebraic / arithmetic group-iso completions. -/

/-- **A-1 (Lemma B, binary group iso).** The obstruction group splits over coprime
CRT factors.  This is exactly `ker_additivity_coprime`, exposed under the checklist name. -/
noncomputable def ker_mulLeft_addEquiv_prod {N₁ N₂ : ℕ} (M : ℕ) (h : Nat.Coprime N₁ N₂) :
    (AddMonoidHom.mulLeft (M : ZMod (N₁ * N₂))).ker ≃+
      (AddMonoidHom.mulLeft (M : ZMod N₁)).ker × (AddMonoidHom.mulLeft (M : ZMod N₂)).ker :=
  ker_additivity_coprime M h

/-- **A-2 (n-fold decomposition, order level).** The order of the obstruction group
factors primewise: `|ker(×M on ℤ/N)| = ∏_{q∣N} q^{min(v_q M, v_q N)}`.  (The full
n-fold *group* iso `⊕_q ker` is the open item already named in §O; this is its order
shadow, proved from `card_ker_mulLeft` + `gcd_eq_prod_primeFactors`.) -/
theorem card_ker_mulLeft_pi_prod {M N : ℕ} [NeZero N] (hM : M ≠ 0) (hN : N ≠ 0) :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker
      = ∏ q ∈ N.primeFactors, q ^ min (M.factorization q) (N.factorization q) := by
  rw [card_ker_mulLeft, Nat.gcd_comm]
  exact gcd_eq_prod_primeFactors hM hN

/-- **A-3 / F-1 (CORRECTED direction).** If `M₁ ∣ M₂` then the `×M₂` gate kills at
least as much as `×M₁`: `ker(×M₁) ≤ ker(×M₂)`. -/
theorem ker_mono_of_dvd {N : ℕ} [NeZero N] {M₁ M₂ : ℕ} (h : M₁ ∣ M₂) :
    (AddMonoidHom.mulLeft (M₁ : ZMod N)).ker ≤ (AddMonoidHom.mulLeft (M₂ : ZMod N)).ker := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx ⊢
  have hx' : (M₁ : ZMod N) * x = 0 := hx
  show ((M₁ * k : ℕ) : ZMod N) * x = 0
  have hcalc : ((M₁ * k : ℕ) : ZMod N) * x = (k : ZMod N) * ((M₁ : ZMod N) * x) := by
    push_cast; ring
  rw [hcalc, hx', mul_zero]

/-- ⚠ **A-3/F-1 stated direction is FALSE.** With `N=4, M₁=2, M₂=4` (so `M₁ ∣ M₂`),
`1 ∈ ker(×4)` but `1 ∉ ker(×2)`, so `ker(×M₂) ≤ ker(×M₁)` fails. -/
theorem ker_mono_dvd_false :
    ¬ ∀ (N : ℕ) [NeZero N] (M₁ M₂ : ℕ), M₁ ∣ M₂ →
      (AddMonoidHom.mulLeft (M₂ : ZMod N)).ker ≤ (AddMonoidHom.mulLeft (M₁ : ZMod N)).ker := by
  intro H
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have hle := H 4 2 4 (by norm_num)
  have hmem : (1 : ZMod 4) ∈ (AddMonoidHom.mulLeft ((4 : ℕ) : ZMod 4)).ker := by
    rw [AddMonoidHom.mem_ker]
    show ((4 : ℕ) : ZMod 4) * 1 = 0
    rw [ZMod.natCast_self, zero_mul]
  have hbad := hle hmem
  rw [AddMonoidHom.mem_ker] at hbad
  have h2 : ((2 : ℕ) : ZMod 4) * 1 = 0 := hbad
  rw [mul_one] at h2
  exact absurd h2 (by decide)

/-- **A-4 (refutation of paper §3.4(3)).** The paper's original Zero-Class formula
`T ∈ (M)∩(pk) ↔ lcm∣T ∨ gcd∣T` is false: `gcd ∣ T` does NOT force membership. -/
theorem paper_zeroClass_false :
    ¬ ∀ (M pk T : ℤ),
      (T ∈ Ideal.span {M} ⊓ Ideal.span {pk}) ↔ (lcm M pk ∣ T ∨ (Int.gcd M pk : ℤ) ∣ T) := by
  intro H
  have h := H 12 9 3
  rw [zeroClass_mem_iff_lcm] at h
  have hg : ((Int.gcd 12 9 : ℤ)) ∣ 3 := by norm_num
  have hl : ¬ (lcm (12 : ℤ) 9 ∣ 3) := by
    intro hd
    have : (9 : ℤ) ∣ 3 := dvd_trans (dvd_lcm_right 12 9) hd
    norm_num at this
  exact hl (h.mpr (Or.inr hg))

/-- The explicit `M=12, pk=9, T=3` witness for A-4. -/
example : ((Int.gcd 12 9 : ℤ)) ∣ 3 ∧
    ¬ (3 : ℤ) ∈ Ideal.span {(12 : ℤ)} ⊓ Ideal.span {(9 : ℤ)} := by
  refine ⟨by norm_num, ?_⟩
  rw [zeroClass_mem_iff_lcm]
  intro hd
  have : (9 : ℤ) ∣ 3 := dvd_trans (dvd_lcm_right 12 9) hd
  norm_num at this

/-- **A-5 (IC vanishing criterion).** `IC(M;N) = 0 ↔ gcd(M,N) = 1 ↔ coprime`. -/
theorem IC_eq_zero_iff_coprime {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    IC M N = 0 ↔ Nat.Coprime M N := by
  have hgcd : (Nat.gcd M N : ℝ) = Real.exp (IC M N) := card_Tor_eq_exp_IC hM hN
  rw [Nat.Coprime]
  constructor
  · intro h0
    rw [h0, Real.exp_zero] at hgcd
    exact_mod_cast hgcd
  · intro hco
    rw [hco] at hgcd
    have h1 : Real.exp (IC M N) = 1 := by exact_mod_cast hgcd.symm
    have hlog := Real.log_exp (IC M N)
    rw [h1, Real.log_one] at hlog
    exact hlog.symm

/-- `log N = ∑_{q∣N} v_q(N)·log q` for `N ≠ 0`. -/
theorem log_eq_sum_factorization {N : ℕ} (hN : N ≠ 0) :
    Real.log N = ∑ q ∈ N.primeFactors, (N.factorization q : ℝ) * Real.log q := by
  have hprod : (∏ q ∈ N.primeFactors, q ^ N.factorization q) = N := by
    rw [← Nat.support_factorization, ← Finsupp.prod, Nat.factorization_prod_pow_eq_self hN]
  have hne : ∀ q ∈ N.primeFactors, ((q ^ N.factorization q : ℕ) : ℝ) ≠ 0 := by
    intro q hq
    have hqp := (Nat.mem_primeFactors.mp hq).1
    exact_mod_cast pow_ne_zero _ hqp.pos.ne'
  calc Real.log N
      = Real.log ((∏ q ∈ N.primeFactors, q ^ N.factorization q : ℕ) : ℝ) := by rw [hprod]
    _ = Real.log (∏ q ∈ N.primeFactors, ((q ^ N.factorization q : ℕ) : ℝ)) := by rw [Nat.cast_prod]
    _ = ∑ q ∈ N.primeFactors, Real.log ((q ^ N.factorization q : ℕ) : ℝ) := Real.log_prod hne
    _ = ∑ q ∈ N.primeFactors, (N.factorization q : ℝ) * Real.log q := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Nat.cast_pow, Real.log_pow]

/-- **A-6 (IC upper bound).** `IC(M;N) ≤ log N`. -/
theorem IC_le_log_N {M N : ℕ} (hN : N ≠ 0) : IC M N ≤ Real.log N := by
  rw [IC, log_eq_sum_factorization hN]
  refine Finset.sum_le_sum (fun q hq => ?_)
  have hqp := (Nat.mem_primeFactors.mp hq).1
  have hlog : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqp.one_lt.le)
  apply mul_le_mul_of_nonneg_right _ hlog
  exact_mod_cast min_le_right (M.factorization q) (N.factorization q)

/-- **A-7 (thickness contrast).** Tor thickness is `min` (gcd), intersection thickness
is `max` (lcm), and in general `gcd ≠ lcm`. -/
theorem thickness_tor_vs_intersection {M pk : ℕ} (hM : M ≠ 0) (hpk : pk ≠ 0) (p : ℕ) :
    (Nat.gcd M pk).factorization p = min (M.factorization p) (pk.factorization p)
      ∧ (Nat.lcm M pk).factorization p = max (M.factorization p) (pk.factorization p)
      ∧ ∃ a b : ℕ, Nat.gcd a b ≠ Nat.lcm a b :=
  ⟨factorization_gcd_apply hM hpk p, factorization_lcm_apply hM hpk p, 2, 3, by decide⟩

/-- **A-8 (Prop 7, CORRECTED localized thickness).** The intersection `(M)∩(p^k)=(lcm)`
has `p`-valuation `max(v_p M, k)`, so localizing at `p` keeps `p^{max}`.  ⚠ The paper's
`p^{min}` again conflates the gcd/Tor thickness with the intersection thickness.  (Full
`Localization` API formalization deferred; this is the valuation identity it rests on.) -/
theorem localized_intersection_valuation {M : ℕ} (k : ℕ) (hM : M ≠ 0) {p : ℕ} (hp : p.Prime) :
    (Nat.lcm M (p ^ k)).factorization p = max (M.factorization p) k := by
  rw [factorization_lcm_apply hM (pow_ne_zero k hp.pos.ne'), Nat.factorization_pow_self hp]

/-! ### Category C — `PrimeSpectrum` support sets. -/

/-- **C-1 (CORRECTED support equality).** The kernel ideal is `(lcm)`, so its zero
locus is `V(lcm)`: `V((M)∩(N)) = V(lcm M N)`.  ⚠ The checklist's `V(gcd)` is the
support of the *Tor module* `ℤ/gcd`, a different set (`V(lcm) ≠ V(gcd)` whenever `M, N`
have a non-common prime, e.g. `M=12, N=9`). -/
theorem kernel_intersection_zeroLocus (M N : ℤ) :
    PrimeSpectrum.zeroLocus (↑(Ideal.span {M} ⊓ Ideal.span {N}) : Set ℤ) =
      PrimeSpectrum.zeroLocus (↑(Ideal.span {lcm M N}) : Set ℤ) := by
  rw [kernel_ideal_inter]

/-- **C-3 (good prime: empty support).** If `M, N` are coprime the obstruction support
vanishes: `V(gcd(M,N)) = V(1) = ∅`. -/
theorem good_prime_no_support {M N : ℕ} (h : Nat.Coprime M N) :
    PrimeSpectrum.zeroLocus (↑(Ideal.span {(Nat.gcd M N : ℤ)}) : Set ℤ) = ∅ := by
  have h1 : Nat.gcd M N = 1 := h
  have hg : (Nat.gcd M N : ℤ) = 1 := by exact_mod_cast h1
  rw [hg, Ideal.span_singleton_one]
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl

/-! ### Category E — missing lemmas (§4.4 / 4.6 / 5.2). -/

/-- **E-1 (Lemma C, generator).** The obstruction group on a prime power is cyclic:
it has a single additive generator. -/
theorem ker_mulLeft_generator (q k : ℕ) [Fact q.Prime] [NeZero (q ^ k)] (M : ℕ) :
    ∃ g : (AddMonoidHom.mulLeft (M : ZMod (q ^ k))).ker, AddSubgroup.zmultiples g = ⊤ :=
  isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance

/-- **E-2 (Stability box, Prop 8).** A bundle of the stability invariants of the pair. -/
structure StabilityBox (M N : ℕ) : Prop where
  kernel_eq : ∀ T : ℤ, T ∈ Ideal.span {(M : ℤ)} ⊓ Ideal.span {(N : ℤ)} ↔ lcm (M : ℤ) (N : ℤ) ∣ T
  thickness_gcd : ∀ p, (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p)
  thickness_lcm : ∀ p, (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p)
  coprime_vanish : Nat.Coprime M N → Nat.gcd M N = 1

/-- The stability box holds for every nonzero pair. -/
theorem stabilityBox {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) : StabilityBox M N where
  kernel_eq T := zeroClass_mem_iff_lcm (M : ℤ) (N : ℤ) T
  thickness_gcd p := factorization_gcd_apply hM hN p
  thickness_lcm p := factorization_lcm_apply hM hN p
  coprime_vanish h := h

/-- **E-4 (Remark 19, component order).** The `q`-component obstruction order is
`q^{min(v_q M, v_q N)}`. -/
theorem Tor_component_order {M N : ℕ} (hM : M ≠ 0) {q : ℕ} (hq : q ∈ N.primeFactors) :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod (q ^ N.factorization q))).ker
      = q ^ min (M.factorization q) (N.factorization q) := by
  have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
  haveI : NeZero (q ^ N.factorization q) := ⟨pow_ne_zero _ hqp.pos.ne'⟩
  rw [card_ker_mulLeft]
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left (pow_ne_zero _ hqp.pos.ne'))
    (pow_ne_zero _ hqp.pos.ne')
  intro p
  rw [factorization_gcd_apply (pow_ne_zero _ hqp.pos.ne') hM]
  rcases eq_or_ne p q with rfl | hpq
  · rw [Nat.factorization_pow_self hqp, Nat.factorization_pow_self hqp, min_comm]
  · have hq0 : (q ^ N.factorization q).factorization p = 0 := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          Nat.Prime.factorization hqp, Finsupp.single_apply, if_neg (Ne.symm hpq), mul_zero]
    have hr0 : (q ^ min (M.factorization q) (N.factorization q)).factorization p = 0 := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          Nat.Prime.factorization hqp, Finsupp.single_apply, if_neg (Ne.symm hpq), mul_zero]
    rw [hq0, hr0]
    exact min_eq_left (Nat.zero_le _)

/-- The single-prime-power term of `IC`. -/
theorem IC_primepower_single {M N : ℕ} {q : ℕ} (hq : q ∈ N.primeFactors) :
    IC M (q ^ N.factorization q)
      = (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q := by
  have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
  have hk : N.factorization q ≠ 0 := by
    rw [← Nat.support_factorization] at hq; exact Finsupp.mem_support_iff.mp hq
  rw [IC, Nat.primeFactors_prime_pow hk hqp, Finset.sum_singleton,
      Nat.factorization_pow_self hqp]

/-- **E-5 (§3.6, IC primewise refinement).** `IC(M;N) = ∑_{q∣N} IC(M; q^{v_q N})`. -/
theorem IC_primepower_sum {M N : ℕ} (hN : N ≠ 0) :
    IC M N = ∑ q ∈ N.primeFactors, IC M (q ^ N.factorization q) := by
  rw [IC]
  exact Finset.sum_congr rfl (fun q hq => (IC_primepower_single hq).symm)

/-! ### Category F — structural improvements. -/

/-- **F-2 (IC boundary values).** `IC(M;1) = 0`, `IC(1;N) = 0`, `IC(N;N) = log N`. -/
theorem IC_one_right (M : ℕ) : IC M 1 = 0 := by
  rw [IC, Nat.primeFactors_one, Finset.sum_empty]

theorem IC_one_left (N : ℕ) : IC 1 N = 0 := by
  rw [IC]
  refine Finset.sum_eq_zero (fun q _ => ?_)
  rw [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero,
      min_eq_left (Nat.cast_nonneg _), zero_mul]

theorem IC_self {N : ℕ} (hN : N ≠ 0) : IC N N = Real.log N := by
  rw [IC, log_eq_sum_factorization hN]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [min_self]

/-- **F-3 (obstruction TFAE).** Coprimality, trivial obstruction order, trivial
obstruction group, and vanishing IC are all equivalent. -/
theorem obstruction_tfae {M N : ℕ} [NeZero N] (hM : M ≠ 0) :
    [Nat.Coprime M N,
     Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker = 1,
     (AddMonoidHom.mulLeft (M : ZMod N)).ker = ⊥,
     IC M N = 0].TFAE := by
  have hN : N ≠ 0 := NeZero.ne N
  tfae_have 1 → 2 := by
    intro h; rw [card_ker_mulLeft, Nat.gcd_comm]; exact h
  tfae_have 2 → 1 := by
    intro h; rw [card_ker_mulLeft, Nat.gcd_comm] at h; exact h
  tfae_have 2 ↔ 3 := AddSubgroup.card_eq_one
  tfae_have 1 ↔ 4 := (IC_eq_zero_iff_coprime hM hN).symm
  tfae_finish

/-- **F-4 (CRT gluing: unique solution).** Over coprime moduli the gluing system has a
unique solution — the exact-solution content behind `overlap_glue_iff_lcm`. -/
theorem crt_gluing_exists {M N : ℕ} (h : Nat.Coprime M N) (a : ZMod M) (b : ZMod N) :
    ∃! x : ZMod (M * N), (ZMod.chineseRemainder h) x = (a, b) := by
  refine ⟨(ZMod.chineseRemainder h).symm (a, b),
    (ZMod.chineseRemainder h).apply_symm_apply (a, b), ?_⟩
  intro y hy
  exact (ZMod.chineseRemainder h).injective
    (by rw [hy, (ZMod.chineseRemainder h).apply_symm_apply])

end Spt3

/-! ============================================================================
    Category B — sheaf-theoretic completions (Spt3Sheaf).
============================================================================ -/

namespace Spt3Sheaf

/-- The amalgam sits below `Fmod`. -/
theorem amalgam_le_Fmod (Fnum Fmod Fpadic FEC : Subfunctor B) :
    amalgam Fnum Fmod Fpadic FEC ≤ Fmod := by
  simp only [amalgam]
  exact le_trans (le_trans inf_le_left inf_le_left) inf_le_right

/-- The amalgam sits below `Fpadic`. -/
theorem amalgam_le_Fpadic (Fnum Fmod Fpadic FEC : Subfunctor B) :
    amalgam Fnum Fmod Fpadic FEC ≤ Fpadic := by
  simp only [amalgam]
  exact le_trans inf_le_left inf_le_right

/-- **B-2 (section uniqueness).** A section of the amalgam is determined by its
restrictions; in particular if two sections have all restrictions equal they are equal. -/
theorem amalgam_section_unique (Fnum Fmod Fpadic FEC : Subfunctor B)
    {U : (Opens S)ᵒᵖ} {s t : (amalgam Fnum Fmod Fpadic FEC).toFunctor.obj U}
    (h : ∀ {V : (Opens S)ᵒᵖ} (f : U ⟶ V),
        (amalgam Fnum Fmod Fpadic FEC).toFunctor.map f s =
          (amalgam Fnum Fmod Fpadic FEC).toFunctor.map f t) :
    s = t := by
  simpa using h (𝟙 U)

/-- **B-3 (terminal/meet property).** The amalgam is the largest subpresheaf below all
four layers: any `G` refining each layer refines the amalgam. -/
theorem amalgam_isTerminal (Fnum Fmod Fpadic FEC G : Subfunctor B)
    (hN : G ≤ Fnum) (hM : G ≤ Fmod) (hP : G ≤ Fpadic) (hE : G ≤ FEC) :
    G ≤ amalgam Fnum Fmod Fpadic FEC := by
  simp only [amalgam]
  exact le_inf (le_inf (le_inf hN hM) hP) hE

/-- **B-4 (projection natural transformations).** The amalgam projects onto each layer
as a genuine natural transformation `F ⟶ Fᵢ`. -/
def amalgam_proj_Fnum (Fnum Fmod Fpadic FEC : Subfunctor B) :
    (amalgam Fnum Fmod Fpadic FEC).toFunctor ⟶ Fnum.toFunctor :=
  Subfunctor.homOfLe (amalgam_le_Fnum Fnum Fmod Fpadic FEC)

def amalgam_proj_Fmod (Fnum Fmod Fpadic FEC : Subfunctor B) :
    (amalgam Fnum Fmod Fpadic FEC).toFunctor ⟶ Fmod.toFunctor :=
  Subfunctor.homOfLe (amalgam_le_Fmod Fnum Fmod Fpadic FEC)

def amalgam_proj_Fpadic (Fnum Fmod Fpadic FEC : Subfunctor B) :
    (amalgam Fnum Fmod Fpadic FEC).toFunctor ⟶ Fpadic.toFunctor :=
  Subfunctor.homOfLe (amalgam_le_Fpadic Fnum Fmod Fpadic FEC)

def amalgam_proj_FEC (Fnum Fmod Fpadic FEC : Subfunctor B) :
    (amalgam Fnum Fmod Fpadic FEC).toFunctor ⟶ FEC.toFunctor :=
  Subfunctor.homOfLe (amalgam_le_FEC Fnum Fmod Fpadic FEC)

/-- **B-5 (triple-overlap cocycle, CORRECTED).** From pairwise agreement on the
`(a,b)` and `(b,c)` overlaps, the two outer sections agree on the common chart `b`:
`b ∣ s₁ - s₃`.  ⚠ The naive `lcm(lcm a b)c ∣ s₁-s₃` is FALSE (take `a=2,b=1,c=3,
s₁=2,s₂=0,s₃=3`: both hypotheses hold but `6 ∤ -1`). -/
theorem triple_cocycle (a b c s₁ s₂ s₃ : ℤ)
    (h12 : lcm a b ∣ (s₁ - s₂)) (h23 : lcm b c ∣ (s₂ - s₃)) :
    b ∣ (s₁ - s₃) := by
  have hb12 : b ∣ (s₁ - s₂) := dvd_trans (dvd_lcm_right a b) h12
  have hb23 : b ∣ (s₂ - s₃) := dvd_trans (dvd_lcm_left b c) h23
  have hsplit : s₁ - s₃ = (s₁ - s₂) + (s₂ - s₃) := by ring
  rw [hsplit]; exact dvd_add hb12 hb23

/-- **B-6 (restriction is inclusion).** Over any open, the amalgam section set is the
intersection of the four layer section sets (so restriction is set inclusion). -/
theorem amalgam_restriction_is_inclusion (Fnum Fmod Fpadic FEC : Subfunctor B)
    {V : (Opens S)ᵒᵖ} :
    (amalgam Fnum Fmod Fpadic FEC).obj V =
      {x | x ∈ Fnum.obj V ∧ x ∈ Fmod.obj V ∧ x ∈ Fpadic.obj V ∧ x ∈ FEC.obj V} := by
  ext x
  rw [Set.mem_setOf_eq]
  exact mem_amalgam Fnum Fmod Fpadic FEC x

end Spt3Sheaf

/-! ============================================================================
    Category D — concrete decision layers (Spt3Cert).
============================================================================ -/

namespace Spt3Cert

/-- **D-1 (concrete modular layer).** Divisibility gate by a modulus `M`. -/
def Fmod_pred (M X : ℕ) : Prop := M ∣ X

/-- Multi-modulus version. -/
def Fmod_multi (moduli : List ℕ) (X : ℕ) : Prop := ∀ M ∈ moduli, M ∣ X

/-- **D-2 (concrete p-adic layer).** `p`-adic valuation gate `p^k ∣ X`. -/
def Fpadic_pred (p k X : ℕ) : Prop := p ^ k ∣ X

/-- Valuation-level form. -/
def Fpadic_valuation (p k X : ℕ) : Prop := k ≤ X.factorization p

/-- **D-3 (concrete certification).** `prime_iff_section` with a meaningful numeric
gate (`1 < X`), the divisor characterisation, and the Lucas layer. -/
theorem prime_iff_section_concrete (X : ℕ) :
    X.Prime ↔ (1 < X ∧ (∀ d, d ∣ X → d = 1 ∨ d = X) ∧ True ∧ LucasCert X) := by
  constructor
  · intro h
    exact ⟨h.one_lt, fun d hd => (Nat.Prime.eq_one_or_self_of_dvd h d hd), trivial,
      LucasCert_complete h⟩
  · rintro ⟨_, _, _, hL⟩
    exact LucasCert_sound hL

/-- **D-4 (layer independence: the EC layer is necessary).** Without the EC/Lucas layer,
the composite `4` would pass the three trivial gates; the EC layer correctly rejects it.
(The full four-way independence needs concrete non-trivial `Fnum, Fmod, Fpadic`.) -/
theorem layer_independence_EC :
    ∃ X : ℕ, ¬ X.Prime ∧ (True ∧ True ∧ True) ∧ ¬ LucasCert X := by
  refine ⟨4, by decide, ⟨trivial, trivial, trivial⟩, ?_⟩
  intro h
  exact (by decide : ¬ Nat.Prime 4) (LucasCert_sound h)

end Spt3Cert

/-! ============================================================================
    Category B-1 (sheaf descent) and C-2 (tensor isomorphism) — previously
    deferred, now formalized.
============================================================================ -/

namespace Spt3Sheaf

/-- **B-1 helper (binary meet of sheaves).** Inside an ambient sheaf `F`, the meet of
two sub-*sheaves* is again a sheaf.  (The constant presheaf `B` is not separated, so
the ambient-sheaf hypothesis `hF` is genuinely needed; it is the honest extra
assumption the descent argument requires.) -/
theorem inf_isSheaf {F : (Opens S)ᵒᵖ ⥤ Type} (hF : Presieve.IsSheaf siteJ F)
    (G₁ G₂ : Subfunctor F)
    (h₁ : Presieve.IsSheaf siteJ G₁.toFunctor)
    (h₂ : Presieve.IsSheaf siteJ G₂.toFunctor) :
    Presieve.IsSheaf siteJ (G₁ ⊓ G₂).toFunctor := by
  rw [(G₁ ⊓ G₂).isSheaf_iff hF]
  intro U s hs
  have le1 : (G₁ ⊓ G₂).sieveOfSection s ≤ G₁.sieveOfSection s := by
    intro V f hf; exact hf.1
  have le2 : (G₁ ⊓ G₂).sieveOfSection s ≤ G₂.sieveOfSection s := by
    intro V f hf; exact hf.2
  have m1 : s ∈ G₁.obj U :=
    (G₁.isSheaf_iff hF).mp h₁ U s (siteJ.superset_covering le1 hs)
  have m2 : s ∈ G₂.obj U :=
    (G₂.isSheaf_iff hF).mp h₂ U s (siteJ.superset_covering le2 hs)
  exact ⟨m1, m2⟩

/-- **B-1 (descent / sheaf condition for the amalgam).** If the ambient `B` is a sheaf
and each of the four layers is a sheaf, then the amalgam `F = Fnum ⊓ Fmod ⊓ Fpadic ⊓ FEC`
is a sheaf: a matching family of local sections glues uniquely. -/
theorem amalgam_isSheaf (hB : Presieve.IsSheaf siteJ B)
    (Fnum Fmod Fpadic FEC : Subfunctor B)
    (hn : Presieve.IsSheaf siteJ Fnum.toFunctor)
    (hm : Presieve.IsSheaf siteJ Fmod.toFunctor)
    (hp : Presieve.IsSheaf siteJ Fpadic.toFunctor)
    (he : Presieve.IsSheaf siteJ FEC.toFunctor) :
    Presieve.IsSheaf siteJ (amalgam Fnum Fmod Fpadic FEC).toFunctor :=
  inf_isSheaf hB _ _ (inf_isSheaf hB _ _ (inf_isSheaf hB _ _ hn hm) hp) he

end Spt3Sheaf

open scoped TensorProduct

namespace Spt3

/-- **C-2 core (pushout of quotient rings).** For ideals `I, J` of any commutative
ring `R`, `(R/I) ⊗_R (R/J) ≃+* R/(I ⊔ J)`.  This is the affine-scheme fiber-product
identity `Spec(R/I) ×_{Spec R} Spec(R/J) = Spec(R/(I+J))` at the ring level (§2.3(4)).
Stated over a general `R` to avoid the `ℤ`-algebra instance diamond; the paper's case
is `R = ℤ` (see `commonResidueFiber_tensorEquiv`). -/
noncomputable def quotTensorQuotEquiv {R : Type*} [CommRing R] (I J : Ideal R) :
    (R ⧸ I) ⊗[R] (R ⧸ J) ≃+* (R ⧸ (I ⊔ J)) := by
  have hmap : I.map (algebraMap R (R ⧸ J)) = I.map (Ideal.Quotient.mk J) := by
    rw [Ideal.Quotient.algebraMap_eq]
  exact ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor (R ⧸ J) I).symm.toRingEquiv).trans
    ((Ideal.quotEquivOfEq hmap).trans
      ((DoubleQuot.quotQuotEquivQuotSup J I).trans (Ideal.quotEquivOfEq (sup_comm ..))))

/-- The gcd identification of the pushout target over `ℤ` (no tensor, so no diamond):
`ℤ/((M) ⊔ (N)) ≃+* ZMod (gcd M N)`. -/
noncomputable def quotSupEquivZModGcd (M N : ℕ) :
    (ℤ ⧸ (Ideal.span {(M : ℤ)} ⊔ Ideal.span {(N : ℤ)})) ≃+* ZMod (Nat.gcd M N) := by
  have hsup : Ideal.span {(M : ℤ)} ⊔ Ideal.span {(N : ℤ)}
      = Ideal.span {((Nat.gcd M N : ℤ))} := by
    apply le_antisymm
    · rw [sup_le_iff]
      refine ⟨?_, ?_⟩
      · rw [Ideal.span_singleton_le_span_singleton]; exact_mod_cast Nat.gcd_dvd_left M N
      · rw [Ideal.span_singleton_le_span_singleton]; exact_mod_cast Nat.gcd_dvd_right M N
    · rw [Ideal.span_singleton_le_iff_mem, Nat.gcd_eq_gcd_ab]
      apply Ideal.add_mem
      · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      · exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  exact (Ideal.quotEquivOfEq hsup).trans (Int.quotientSpanEquivZMod (Nat.gcd M N : ℤ))

/-- **C-2 (common residue fiber).** Composing the pushout iso (at `R = ℤ`) with the gcd
identification: `(ℤ/(M)) ⊗_ℤ (ℤ/(N)) ≃+* ZMod (gcd M N)` — the scheme intersection
`Spec(ℤ/M) ×_{Spec ℤ} Spec(ℤ/N) = Spec(ℤ/gcd)`.  (The type is inferred from the
composition so that the tensor's ring instances are inherited from `quotTensorQuotEquiv`,
sidestepping the `ℤ`-algebra diamond that blocks writing `⊗[ℤ]` in a raw signature.) -/
noncomputable def commonResidueFiber_tensorEquiv (M N : ℕ) :=
  (quotTensorQuotEquiv (Ideal.span {(M : ℤ)}) (Ideal.span {(N : ℤ)})).trans
    (quotSupEquivZModGcd M N)

end Spt3

/-! ============================================================================
    Extended Checklist A (items provable in current Mathlib, previously listed
    as "미증명") + Checklist B-3 arithmetic core.
============================================================================ -/

namespace Spt3

/-- **A-1 helper (Π-kernel split).** The obstruction kernel on a finite product ring
splits as the product of the componentwise obstruction kernels. -/
def ker_mulLeft_pi {ι : Type*} (R : ι → Type*) [∀ i, Ring (R i)] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ∀ i, R i)).ker ≃+
      ∀ i, (AddMonoidHom.mulLeft (M : R i)).ker where
  toFun x i := ⟨x.1 i, congrFun x.2 i⟩
  invFun y := ⟨fun i => (y i).1, funext fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **A-1 (n-fold group-level Tor decomposition).** The obstruction group decomposes
as a genuine additive-group product over the prime factorization of `N`:
`ker(×M on ℤ/N) ≃+ Π_{q ∣ N} ker(×M on ℤ/q^{v_q N})`.  (Closes the §O gap: not just
the order, but the group, factors primewise.) -/
noncomputable def ker_mulLeft_pi_addEquiv {N : ℕ} (hN : N ≠ 0) (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+
      ∀ q : N.primeFactors, (AddMonoidHom.mulLeft (M : ZMod (q ^ N.factorization q))).ker :=
  (kerTransport (crt_pi_iso hN).toAddEquiv
      (AddMonoidHom.mulLeft (M : ZMod N))
      (AddMonoidHom.mulLeft (M : ∀ q : N.primeFactors, ZMod (q ^ N.factorization q)))
      (fun a => by
        show (crt_pi_iso hN) ((M : ZMod N) * a)
            = (M : ∀ q : N.primeFactors, ZMod (q ^ N.factorization q)) * (crt_pi_iso hN) a
        rw [map_mul, map_natCast])).trans (ker_mulLeft_pi _ M)

/-- **A-3 (annihilator of the Tor module = `(gcd)`).** The "correct" restoration of the
paper's support claim.  The obstruction module is `ℤ/gcd`; its `ℤ`-annihilator is exactly
`(gcd(M,N))`.  Since for a finite module `Supp M = Z(Ann M)` (`Module.support_eq_zeroLocus`),
this says the obstruction is supported precisely on `V(gcd(M,N))`. -/
theorem ann_tor_eq_span_gcd (M N : ℕ) :
    Module.annihilator ℤ (ℤ ⧸ Ideal.span {(Nat.gcd M N : ℤ)})
      = Ideal.span {(Nat.gcd M N : ℤ)} :=
  Ideal.annihilator_quotient

/-- The support form, packaged from `ann_tor_eq_span_gcd`: `Supp(ℤ/gcd) = V(gcd)`. -/
theorem supp_tor_eq_zeroLocus_gcd (M N : ℕ) :
    Module.support ℤ (ℤ ⧸ Ideal.span {(Nat.gcd M N : ℤ)})
      = PrimeSpectrum.zeroLocus (Ideal.span {(Nat.gcd M N : ℤ)} : Set ℤ) := by
  haveI : Module.Finite ℤ (ℤ ⧸ Ideal.span {(Nat.gcd M N : ℤ)}) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  rw [Module.support_eq_zeroLocus, ann_tor_eq_span_gcd]

/-- **A-5 (principal-open basis bookkeeping).** `D(fg) = D(f) ∩ D(g)`, `D(1) = S`,
`D(0) = ∅` on `Spec ℤ` — the multiplicative structure of the principal-open basis the
site is built from. -/
theorem basicOpen_mul_eq (f g : ℤ) :
    PrimeSpectrum.basicOpen (f * g) = PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g :=
  PrimeSpectrum.basicOpen_mul f g

theorem basicOpen_one_eq : PrimeSpectrum.basicOpen (1 : ℤ) = ⊤ := PrimeSpectrum.basicOpen_one

theorem basicOpen_zero_eq : PrimeSpectrum.basicOpen (0 : ℤ) = ⊥ := PrimeSpectrum.basicOpen_zero

/-- **A-8 (non-coprime general CRT, existence).** If `gcd(M,N) ∣ (a-b)` then the gluing
system `x ≡ a (mod M)`, `x ≡ b (mod N)` is solvable (Mathlib's CRT is coprime-only;
this is the Bézout construction for the general case). -/
theorem crt_noncoprime_exists (M N a b : ℤ) (h : (Int.gcd M N : ℤ) ∣ (a - b)) :
    ∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b) := by
  obtain ⟨k, hk⟩ := h
  have hbez : (Int.gcd M N : ℤ) = M * Int.gcdA M N + N * Int.gcdB M N := Int.gcd_eq_gcd_ab M N
  refine ⟨a - M * Int.gcdA M N * k, ⟨-(Int.gcdA M N * k), by ring⟩,
    ⟨Int.gcdB M N * k, ?_⟩⟩
  linear_combination hk + k * hbez

/-- **A-10 (univariate Hensel gate).** A simple residual root lifts to a unique `p`-adic
root: this is the gate Proposition 2 uses, promoted to a theorem via Mathlib's
`hensels_lemma`.  (`‖F(a)‖ < ‖F'(a)‖²` is the simple-root/non-degeneracy condition.) -/
theorem hensel_gate {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]} {a : ℤ_[p]}
    (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2) :
    ∃! z : ℤ_[p], F.aeval z = 0 ∧ ‖z - a‖ < ‖F.derivative.aeval a‖ := by
  obtain ⟨z, hz0, hzlt, _, huniq⟩ := hensels_lemma hnorm
  exact ⟨z, ⟨hz0, hzlt⟩, fun z' hz' => huniq z' hz'.1 hz'.2⟩

/-! ### Checklist B-3 (truncated p-adic log) — arithmetic core.

The truncated logarithm `L(u) = Σ_{1≤n≤m} (-1)^{n+1} u^n/n` has each term's `p`-adic
valuation `v_p(u^n/n) ≥ n·k - v_p(n)` for `u ∈ p^k ℤ_p`.  The key Nat fact making each
term survive (`≥ k`) is `v_p(n) < n` (Legendre + `log_p n < n`).  Formalizing the term
bound also exposes the paper's `p = 2` boundary defect: `v_2(2) = 1`, so at `(p,n)=(2,2)`
the bound `v_p(u^n/n) ≥ 2k` is only `≥ 2k-1` — the inequality `r ≥ 2k` holds for odd `p`. -/

/-- The per-term denominator valuation is strictly below `n` (Legendre's theorem via
`padicValNat ≤ log_p n < n`). -/
theorem padicValNat_lt_self (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    padicValNat p n < n :=
  lt_of_le_of_lt (padicValNat_le_nat_log n) (Nat.log_lt_self p hn)

/-- **B-3 `p = 2` boundary defect.** `v_2(2) = 1 > 0`, so the truncated-log term
`u^2/2` loses one unit of valuation: at `p = 2` the paper's `v_p(r) ≥ 2k` degrades to
`≥ 2k-1`.  (Another formalization-induced correction: the bound holds for odd `p`.) -/
theorem padic_log_defect_p_two : padicValNat 2 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat_self

end Spt3

namespace Spt3Cert

/-- **A-12 (indicator semantics).** A decision layer recovered as a `Bool`-valued
indicator section: `s(X) = true ⟺ X` lies in the layer.  Replaces bare set membership
with the paper's `s(X) = 1` semantics. -/
def layerIndicator (P : ℕ → Prop) [DecidablePred P] (X : ℕ) : Bool := decide (P X)

theorem layerIndicator_eq_true_iff (P : ℕ → Prop) [DecidablePred P] (X : ℕ) :
    layerIndicator P X = true ↔ P X := by
  simp [layerIndicator]

end Spt3Cert

/-! ============================================================================
    Previously-deferred "research-scale" items — verifiable cores.
    (A2 derived-Tor resolution, A7 four-layer independence, B2 cotangent-smoothness,
     B6 multivariate Hensel via formal étaleness.)
============================================================================ -/

namespace Spt3

/-! ### A-2 — the projective resolution behind the Tor proxy.

Mathlib has no `Tor` functor for modules, so `Tor₁(ℤ/M, ℤ/N)` cannot be *defined* as a
derived functor here.  What we CAN do — and what justifies using `ker(×M)` as the proxy —
is exhibit the length-1 free resolution `0 → ℤ --×M--> ℤ --mk--> ℤ/M → 0` and prove it is
a short exact sequence.  Tensoring it with `ℤ/N` and taking `H₁` is, by definition, `Tor₁`;
the `×M` map becomes `×M` on `ℤ/N`, whose kernel is the obstruction group. -/

/-- Left end of the resolution: `×M : ℤ → ℤ` is injective for `M ≠ 0`. -/
theorem resolution_mul_injective {M : ℤ} (hM : M ≠ 0) : Function.Injective (M * ·) :=
  mul_right_injective₀ hM

/-- Middle exactness: `ker(ℤ → ℤ/M) = image(×M) = (M)`. -/
theorem resolution_ker_eq_span (M : ℕ) :
    RingHom.ker (Int.castRingHom (ZMod M)) = Ideal.span {(M : ℤ)} :=
  ZMod.ker_intCastRingHom M

/-- Right end: `ℤ → ℤ/M` is surjective. -/
theorem resolution_mk_surjective (M : ℕ) :
    Function.Surjective (Int.castRingHom (ZMod M)) :=
  ZMod.intCast_surjective

/-! ### B-2 — cotangent / smoothness bridge.

The simplicial cotangent complex is absent, but Mathlib has the (naive) `H1Cotangent`.
The paper's Theorem-20 direction (b)⇒(c) "formally smooth ⇒ `H¹(L) = 0`" is a theorem. -/

/-- **B-2 (smooth ⇒ `H¹(L)` vanishes).** A formally smooth algebra has trivial first
cotangent cohomology — the `(b) ⇒ (c)` bridge of Theorem 20, now unconditional. -/
theorem smooth_imp_h1Cotangent_subsingleton {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FormallySmooth R A] :
    Subsingleton (Algebra.H1Cotangent R A) :=
  Algebra.FormallySmooth.subsingleton_h1Cotangent

/-! ### B-6 — multivariate Hensel via formal étaleness.

`FormallyEtale.comp_bijective`: for a formally étale `R`-algebra `A`, lifting `A`-points
along ANY square-zero extension `B ↠ B/I` is a bijection — existence + uniqueness of the
lift.  This is exactly the (multivariate, Jacobian-nondegenerate) Hensel statement. -/

/-- **B-6 (unique lift along square-zero extensions).** For a formally étale `A`, the
restriction `(A →ₐ B) → (A →ₐ B/I)` along a square-zero ideal `I` is bijective: every
mod-`I` solution lifts, uniquely. -/
theorem hensel_multivar_unique_lift {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  Algebra.FormallyEtale.comp_bijective (R := R) (A := A) (B := B) I hI

end Spt3

namespace Spt3Cert

/-! ### A-7 — concrete four decision layers and their independence (§2.3(6)).

Concrete predicates for the four gates, and witnesses that each gate strictly refines the
previous one (catches a composite the lighter gates admit) — the non-redundancy / minimality
of the four-layer profile.  (Logical 4-way independence in the "necessary for soundness"
sense cannot hold once one layer — here `LucasCert` — is already complete; the honest
content is the strictly-increasing discriminating power below.) -/

/-- Numeric size gate. -/
abbrev Fnum_layer (X : ℕ) : Prop := 1 < X
/-- Modular (parity) gate. -/
abbrev Fmod_layer (X : ℕ) : Prop := ¬ 2 ∣ X ∨ X = 2
/-- `p`-adic (mod 3) gate. -/
abbrev Fpadic_layer (X : ℕ) : Prop := ¬ 3 ∣ X ∨ X = 3
/-- EC/AKS completeness gate (here the complete Lucas certificate). -/
def FEC_layer (X : ℕ) : Prop := LucasCert X

/-- `Fnum` strictly refines nothing below it but already excludes `1`, which the numeric
gate is exactly there to catch (`1` is admitted by the mod gates). -/
theorem layer_indep_num : Fmod_layer 1 ∧ Fpadic_layer 1 ∧ ¬ Fnum_layer 1 :=
  ⟨Or.inl (by decide), Or.inl (by decide), by decide⟩

/-- `Fmod` catches the even composite `4`, which passes the numeric gate. -/
theorem layer_indep_mod : Fnum_layer 4 ∧ ¬ Fmod_layer 4 :=
  ⟨by decide, by decide⟩

/-- `Fpadic` catches the multiple of `3` composite `9`, which passes numeric + parity. -/
theorem layer_indep_padic : Fnum_layer 9 ∧ Fmod_layer 9 ∧ ¬ Fpadic_layer 9 :=
  ⟨by decide, Or.inl (by decide), by decide⟩

/-- `FEC` (Lucas) is the only gate catching the composite `25` (passes numeric, parity,
mod 3) — the completeness layer is genuinely needed. -/
theorem layer_indep_EC : Fnum_layer 25 ∧ Fmod_layer 25 ∧ Fpadic_layer 25 ∧ ¬ FEC_layer 25 :=
  ⟨by decide, Or.inl (by decide), Or.inl (by decide),
    fun h => (by decide : ¬ Nat.Prime 25) (LucasCert_sound h)⟩

end Spt3Cert

namespace Spt3

/-! ### A-11 — elliptic-curve discriminant gate (good reduction at `p ∤ Δ`).

The gate Proposition uses on `D(Δ)`: away from the discriminant the reduction mod `p` is
nonsingular.  `WeierstrassCurve.map_Δ` (Δ commutes with base change) + the Mathlib fact
`equation_iff_nonsingular_of_Δ_ne_zero` give it directly. -/

/-- **A-11 (good reduction / nonsingular gate).** If `p ∤ Δ(W)` for a Weierstrass curve
`W/ℤ`, then over `𝔽_p = ZMod p` every solution of the reduced Weierstrass equation is
nonsingular — the curve has good (smooth) reduction at `p`. -/
theorem ec_good_reduction {W : WeierstrassCurve ℤ} {p : ℕ} [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ W.Δ) (x y : ZMod p) :
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation x y ↔
      (W.map (Int.castRingHom (ZMod p))).toAffine.Nonsingular x y := by
  refine WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero ?_
  show (W.map (Int.castRingHom (ZMod p))).Δ ≠ 0
  rw [WeierstrassCurve.map_Δ]
  intro hcontra
  exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd W.Δ p).mp hcontra)

end Spt3

namespace Spt3Sheaf

/-! ### A-6 — `Spec ℤ` is irreducible (the geometric input that upgrades B-1).

`ℤ` is a domain, so `Spec ℤ` is irreducible: any two nonempty opens meet
(`IsPreirreducible Set.univ`).  This is exactly what makes a presheaf that is *constant on
nonempty opens* (with value a point on `∅`) a genuine sheaf — every compatible family over a
cover is a single constant — so over `Spec ℤ` the amalgam sheaf condition holds
unconditionally on such an ambient.  (The full re-pointed presheaf `B(∅) = {∗}` is the
remaining construction; the geometric core is below.) -/

/-- **A-6 core.** `Spec ℤ` is an irreducible space. -/
theorem specZ_irreducibleSpace : IrreducibleSpace (PrimeSpectrum ℤ) := inferInstance

/-- **A-6 core.** Any two nonempty opens of `Spec ℤ` intersect (preirreducibility) — the
gluing-triviality that discharges the sheaf condition for a constant-on-nonempty ambient. -/
theorem specZ_isPreirreducible : IsPreirreducible (Set.univ : Set (PrimeSpectrum ℤ)) :=
  PreirreducibleSpace.isPreirreducible_univ

end Spt3Sheaf

namespace Spt3

/-! ### A-9 — affine-scheme fiber product `Spec(ℤ/M) ×_{Spec ℤ} Spec(ℤ/N) = Spec(ℤ/gcd)`.

The scheme intersection of the two residue fibers, as the `Spec` of the C-2 pushout ring,
identified with `Spec(ZMod gcd)`.  `pullbackSpecIso` turns the pullback into `Spec` of the
tensor product; `Scheme.Spec.mapIso` of the C-2 ring isomorphism finishes. -/

open AlgebraicGeometry CategoryTheory.Limits in
/-- **A-9 (scheme fiber product).** The fibre product of `Spec(ℤ/M)` and `Spec(ℤ/N)` over
`Spec ℤ` is `Spec(ZMod gcd(M,N))` — the residue-fibre intersection at the scheme level. -/
noncomputable def spec_fiber_product (M N : ℕ) :=
  (pullbackSpecIso ℤ (ℤ ⧸ Ideal.span {(M : ℤ)}) (ℤ ⧸ Ideal.span {(N : ℤ)})).trans
    (Scheme.Spec.mapIso (commonResidueFiber_tensorEquiv M N).toCommRingCatIso.op).symm

/-! ### A-4 — localized thickness via `Localization.AtPrime`.

The arithmetic core of Proposition 7's localization claim: in `ℤ` localized at the prime
`(p)`, every integer coprime to `p` becomes a unit.  Hence the prime-to-`p` cofactor of
`lcm M (p^k)` is invertible there, leaving exactly `p^{max(v_p M, k)}` — the corrected
(`max`, not `min`) localized thickness.  (The `max` valuation identity is
`localized_intersection_valuation`; this supplies the localization step it relies on.) -/

/-- **A-4 (coprime ⇒ unit in the local ring `ℤ_(p)`).** If `p ∤ n`, then `n` is a unit in
any localization of `ℤ` at the prime ideal `(p)`. -/
theorem coprime_isUnit_atPrime {p : ℕ} {n : ℤ} (hn : ¬ (p : ℤ) ∣ n)
    (S : Type*) [CommRing S] [Algebra ℤ S]
    [(Ideal.span {(p : ℤ)}).IsPrime]
    [IsLocalization.AtPrime S (Ideal.span {(p : ℤ)})] :
    IsUnit (algebraMap ℤ S n) := by
  have hmem : n ∈ (Ideal.span {(p : ℤ)}).primeCompl :=
    fun hc => hn (Ideal.mem_span_singleton.mp hc)
  exact IsLocalization.map_units S (⟨n, hmem⟩ : (Ideal.span {(p : ℤ)}).primeCompl)

/-- The prime ideal `(p) ⊆ ℤ` is genuinely prime, so `Localization.AtPrime (p)` is the local
ring `ℤ_(p)` the statement above lives in. -/
instance span_p_isPrime {p : ℕ} [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

end Spt3

/-! ## Axiom audit for the checklist additions. -/
section ChecklistAxiomAudit
#print axioms Spt3.spec_fiber_product
#print axioms Spt3.coprime_isUnit_atPrime
#print axioms Spt3.ec_good_reduction
#print axioms Spt3Sheaf.specZ_isPreirreducible
#print axioms Spt3.resolution_ker_eq_span
#print axioms Spt3.smooth_imp_h1Cotangent_subsingleton
#print axioms Spt3.hensel_multivar_unique_lift
#print axioms Spt3Cert.layer_indep_EC
#print axioms Spt3Sheaf.amalgam_isSheaf
#print axioms Spt3.quotTensorQuotEquiv
#print axioms Spt3.quotSupEquivZModGcd
#print axioms Spt3.commonResidueFiber_tensorEquiv
#print axioms Spt3.ker_mulLeft_pi_addEquiv
#print axioms Spt3.supp_tor_eq_zeroLocus_gcd
#print axioms Spt3.basicOpen_mul_eq
#print axioms Spt3.crt_noncoprime_exists
#print axioms Spt3.hensel_gate
#print axioms Spt3.padicValNat_lt_self
#print axioms Spt3.padic_log_defect_p_two
#print axioms Spt3Cert.layerIndicator_eq_true_iff
#print axioms Spt3.ker_mulLeft_addEquiv_prod
#print axioms Spt3.card_ker_mulLeft_pi_prod
#print axioms Spt3.ker_mono_of_dvd
#print axioms Spt3.ker_mono_dvd_false
#print axioms Spt3.paper_zeroClass_false
#print axioms Spt3.IC_eq_zero_iff_coprime
#print axioms Spt3.log_eq_sum_factorization
#print axioms Spt3.IC_le_log_N
#print axioms Spt3.thickness_tor_vs_intersection
#print axioms Spt3.localized_intersection_valuation
#print axioms Spt3.kernel_intersection_zeroLocus
#print axioms Spt3.good_prime_no_support
#print axioms Spt3.ker_mulLeft_generator
#print axioms Spt3.stabilityBox
#print axioms Spt3.Tor_component_order
#print axioms Spt3.IC_primepower_sum
#print axioms Spt3.IC_one_right
#print axioms Spt3.IC_self
#print axioms Spt3.obstruction_tfae
#print axioms Spt3.crt_gluing_exists
#print axioms Spt3Sheaf.amalgam_section_unique
#print axioms Spt3Sheaf.amalgam_isTerminal
#print axioms Spt3Sheaf.amalgam_proj_FEC
#print axioms Spt3Sheaf.triple_cocycle
#print axioms Spt3Sheaf.amalgam_restriction_is_inclusion
#print axioms Spt3Cert.prime_iff_section_concrete
#print axioms Spt3Cert.layer_independence_EC
end ChecklistAxiomAudit

/-!
================================================================================
  Gap ledger and integration checklist

  This final namespace records the current audit requested for the unified spt3
  Lean file.  It deliberately contains data, not new mathematical assumptions:
  missing Mathlib infrastructure is not introduced as `axiom`, and paper-level
  claims that are only conditional remain marked as conditional or as corrected
  replacements.

  Reading convention:
    * `mathlibAbsent` means the requested object is not currently available as a
      direct Mathlib API in the form needed by the paper.
    * `mathlibPossible` means the path is plausible in Mathlib, but the present
      file either proves a proxy or records a future target.
    * `formalizedDifferent` means the file proves a corrected/weaker/conditional
      statement instead of the paper's literal statement.
    * `workaround` means the file gives a conservative formal substitute.
================================================================================
-/

namespace Spt3Checklist

inductive GapClass where
  | mathlibAbsent
  | mathlibPossible
  | formalizedDifferent
  | workaround
deriving Repr, DecidableEq

inductive ChecklistStatus where
  | proved
  | proxyProved
  | conditional
  | futureTarget
  | blockedByMathlib
  | correctedPaperClaim
  | deliberatelyDropped
deriving Repr, DecidableEq

structure ChecklistItem where
  code : String
  title : String
  gap : GapClass
  status : ChecklistStatus
  currentLeanAnchor : List String
  mathlibAnchor : List String
  integrationNote : String
  recommendedNextStep : String
deriving Repr

def A1_AKS_ECPP : ChecklistItem :=
  { code := "A1",
    title := "AKS / ECPP primality layer",
    gap := GapClass.mathlibAbsent,
    status := ChecklistStatus.blockedByMathlib,
    currentLeanAnchor :=
      ["Spt3Cert.LucasCert", "Spt3Cert.prime_iff_section",
       "Spt3Cert.AKSIsComplete", "Spt3Cert.prime_iff_section_of_complete"],
    mathlibAnchor := ["Mathlib.NumberTheory.LucasPrimality"],
    integrationNote :=
      "Mathlib has a Lucas-Pratt style complete certificate, but no AKS or ECPP formalization.  The file closes Theorem 18 with LucasCert and isolates future AKS/ECPP as AKSIsComplete.",
    recommendedNextStep :=
      "Keep LucasCert as the verified complete layer; replace FEC only after a genuine AKS/ECPP soundness and completeness theorem is available." }

def A2_padic_log_Baker : ChecklistItem :=
  { code := "A2",
    title := "p-adic logarithm Lipschitz bounds and Baker-Wustholz lower bounds",
    gap := GapClass.mathlibAbsent,
    status := ChecklistStatus.blockedByMathlib,
    currentLeanAnchor :=
      ["Spt3.padicValNat_lt_self", "Spt3.padic_log_defect_p_two",
       "Spt3.hensel_gate", "Spt3.hensel_multivar_unique_lift"],
    mathlibAnchor :=
      ["Mathlib.NumberTheory.Padics.Hensel",
       "Mathlib.NumberTheory.Padics.PadicVal.Basic"],
    integrationNote :=
      "The analytic p-adic log and Baker-Wustholz layer is not formalized here.  The file records the elementary valuation facts and Hensel-style gates that can support a finite/truncated replacement.",
    recommendedNextStep :=
      "Use truncated polynomial log bounds plus finite decidable checks for concrete windows; keep Baker-type global lower bounds as explicit hypotheses if needed." }

def A3_scheme_cotangent_motivic : ChecklistItem :=
  { code := "A3",
    title := "General scheme cotangent complex and motivic/etale detectors",
    gap := GapClass.mathlibAbsent,
    status := ChecklistStatus.deliberatelyDropped,
    currentLeanAnchor :=
      ["Spt3.smooth_imp_h1Cotangent_subsingleton",
       "Spt3.ec_good_reduction", "Spt3.spec_fiber_product"],
    mathlibAnchor :=
      ["Mathlib.RingTheory.Smooth.Basic",
       "Mathlib.RingTheory.Etale.Basic",
       "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass"],
    integrationNote :=
      "The paper's general detector language is not needed for the arithmetic certification core.  The unified file works affinely through rings, H1Cotangent, formal smoothness/etaleness, and elliptic discriminant good reduction.",
    recommendedNextStep :=
      "Keep the affine algebraic replacement unless the paper later supplies a precise scheme-level theorem statement." }

def A4_computable_Tor_API : ChecklistItem :=
  { code := "A4",
    title := "Computation-friendly Tor API for Z/gcd",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.proxyProved,
    currentLeanAnchor :=
      ["Spt3.card_ker_mulLeft", "Spt3.ker_mulLeft_addEquiv",
       "Spt3.resolution_mul_injective", "Spt3.resolution_ker_eq_span",
       "Spt3.resolution_mk_surjective"],
    mathlibAnchor :=
      ["Mathlib.CategoryTheory.Monoidal.Tor",
       "CategoryTheory.Functor.leftDerived"],
    integrationNote :=
      "The file proves the group-level kernel proxy and the length-one resolution behind Tor_1.  It does not yet identify Mathlib's Tor functor with ZMod (gcd M N).",
    recommendedNextStep :=
      "Build the derived-functor statement from ModuleCat Z, the short exact resolution, and the long exact homology sequence." }

def B1_true_Tor_identification : ChecklistItem :=
  { code := "B1",
    title := "True Tor_1(Z/M,Z/N) is Z/gcd",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.futureTarget,
    currentLeanAnchor :=
      ["Spt3.ker_mulLeft_addEquiv", "Spt3.card_ker_mulLeft",
       "Spt3.commonResidueFiber_tensorEquiv"],
    mathlibAnchor :=
      ["Mathlib.CategoryTheory.Monoidal.Tor",
       "ModuleCat", "Functor.leftDerived"],
    integrationNote :=
      "The mathematical content is already present as ker(mulLeft M on ZMod N).  The literal Tor functor statement remains a future API-heavy upgrade.",
    recommendedNextStep :=
      "Transport the proxy isomorphism through the projective resolution and expose a named Tor_1 add-equivalence." }

def B2_cotangent_reverse_bridge : ChecklistItem :=
  { code := "B2",
    title := "Cotangent reverse bridge H1(L)=0 implies formal smoothness",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.futureTarget,
    currentLeanAnchor :=
      ["Spt3.smooth_imp_h1Cotangent_subsingleton",
       "Spt3.derived_equalizer_tfae"],
    mathlibAnchor :=
      ["RingTheory/Smooth/Fiber.lean",
       "Algebra.Extension.equivH1CotangentOfFormallySmooth",
       "FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField"],
    integrationNote :=
      "The current file proves the forward direction and keeps Theorem 20's full equivalence conditional.  Mathlib has algebraic fiber/residue-field tools that may prove the reverse in suitable hypotheses.",
    recommendedNextStep :=
      "Specialize the Smooth/Fiber API to the affine residue-field situation used by the paper and replace the hypothesis in derived_equalizer_tfae." }

def B3_localized_intersection_ideal : ChecklistItem :=
  { code := "B3",
    title := "Localized ideal equality for (M) cap (p^k) in Z_(p)",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.proxyProved,
    currentLeanAnchor :=
      ["Spt3.localized_intersection_valuation",
       "Spt3.coprime_isUnit_atPrime", "Spt3.span_p_isPrime"],
    mathlibAnchor :=
      ["Mathlib.RingTheory.Localization.AtPrime.Basic",
       "Ideal.span_singleton_prime"],
    integrationNote :=
      "The valuation identity and the unit-in-localization step are present.  The literal localized ideal equality should state max-thickness, not the paper's min-thickness.",
    recommendedNextStep :=
      "Package the valuation result as an equality of ideals in Localization.AtPrime at (p)." }

def B4_unconditional_sheaf_upgrade : ChecklistItem :=
  { code := "B4",
    title := "Unconditional sheaf upgrade for repointed constant-on-nonempty ambient",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.futureTarget,
    currentLeanAnchor :=
      ["Spt3Sheaf.amalgam_isSheaf", "Spt3Sheaf.specZ_isPreirreducible",
       "Spt3Sheaf.specZ_irreducibleSpace"],
    mathlibAnchor :=
      ["Mathlib.CategoryTheory.Sites.Subsheaf",
       "Mathlib.RingTheory.Spectrum.Prime.Topology"],
    integrationNote :=
      "The file proves meet-of-sheaves descent conditionally and proves irreducibility of Spec Z.  The repointed ambient B(empty) = unit is recorded as the clean unconditional target.",
    recommendedNextStep :=
      "Define the repointed constant presheaf and prove its sheaf condition from preirreducibility." }

def B5_concrete_layers : ChecklistItem :=
  { code := "B5",
    title := "Concrete layer predicates instead of abstract subfunctors",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.proved,
    currentLeanAnchor :=
      ["Spt3Cert.Fnum_layer", "Spt3Cert.Fmod_pred",
       "Spt3Cert.Fpadic_pred", "Spt3Cert.Fpadic_valuation",
       "Spt3Cert.FEC_layer", "Spt3Cert.prime_iff_section_concrete"],
    mathlibAnchor := [],
    integrationNote :=
      "The concrete Nat -> Prop layer predicates are present.  The sheaf-level subfunctor packaging is still abstract where it belongs to the site layer.",
    recommendedNextStep :=
      "Connect the concrete predicates to Subfunctor objects only when a concrete base site and restriction semantics are fixed." }

def B6_Tor_naturality : ChecklistItem :=
  { code := "B6",
    title := "Tor naturality as a natural transformation",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.futureTarget,
    currentLeanAnchor :=
      ["Spt3.mulLeft_mul_comp", "Spt3.kerTransport",
       "Spt3.ker_crt_transport"],
    mathlibAnchor :=
      ["Mathlib.CategoryTheory.Monoidal.Tor"],
    integrationNote :=
      "Current naturality is the kernel-level shadow: multiplication maps compose correctly and transports respect kernels.  True naturality follows after B1.",
    recommendedNextStep :=
      "After defining the true Tor_1 equivalence, prove naturality by uniqueness of derived-functor connecting morphisms or by resolution-level chain maps." }

def B7_true_Tor_direct_sum : ChecklistItem :=
  { code := "B7",
    title := "True Tor n-fold direct-sum decomposition",
    gap := GapClass.mathlibPossible,
    status := ChecklistStatus.futureTarget,
    currentLeanAnchor :=
      ["Spt3.ker_mulLeft_pi_addEquiv",
       "Spt3.ker_mulLeft_addEquiv_prod",
       "Spt3.card_ker_mulLeft_pi_prod"],
    mathlibAnchor :=
      ["Mathlib.CategoryTheory.Monoidal.Tor"],
    integrationNote :=
      "The finite product/group-level proxy decomposition is proved.  The literal Tor direct-sum statement is downstream of B1 and B6.",
    recommendedNextStep :=
      "Transport the existing pi/AddEquiv decomposition across the true Tor_1 identification." }

def B8_layer_independence_honesty : ChecklistItem :=
  { code := "B8",
    title := "Honest replacement for four-layer logical independence",
    gap := GapClass.formalizedDifferent,
    status := ChecklistStatus.correctedPaperClaim,
    currentLeanAnchor :=
      ["Spt3Cert.layer_indep_num", "Spt3Cert.layer_indep_mod",
       "Spt3Cert.layer_indep_padic", "Spt3Cert.layer_indep_EC",
       "Spt3Cert.layer_independence_EC"],
    mathlibAnchor := [],
    integrationNote :=
      "Once one layer is complete, logical necessity of every other layer for soundness is impossible.  The file proves strict discriminating-power witnesses instead.",
    recommendedNextStep :=
      "Use the strict-refinement witnesses as the formal statement and avoid claiming logical independence of soundness." }

def C1_theorem18_scope : ChecklistItem :=
  { code := "C1",
    title := "Theorem 18 prime iff certificate",
    gap := GapClass.formalizedDifferent,
    status := ChecklistStatus.conditional,
    currentLeanAnchor :=
      ["Spt3.certification_iff_of_complete",
       "Spt3Cert.prime_iff_section", "Spt3Cert.prime_iff_section_concrete"],
    mathlibAnchor := ["Mathlib.NumberTheory.LucasPrimality"],
    integrationNote :=
      "The paper's EC/AKS completeness is not proved.  The unified file gives a conditional closure and a LucasCert concrete closure.",
    recommendedNextStep :=
      "State any EC/AKS variant through AKSIsComplete until the actual algorithm is formalized." }

def C2_theorem20_category_error : ChecklistItem :=
  { code := "C2",
    title := "Theorem 20 arithmetic Tor versus geometric cotangent bridge",
    gap := GapClass.formalizedDifferent,
    status := ChecklistStatus.correctedPaperClaim,
    currentLeanAnchor :=
      ["Spt3.derived_equalizer_tfae",
       "Spt3.obstruction_tfae",
       "Spt3.smooth_imp_h1Cotangent_subsingleton"],
    mathlibAnchor := ["Mathlib.RingTheory.Smooth.Basic"],
    integrationNote :=
      "The paper identifies arithmetic Tor obstruction and geometric cotangent smoothness by name only.  The file exposes the required bridge hypotheses instead of silently conflating them.",
    recommendedNextStep :=
      "Keep the Hder/Hgate assumptions explicit unless a concrete theorem relates these exact objects." }

def W1_Lucas_workaround : ChecklistItem :=
  { code := "W1",
    title := "AKS/ECPP workaround by Lucas-Pratt certification",
    gap := GapClass.workaround,
    status := ChecklistStatus.proved,
    currentLeanAnchor :=
      ["Spt3Cert.LucasCert_sound", "Spt3Cert.LucasCert_complete",
       "Spt3Cert.prime_iff_section"],
    mathlibAnchor := ["Mathlib.NumberTheory.LucasPrimality"],
    integrationNote :=
      "This is the recommended complete primality layer presently available in Mathlib.",
    recommendedNextStep :=
      "Use LucasCert for fully checked prime iff certificate statements." }

def W2_truncated_padic_workaround : ChecklistItem :=
  { code := "W2",
    title := "Truncated p-adic log plus finite checks",
    gap := GapClass.workaround,
    status := ChecklistStatus.futureTarget,
    currentLeanAnchor :=
      ["Spt3.padicValNat_lt_self", "Spt3.hensel_gate"],
    mathlibAnchor :=
      ["Mathlib.NumberTheory.Padics.PadicVal.Basic",
       "Mathlib.NumberTheory.Padics.Hensel"],
    integrationNote :=
      "For finite modulus gates, convergence of the analytic log can often be replaced by polynomial truncation and valuation inequalities.",
    recommendedNextStep :=
      "Formalize a finite polynomial log truncation with termwise valuation bounds." }

def W3_affine_cotangent_workaround : ChecklistItem :=
  { code := "W3",
    title := "Affine algebraic replacement for scheme cotangent detectors",
    gap := GapClass.workaround,
    status := ChecklistStatus.proved,
    currentLeanAnchor :=
      ["Spt3.smooth_imp_h1Cotangent_subsingleton",
       "Spt3.hensel_multivar_unique_lift", "Spt3.ec_good_reduction"],
    mathlibAnchor :=
      ["Mathlib.RingTheory.Smooth.Basic",
       "Mathlib.RingTheory.Etale.Basic"],
    integrationNote :=
      "The file uses ring-level formal smoothness, formal etaleness, H1Cotangent, and elliptic discriminants, avoiding the unavailable general simplicial scheme cotangent complex.",
    recommendedNextStep :=
      "Do not introduce motivic/etale detector names unless they carry exact formal statements." }

def W4_kernel_Tor_workaround : ChecklistItem :=
  { code := "W4",
    title := "Kernel of multiplication as Tor_1 proxy",
    gap := GapClass.workaround,
    status := ChecklistStatus.proxyProved,
    currentLeanAnchor :=
      ["Spt3.card_ker_mulLeft", "Spt3.ker_mulLeft_addEquiv",
       "Spt3.resolution_mul_injective", "Spt3.resolution_ker_eq_span",
       "Spt3.resolution_mk_surjective"],
    mathlibAnchor := ["Mathlib.Data.ZMod.Basic"],
    integrationNote :=
      "The proxy is mathematically justified by the displayed free resolution and loses no group-level content for the results currently stated.",
    recommendedNextStep :=
      "Preserve the proxy for computations; add true Tor only when a downstream theorem requires the categorical API." }

def all : List ChecklistItem :=
  [A1_AKS_ECPP,
   A2_padic_log_Baker,
   A3_scheme_cotangent_motivic,
   A4_computable_Tor_API,
   B1_true_Tor_identification,
   B2_cotangent_reverse_bridge,
   B3_localized_intersection_ideal,
   B4_unconditional_sheaf_upgrade,
   B5_concrete_layers,
   B6_Tor_naturality,
   B7_true_Tor_direct_sum,
   B8_layer_independence_honesty,
   C1_theorem18_scope,
   C2_theorem20_category_error,
   W1_Lucas_workaround,
   W2_truncated_padic_workaround,
   W3_affine_cotangent_workaround,
   W4_kernel_Tor_workaround]

def currentProvedOrProxy : List ChecklistItem :=
  all.filter (fun item =>
    decide (item.status = ChecklistStatus.proved) ||
    decide (item.status = ChecklistStatus.proxyProved) ||
    decide (item.status = ChecklistStatus.correctedPaperClaim))

def futureTargets : List ChecklistItem :=
  all.filter (fun item =>
    decide (item.status = ChecklistStatus.futureTarget) ||
    decide (item.status = ChecklistStatus.blockedByMathlib))

def conditionalClaims : List ChecklistItem :=
  all.filter (fun item => decide (item.status = ChecklistStatus.conditional))

/-! ## Machine-checked proof layer for the checklist

The following declarations turn the ledger above into proof-carrying entries.
Items that are already formalized are connected directly to the corresponding
theorems in `Spt3`, `Spt3Sheaf`, or `Spt3Cert`.  Items that are intentionally not
claimed as theorems are proved to have the appropriate checklist status instead
of being smuggled in as assumptions.
-/

theorem checklist_total_items : all.length = 18 := rfl

theorem checklist_current_proved_or_proxy_count :
    currentProvedOrProxy.length = 8 := rfl

theorem checklist_future_target_count :
    futureTargets.length = 8 := rfl

theorem checklist_conditional_count :
    conditionalClaims.length = 1 := rfl

theorem A1_is_blocked_by_missing_AKS_ECPP :
    A1_AKS_ECPP.status = ChecklistStatus.blockedByMathlib := rfl

theorem A2_is_blocked_by_missing_padic_log_and_Baker :
    A2_padic_log_Baker.status = ChecklistStatus.blockedByMathlib := rfl

theorem A3_is_deliberately_dropped_detector_layer :
    A3_scheme_cotangent_motivic.status = ChecklistStatus.deliberatelyDropped := rfl

theorem B1_true_Tor_is_future_target :
    B1_true_Tor_identification.status = ChecklistStatus.futureTarget := rfl

theorem B2_reverse_cotangent_bridge_is_future_target :
    B2_cotangent_reverse_bridge.status = ChecklistStatus.futureTarget := rfl

theorem B6_true_Tor_naturality_is_future_target :
    B6_Tor_naturality.status = ChecklistStatus.futureTarget := rfl

theorem B7_true_Tor_direct_sum_is_future_target :
    B7_true_Tor_direct_sum.status = ChecklistStatus.futureTarget := rfl

/-- A1/W1: the available complete primality layer is Lucas-Pratt, not AKS/ECPP. -/
theorem A1_Lucas_complete_layer (X : ℕ) :
    X.Prime ↔ (True ∧ True ∧ True ∧ Spt3Cert.LucasCert X) :=
  Spt3Cert.prime_iff_section X

/-- W1 soundness: a Lucas certificate proves primality. -/
theorem W1_Lucas_sound {X : ℕ} (h : Spt3Cert.LucasCert X) : X.Prime :=
  Spt3Cert.LucasCert_sound h

/-- W1 completeness: every prime has a Lucas certificate. -/
theorem W1_Lucas_complete {X : ℕ} (h : X.Prime) : Spt3Cert.LucasCert X :=
  Spt3Cert.LucasCert_complete h

/-- A4/B1/W4: the kernel proxy has exactly the expected Tor_1 cardinality. -/
theorem A4_kernel_proxy_cardinality (N : ℕ) [NeZero N] (M : ℕ) :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker = Nat.gcd N M :=
  Spt3.card_ker_mulLeft N M

/-- B1/W4: the proxy is not merely equicardinal; it is additively isomorphic to
`ZMod (gcd N M)`. -/
noncomputable def B1_kernel_proxy_addEquiv (N : ℕ) [NeZero N] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod (Nat.gcd N M) :=
  Spt3.ker_mulLeft_addEquiv N M

/-- A4/W4: the free length-one resolution facts behind the proxy. -/
theorem A4_resolution_mul_injective {M : ℤ} (hM : M ≠ 0) :
    Function.Injective (M * ·) :=
  Spt3.resolution_mul_injective hM

theorem A4_resolution_ker_eq_span (M : ℕ) :
    RingHom.ker (Int.castRingHom (ZMod M)) = Ideal.span {(M : ℤ)} :=
  Spt3.resolution_ker_eq_span M

theorem A4_resolution_mk_surjective (M : ℕ) :
    Function.Surjective (Int.castRingHom (ZMod M)) :=
  Spt3.resolution_mk_surjective M

/-- B2/W3: the already-formalized cotangent direction, formal smoothness implies
vanishing first cotangent cohomology. -/
theorem B2_formallySmooth_h1Cotangent_subsingleton
    {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FormallySmooth R A] :
    Subsingleton (Algebra.H1Cotangent R A) :=
  Spt3.smooth_imp_h1Cotangent_subsingleton

/-- B3: the localized-intersection arithmetic content is the corrected max-valuation
statement, not the paper's min-valuation statement. -/
theorem B3_localized_intersection_max_valuation
    {M : ℕ} (k : ℕ) (hM : M ≠ 0) {p : ℕ} (hp : p.Prime) :
    (Nat.lcm M (p ^ k)).factorization p = max (M.factorization p) k :=
  Spt3.localized_intersection_valuation k hM hp

/-- B3: the localization unit step used to pass from valuation to local ideal
language. -/
theorem B3_coprime_isUnit_atPrime {p : ℤ} {n : ℤ} (hn : ¬ (p ∣ n))
    (S : Type*) [CommRing S] [Algebra ℤ S]
    [(Ideal.span {(p : ℤ)}).IsPrime]
    [IsLocalization.AtPrime S (Ideal.span {(p : ℤ)})] :
    IsUnit (algebraMap ℤ S n) :=
  Spt3.coprime_isUnit_atPrime hn S

/-- B4: the conditional sheaf upgrade already proved in the sheaf section. -/
theorem B4_amalgam_isSheaf_conditional
    (hB : Presieve.IsSheaf Spt3Sheaf.siteJ Spt3Sheaf.B)
    (Fnum Fmod Fpadic FEC : Subfunctor Spt3Sheaf.B)
    (hn : Presieve.IsSheaf Spt3Sheaf.siteJ Fnum.toFunctor)
    (hm : Presieve.IsSheaf Spt3Sheaf.siteJ Fmod.toFunctor)
    (hp : Presieve.IsSheaf Spt3Sheaf.siteJ Fpadic.toFunctor)
    (he : Presieve.IsSheaf Spt3Sheaf.siteJ FEC.toFunctor) :
    Presieve.IsSheaf Spt3Sheaf.siteJ
      (Spt3Sheaf.amalgam Fnum Fmod Fpadic FEC).toFunctor :=
  Spt3Sheaf.amalgam_isSheaf hB Fnum Fmod Fpadic FEC hn hm hp he

/-- B4 geometric core: `Spec ℤ` is preirreducible, the key input for the future
unconditional repointed-constant sheaf proof. -/
theorem B4_specZ_preirreducible :
    IsPreirreducible (Set.univ : Set (PrimeSpectrum ℤ)) :=
  Spt3Sheaf.specZ_isPreirreducible

/-- B5/C1: the concrete Lucas-backed certificate theorem. -/
theorem B5_concrete_prime_iff_section (X : ℕ) :
    X.Prime ↔
      (1 < X ∧ (∀ d, d ∣ X → d = 1 ∨ d = X) ∧ True ∧ Spt3Cert.LucasCert X) :=
  Spt3Cert.prime_iff_section_concrete X

/-- B6: the naturality shadow currently available without the true Tor functor. -/
theorem B6_mulLeft_composition_shadow (N : ℕ) [NeZero N] (M₁ M₂ : ℕ) :
    AddMonoidHom.mulLeft ((M₁ : ZMod N) * (M₂ : ZMod N))
      =
    (AddMonoidHom.mulLeft (M₁ : ZMod N)).comp
      (AddMonoidHom.mulLeft (M₂ : ZMod N)) :=
  Spt3.mulLeft_mul_comp N M₁ M₂

/-- B7: the n-fold direct-sum item is presently proved at the finite-product proxy
level over the prime-factor decomposition of `N`. -/
noncomputable def B7_kernel_pi_decomposition
    {N : ℕ} (hN : N ≠ 0) (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker
      ≃+
    ∀ q : N.primeFactors,
      (AddMonoidHom.mulLeft (M : ZMod (q ^ N.factorization q))).ker :=
  Spt3.ker_mulLeft_pi_addEquiv hN M

/-- B8: the honest replacement for logical independence is strict discriminating
power of the layers, witnessed concretely. -/
theorem B8_layer_independence_EC_witness :
    Spt3Cert.Fnum_layer 25 ∧
    Spt3Cert.Fmod_layer 25 ∧
    Spt3Cert.Fpadic_layer 25 ∧
    ¬ Spt3Cert.FEC_layer 25 :=
  Spt3Cert.layer_indep_EC

theorem B8_layer_independence_numeric_witness :
    Spt3Cert.Fmod_layer 1 ∧
    Spt3Cert.Fpadic_layer 1 ∧
    ¬ Spt3Cert.Fnum_layer 1 :=
  Spt3Cert.layer_indep_num

theorem B8_layer_independence_modular_witness :
    Spt3Cert.Fnum_layer 4 ∧ ¬ Spt3Cert.Fmod_layer 4 :=
  Spt3Cert.layer_indep_mod

theorem B8_layer_independence_padic_witness :
    Spt3Cert.Fnum_layer 9 ∧
    Spt3Cert.Fmod_layer 9 ∧
    ¬ Spt3Cert.Fpadic_layer 9 :=
  Spt3Cert.layer_indep_padic

/-- C1: Theorem 18 remains valid for any explicitly sound and complete final layer. -/
theorem C1_certification_iff_of_complete
    (Fnum Fmod Fpadic FEC : ℕ → Prop) (X : ℕ)
    (Hsound : FEC X → X.Prime)
    (Hcomplete : X.Prime → Fnum X ∧ Fmod X ∧ Fpadic X ∧ FEC X) :
    X.Prime ↔ (Fnum X ∧ Fmod X ∧ Fpadic X ∧ FEC X) :=
  Spt3.certification_iff_of_complete Fnum Fmod Fpadic FEC X Hsound Hcomplete

/-- C2: Theorem 20 is retained as an explicitly conditional equivalence, making the
bridge hypotheses visible. -/
theorem C2_derived_equalizer_conditional
    (smooth : Prop) (der M pk : ℕ)
    (Hder : der = 0 ↔ smooth)
    (Hgate : smooth ↔ Nat.gcd M pk = 1) :
    [Nat.gcd M pk = 1, smooth, der = 0].TFAE :=
  Spt3.derived_equalizer_tfae smooth der M pk Hder Hgate

/-- W2: the finite p-adic replacement starts from the elementary valuation bound. -/
theorem W2_padicValNat_lt_self
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    padicValNat p n < n :=
  Spt3.padicValNat_lt_self p n hn

/-- W3: affine formal etaleness gives the Hensel-style unique lifting statement. -/
theorem W3_hensel_multivar_unique_lift
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  Spt3.hensel_multivar_unique_lift I hI

section ChecklistProofAudit
#print axioms A1_Lucas_complete_layer
#print axioms A4_kernel_proxy_cardinality
#print axioms B1_kernel_proxy_addEquiv
#print axioms B2_formallySmooth_h1Cotangent_subsingleton
#print axioms B3_localized_intersection_max_valuation
#print axioms B4_amalgam_isSheaf_conditional
#print axioms B5_concrete_prime_iff_section
#print axioms B6_mulLeft_composition_shadow
#print axioms B7_kernel_pi_decomposition
#print axioms B8_layer_independence_EC_witness
#print axioms C1_certification_iff_of_complete
#print axioms C2_derived_equalizer_conditional
#print axioms W2_padicValNat_lt_self
#print axioms W3_hensel_multivar_unique_lift
end ChecklistProofAudit

end Spt3Checklist
