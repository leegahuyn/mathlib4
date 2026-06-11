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
