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
import Mathlib.Algebra.Exact
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian

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
    rw [not_or] at hc
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
    rw [← Nat.support_factorization, ← Finsupp.prod, Nat.prod_factorization_pow_eq_self hN]
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
theorem IC_primepower_sum {M N : ℕ} (_hN : N ≠ 0) :
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
theorem B3_coprime_isUnit_atPrime {p : ℕ} {n : ℤ} (hn : ¬ ((p : ℤ) ∣ n))
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


/-! ============================================================================
    Category G — closing genuinely Mathlib-provable gaps (NEW).

    Added after a full kernel recompile of the unified file.  These items were
    NOT present in the three source fragments and are proved here from current
    Mathlib, sorry-free and axiom-free (audited at the end):

      • G-1  the paper's CENTRAL CRT equalizer biconditional
             `(∃x, x≡a [M] ∧ x≡b [N]) ↔ gcd(M,N) ∣ (a-b)`  (pages 2 & 36, §5.4 P1).
             The file previously had only the `(⇐)` existence half
             (`crt_noncoprime_exists`); G-1 supplies the missing `(⇒)` direction
             and packages the full equalizer-compatibility iff.
      • G-2  `gcd(q^{v_q N}, M) = q^{min(v_q M, v_q N)}` — the per-prime identity.
      • G-3  **Theorem 14 / Remark 19 as a genuine GROUP isomorphism.**  Previously
             the n-fold split was only `Π_q ker(...)` plus an order formula; G-3
             upgrades it to the literal target of the paper,
             `ker(×M on ℤ/N) ≃+ Π_{q∣N} ℤ/q^{min(v_q M, v_q N)}`, i.e. the proxy
             realisation of `Tor₁(ℤ/M,ℤ/N) ≅ ⊕_{q∣N} ℤ/q^{min}`.
      • G-4/G-5  Worked Examples B (M=7²·3, N=7⁴) and C (coprime) of §3.6/§4.4.5,
             at the group level and as symbolic `IC` values.
      • G-6  sheaf-level "no bad primes": the amalgam of full layers is full
             (`Γ(U,F)=Γ(U,B)`), the §5.4 normalized-profile statement.
============================================================================ -/

namespace Spt3

/-- **G-1 (CRT equalizer compatibility, the paper's central overlap criterion).**
`∃ x, x ≡ a (mod M) ∧ x ≡ b (mod N)` holds iff `gcd(M,N) ∣ (a-b)`.  This is the
exact equalizer/Čech-gluing biconditional asserted on p. 2 and proved in §5.4 P1;
the `(⇐)` half is `crt_noncoprime_exists`, and here we add the `(⇒)` half. -/
theorem crt_equalizer_compat_iff (M N a b : ℤ) :
    (∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b)) ↔ (Int.gcd M N : ℤ) ∣ (a - b) := by
  constructor
  · rintro ⟨x, hxa, hxb⟩
    have hgM : (Int.gcd M N : ℤ) ∣ (x - a) := dvd_trans (Int.gcd_dvd_left ..) hxa
    have hgN : (Int.gcd M N : ℤ) ∣ (x - b) := dvd_trans (Int.gcd_dvd_right ..) hxb
    have hsub : a - b = (x - b) - (x - a) := by ring
    rw [hsub]; exact dvd_sub hgN hgM
  · exact crt_noncoprime_exists M N a b

/-- **G-2.** The per-prime obstruction order: `gcd(q^{v_q N}, M) = q^{min(v_q M, v_q N)}`.
(The arithmetic core also used inside `Tor_component_order`.) -/
theorem gcd_primepow_eq {M N : ℕ} (hM : M ≠ 0) {q : ℕ} (hq : q ∈ N.primeFactors) :
    Nat.gcd (q ^ N.factorization q) M
      = q ^ min (M.factorization q) (N.factorization q) := by
  have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
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
    rw [hq0, hr0]; exact min_eq_left (Nat.zero_le _)

/-- **G-3 (Theorem 14 / Remark 19 as a genuine GROUP isomorphism).**  The derived
obstruction decomposes primewise *as an additive group* directly onto the paper's
target cyclic factors:
`ker(×M on ℤ/N) ≃+ Π_{q∣N} ℤ/q^{min(v_q M, v_q N)}`.
This is the proxy realisation of `Tor₁(ℤ/M, ℤ/N) ≅ ⊕_{q∣N} ℤ/q^{min}` at the group
level — strictly stronger than the previous `Π_q ker` decomposition
(`ker_mulLeft_pi_addEquiv`) plus the order formula (`card_ker_mulLeft_pi_prod`),
because each factor is now identified with the literal group `ℤ/q^{min}`. -/
noncomputable def tor_primewise_addEquiv {N : ℕ} (hN : N ≠ 0) (M : ℕ) (hM : M ≠ 0) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+
      ∀ q : N.primeFactors,
        ZMod ((q : ℕ) ^ min (M.factorization (q : ℕ)) (N.factorization (q : ℕ))) := by
  refine (ker_mulLeft_pi_addEquiv hN M).trans (AddEquiv.piCongrRight (fun q => ?_))
  obtain ⟨q, hq⟩ := q
  have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
  haveI : NeZero (q ^ N.factorization q) := ⟨pow_ne_zero _ hqp.pos.ne'⟩
  exact gcd_primepow_eq hM hq ▸ ker_mulLeft_addEquiv (q ^ N.factorization q) M

/-! ### G-4 / G-5 — Worked Examples B and C (§3.6 / §4.4.5). -/
section WorkedExamplesBC

/-- **Example B (single prime power, §3.6).** `M = 7²·3 = 147`, `N = 7⁴ = 2401`;
`gcd = 7² = 49`, so `Tor ≅ ℤ/49` as a GROUP and `|Tor| = 7²`. -/
example : Nonempty ((AddMonoidHom.mulLeft ((147 : ℕ) : ZMod 2401)).ker ≃+ ZMod 49) := by
  haveI : NeZero (2401 : ℕ) := ⟨by norm_num⟩
  have e := ker_mulLeft_addEquiv 2401 147
  rw [show Nat.gcd 2401 147 = 49 from by norm_num] at e
  exact ⟨e⟩

/-- **Example B, symbolic IC.** `IC(147; 2401) = 2·log 7`. -/
example : IC 147 2401 = 2 * Real.log 7 := by
  have h := card_Tor_eq_exp_IC (M := 147) (N := 2401) (by norm_num) (by norm_num)
  rw [show Nat.gcd 147 2401 = 49 from by norm_num] at h
  have h49 : IC 147 2401 = Real.log 49 := by
    rw [← Real.log_exp (IC 147 2401), ← h]; norm_num
  rw [h49, show (49 : ℝ) = 7 ^ 2 from by norm_num, Real.log_pow]; push_cast; ring

/-- **Example C (coprime, §4.4.5 / §3.6).** `gcd(12, 5) = 1`, so `Tor = 0`: the
obstruction group is trivial (`ℤ/1`) and `IC(12; 5) = 0`. -/
example : Nonempty ((AddMonoidHom.mulLeft ((12 : ℕ) : ZMod 5)).ker ≃+ ZMod 1) := by
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  have e := ker_mulLeft_addEquiv 5 12
  rw [show Nat.gcd 5 12 = 1 from by norm_num] at e
  exact ⟨e⟩

example : IC 12 5 = 0 := by
  rw [IC_eq_zero_iff_coprime (by norm_num) (by norm_num)]; decide

end WorkedExamplesBC

end Spt3

namespace Spt3Sheaf

/-- **G-6 (sheaf-level "no bad primes", §5.4 / Cor 9).**  When the four layers
admit every candidate (each is the full subpresheaf `⊤`, the normalized
`gcd(M,pᵏ)=1` regime), the amalgam is itself full: `F = B`, i.e.
`Γ(U,F) = Γ(U,B)` on every open. -/
theorem amalgam_no_bad_primes :
    amalgam (⊤ : Subfunctor B) ⊤ ⊤ ⊤ = (⊤ : Subfunctor B) := by
  simp only [amalgam, inf_top_eq]

end Spt3Sheaf

/-! ## Axiom audit for Category G. -/
section CategoryGAxiomAudit
#print axioms Spt3.crt_equalizer_compat_iff
#print axioms Spt3.gcd_primepow_eq
#print axioms Spt3.tor_primewise_addEquiv
#print axioms Spt3Sheaf.amalgam_no_bad_primes
end CategoryGAxiomAudit


/-! ============================================================================
    Category H — "one level deeper" + maximal Mathlib coverage (NEW).

    Per the request to (i) raise B3 from the valuation level to the genuine
    *ideal* equality in the localization, and (ii) prove everything else still
    reachable in current Mathlib.  All kernel-verified, sorry-free, axiom-free.

      • H-1  B3 UPGRADE — the localized intersection ideal equality (Prop 7, eq.(4),
             §3.5, CORRECTED to `max`).  Previously only the valuation identity
             `v_p(lcm) = max` was proved; H-1 proves the actual ideal equality in
             `S = ℤ_(p)`:  `((M)∩(pᵏ))·S = (p^{max(v_p M, k)})·S`, by factoring
             `lcm = p^{max}·c` with `c` a `p`-unit in the localization.
      • H-2  closed-form overlap gcd `gcd(M, pᵏ) = p^{min(v_p M, k)}` (§3.5, the
             gcd/Tor thickness, correctly attributed).
      • H-3  Theorem 14 in the paper's LITERAL `⊕` notation:
             `ker(×M on ℤ/N) ≃+ ⨁_{q∣N} ℤ/q^{min}`  (direct-sum form of G-3).
      • H-4  the free resolution `0→ℤ→^{×M} ℤ→ℤ/M→0` is EXACT as `Function.Exact`
             (upgrades the three separate A2/A4 facts to the actual exactness that
             justifies the `ker(×M)` Tor proxy).
      • H-5  Theorem 20 cotangent bridge, BOTH directions (honest):
             `FormallySmooth R A ↔ (Ω[A⁄R] projective ∧ H¹(L_{A/R}) = 0)`
             — the genuine Mathlib iff (`Algebra.formallySmooth_iff`), upgrading the
             previously one-directional `smooth ⇒ H¹=0` (B2) to an equivalence.
============================================================================ -/

namespace Spt3

/-- **H-2 (closed-form overlap gcd, §3.5).** `gcd(M, pᵏ) = p^{min(v_p M, k)}` — the
gcd/Tor thickness of the modular/p-adic overlap in closed form. -/
theorem gcd_primepow_overlap {M : ℕ} (hM : M ≠ 0) {p : ℕ} (k : ℕ) (hp : p.Prime) :
    Nat.gcd M (p ^ k) = p ^ min (M.factorization p) k := by
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left hM) (pow_ne_zero _ hp.pos.ne')
  intro q
  rw [factorization_gcd_apply hM (pow_ne_zero k hp.pos.ne')]
  rcases eq_or_ne q p with rfl | hqp
  · rw [Nat.factorization_pow_self hp, Nat.factorization_pow_self hp]
  · have h1 : (p ^ k).factorization q = 0 := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          Nat.Prime.factorization hp, Finsupp.single_apply, if_neg (Ne.symm hqp), mul_zero]
    have h2 : (p ^ min (M.factorization p) k).factorization q = 0 := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          Nat.Prime.factorization hp, Finsupp.single_apply, if_neg (Ne.symm hqp), mul_zero]
    rw [h1, h2]; exact min_eq_right (Nat.zero_le _)

/-- **H-1 (B3 raised to the ideal level; Prop 7, eq.(4), CORRECTED).**  In the
localization `S = ℤ_(p)` at the prime `(p)`, the equalizer-kernel ideal
`(M)∩(pᵏ) = (lcm M pᵏ)` becomes the principal power `(p^{max(v_p M, k)})`:
`((M)∩(pᵏ))·ℤ_(p) = (p^{max})·ℤ_(p)`.
(The paper writes `p^{min}`; the truth is `p^{max}`, since the intersection is the
`lcm`.  The prime-to-`p` cofactor of the `lcm` is a unit in `ℤ_(p)`, which is what
collapses the generator to `p^{max}`.) -/
theorem localized_intersection_ideal {M : ℕ} (k : ℕ) (hM : M ≠ 0) {p : ℕ} [hp : Fact p.Prime]
    (S : Type*) [CommRing S] [Algebra ℤ S]
    [IsLocalization.AtPrime S (Ideal.span {(p : ℤ)})] :
    (Ideal.span {(Nat.lcm M (p ^ k) : ℤ)}).map (algebraMap ℤ S)
      = (Ideal.span {((p : ℤ) ^ max (M.factorization p) k)}).map (algebraMap ℤ S) := by
  have hpp : p.Prime := hp.out
  set L := Nat.lcm M (p ^ k) with hLdef
  have hLne : L ≠ 0 := Nat.lcm_ne_zero hM (pow_ne_zero k hpp.pos.ne')
  have he : L.factorization p = max (M.factorization p) k := by
    rw [hLdef, factorization_lcm_apply hM (pow_ne_zero k hpp.pos.ne'),
        Nat.factorization_pow_self hpp]
  set c := ordCompl[p] L with hc
  have hsplit : p ^ L.factorization p * c = L := Nat.ordProj_mul_ordCompl_eq_self L p
  have hcop : ¬ p ∣ c := Nat.not_dvd_ordCompl (n := L) hpp hLne
  have hLZ : (L : ℤ) = (p : ℤ) ^ (L.factorization p) * (c : ℤ) := by
    have hcast : (L : ℤ) = ((p ^ L.factorization p * c : ℕ) : ℤ) := by rw [hsplit]
    rw [hcast]; push_cast; ring
  have hcS : IsUnit (algebraMap ℤ S (c : ℤ)) :=
    coprime_isUnit_atPrime (p := p)
      (fun hdvd => hcop (Int.natCast_dvd_natCast.mp hdvd)) S
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, hLZ, map_mul,
      Ideal.span_singleton_mul_right_unit hcS, he]

/-- **H-4 (the free resolution is exact, A2/A4 upgrade).**  The length-one free
resolution `0 → ℤ --(×M)--> ℤ --(mod M)--> ℤ/M → 0` is exact at the middle:
`range(×M) = ker(ℤ → ℤ/M)`, stated as `Function.Exact`.  Together with
`resolution_mul_injective` (left exact) and `resolution_mk_surjective` (right
exact) this is the full short exact sequence whose `Tor₁` is the `ker(×M)` proxy. -/
theorem resolution_exact (M : ℕ) :
    Function.Exact ((M : ℤ) * ·) ((↑) : ℤ → ZMod M) := by
  intro b
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

/-- **H-3 (Theorem 14 / Remark 19 in the paper's literal `⊕` notation).**  The
primewise group decomposition as an honest `DirectSum`:
`ker(×M on ℤ/N) ≃+ ⨁_{q∣N} ℤ/q^{min(v_q M, v_q N)}`,
i.e. the proxy realisation of `Tor₁(ℤ/M,ℤ/N) ≅ ⊕_{q∣N} ℤ/q^{min}`.  (Direct-sum
repackaging of `tor_primewise_addEquiv` via `DirectSum.linearEquivFunOnFintype`.) -/
noncomputable def tor_primewise_directSum {N : ℕ} (hN : N ≠ 0) (M : ℕ) (hM : M ≠ 0) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+
      DirectSum N.primeFactors
        (fun q => ZMod ((q : ℕ) ^ min (M.factorization (q : ℕ)) (N.factorization (q : ℕ)))) :=
  (tor_primewise_addEquiv hN M hM).trans
    (DirectSum.linearEquivFunOnFintype ℤ (N.primeFactors)
      (fun q => ZMod ((q : ℕ) ^ min (M.factorization (q : ℕ))
        (N.factorization (q : ℕ))))).symm.toAddEquiv

end Spt3

namespace Spt3

/-- **H-5 (Theorem 20 cotangent bridge, BOTH directions).**  Mathlib's definition of
formal smoothness is exactly the conjunction of the cotangent-vanishing and the
projectivity of Kähler differentials, giving the honest equivalence
`FormallySmooth R A ↔ (Ω[A⁄R] projective ∧ H¹(L_{A/R}) = 0)`.  This upgrades the
one-directional `smooth_imp_h1Cotangent_subsingleton` (B2) to an iff and makes the
exact extra hypothesis (projectivity of `Ω`) for the reverse direction visible. -/
theorem formallySmooth_iff_h1_and_projective (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] :
    Algebra.FormallySmooth R A ↔
      (Module.Projective A (KaehlerDifferential R A) ∧
        Subsingleton (Algebra.H1Cotangent R A)) :=
  ⟨fun h => ⟨h.projective_kaehlerDifferential, h.subsingleton_h1Cotangent⟩,
   fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

end Spt3

/-! ## Axiom audit for Category H. -/
section CategoryHAxiomAudit
#print axioms Spt3.gcd_primepow_overlap
#print axioms Spt3.localized_intersection_ideal
#print axioms Spt3.resolution_exact
#print axioms Spt3.tor_primewise_directSum
#print axioms Spt3.formallySmooth_iff_h1_and_projective
end CategoryHAxiomAudit


/-! ============================================================================
    Category I — further Mathlib-provable items from the formalization audit (NEW).

    Two genuinely new, kernel-verified additions (the audit's B3 and B5 were already
    closed in Categories H; B1/B4/B6 and the true `Tor` functor remain genuine
    future targets requiring large category-theory / site infrastructure):

      • A2-core  the truncated `p`-adic logarithm's TERMWISE survival bound.  Each
                 term `uⁿ/n` of `L(u)=∑(-1)^{n+1}uⁿ/n` (for `u ∈ pᵏℤ_p`) has
                 `v_p(uⁿ/n) = n·v_p(u) - v_p(n) ≥ n·k - v_p(n) ≥ k`.  The surviving
                 inequality `n·k - v_p(n) ≥ k` is exactly the Nat fact
                 `v_p(n) + k ≤ n·k`, proved here from the already-verified
                 `padicValNat_lt_self` (`v_p(n) < n`).  This is the Mathlib-only
                 replacement for the analytic 1-Lipschitz bound `|log(1+u)|_p ≤ p^{-k}`
                 (no Baker–Wüstholz needed).  Combined with `padic_log_defect_p_two`
                 it shows the bound is `≥ k` for every `p` (the paper's stronger `≥ 2k`
                 second-order claim is the one that degrades at `p = 2`).
      • B7       global-section gluing on an actual THREE-face principal-open cover in
                 the normalized "no bad primes" (pairwise-coprime) regime: pairwise
                 CRT-compatible local witnesses glue to one global witness.  This
                 lifts the two-face equalizer (`overlap_glue_iff_lcm`,
                 `crt_equalizer_compat_iff`) to a genuine multi-face cover, exactly
                 the §5.3 gluing protocol for normalized profiles.
============================================================================ -/

namespace Spt3

/-- **A2-core (truncated p-adic log, termwise survival).**  For `n ≥ 1` and depth
`k ≥ 1`, `v_p(n) + k ≤ n·k`, i.e. `n·k - v_p(n) ≥ k`.  Since the `n`-th truncated-log
term `uⁿ/n` with `u ∈ pᵏℤ_p` has valuation `n·v_p(u) - v_p(n) ≥ n·k - v_p(n)`, this
says every term survives at depth `≥ k`, which is the arithmetic core of the p-adic
gate `|log(1+u)|_p ≤ p^{-k}` — proved with Mathlib only (no Baker–Wüstholz). -/
theorem padic_log_term_survives {p : ℕ} [Fact p.Prime] {n k : ℕ} (hn : n ≠ 0) (hk : 1 ≤ k) :
    padicValNat p n + k ≤ n * k := by
  have h1 : padicValNat p n + 1 ≤ n := padicValNat_lt_self p n hn
  calc padicValNat p n + k
      ≤ padicValNat p n * k + k :=
        Nat.add_le_add_right (le_mul_of_one_le_right (Nat.zero_le _) hk) k
    _ = (padicValNat p n + 1) * k := by ring
    _ ≤ n * k := by gcongr

/-- **B7 (three-face gluing, normalized/coprime regime; §5.3 protocol).**  If the
three pairwise moduli `a, b, c` are pairwise coprime (the no-bad-primes profile
`gcd = 1`), then any three local witnesses `s₁, s₂, s₃` glue: there is a single
global witness `x` agreeing with each on its face, `a ∣ x-s₁`, `b ∣ x-s₂`,
`c ∣ x-s₃`.  This is the genuine multi-face upgrade of the two-face equalizer
`crt_equalizer_compat_iff`, obtained by composing the binary CRT gluing twice. -/
theorem crt_glue_triple {a b c : ℤ} (s₁ s₂ s₃ : ℤ)
    (hab : Int.gcd a b = 1) (hac : Int.gcd a c = 1) (hbc : Int.gcd b c = 1) :
    ∃ x : ℤ, a ∣ (x - s₁) ∧ b ∣ (x - s₂) ∧ c ∣ (x - s₃) := by
  obtain ⟨x₁, hx1a, hx1b⟩ :=
    crt_noncoprime_exists a b s₁ s₂ (by rw [hab, Nat.cast_one]; exact one_dvd _)
  have habc : Int.gcd (a * b) c = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one] at hac hbc ⊢
    exact hac.mul_left hbc
  obtain ⟨x, hxab, hxc⟩ :=
    crt_noncoprime_exists (a * b) c x₁ s₃ (by rw [habc, Nat.cast_one]; exact one_dvd _)
  refine ⟨x, ?_, ?_, hxc⟩
  · have ha_ab : a ∣ (x - x₁) := dvd_trans (dvd_mul_right a b) hxab
    have hsplit : x - s₁ = (x - x₁) + (x₁ - s₁) := by ring
    rw [hsplit]; exact dvd_add ha_ab hx1a
  · have hb_ab : b ∣ (x - x₁) := dvd_trans (dvd_mul_left b a) hxab
    have hsplit : x - s₂ = (x - x₁) + (x₁ - s₂) := by ring
    rw [hsplit]; exact dvd_add hb_ab hx1b

end Spt3

/-! ## Axiom audit for Category I. -/
section CategoryIAxiomAudit
#print axioms Spt3.padic_log_term_survives
#print axioms Spt3.crt_glue_triple
end CategoryIAxiomAudit


/-! ============================================================================
    Category J — B1 SES data + C1/C2 gap-as-theorem (NEW).

    Honest closure of the remaining audit items, subject to a HARD Mathlib limit:
    Mathlib has NO module `Tor` functor (only the `Functor.leftDerived` machinery and
    `Algebra.H1Cotangent`); there is no `def Tor`.  So "true `Tor₁ ≅ ℤ/gcd`" (B1),
    "true `Tor` naturality" (B6), and the n-fold `Tor(⊕)≅⊕Tor` (B2 at functor level)
    cannot be CLOSED sorry-free without first BUILDING `Tor` itself — a research-scale
    addition to Mathlib, not "assembly".  We therefore provide the honest maxima:

      • B1-data   the length-one free resolution `0→ℤ→^{×M}ℤ→ℤ/M→0` packaged as a
                  genuine short exact sequence of `ℤ`-modules (the exact INPUT a future
                  `leftDerived` computation consumes).  The categorical `Tor` step is
                  the only missing piece and it is missing from Mathlib, not from here.
      • C1        the main-theorem dilemma, as THEOREMS (not prose): (a) the three
                  lightweight gates do NOT exclude composites (`25` passes all three),
                  so soundness REQUIRES a genuinely complete layer; (b) once a complete
                  layer is present, the other three are logically redundant.
      • C2        the arithmetic obstruction equivalence `coprime ⟺ Tor-vanishing` holds
                  UNCONDITIONALLY (no geometry), isolating exactly what the paper's
                  Theorem-20 "gcd=1 ⟺ geometric smoothness" bridge adds as a hypothesis.
============================================================================ -/

namespace Spt3

/-- **B1-data (free resolution as a short exact sequence).**  The three facts
`injective(×M)`, `exact(×M, mod M)`, `surjective(mod M)` together say
`0 → ℤ --(×M)--> ℤ --(mod M)--> ℤ/M → 0` is a short exact sequence of `ℤ`-modules.
This is the precise projective-resolution input that `Functor.leftDerived 1` would
tensor with `ℤ/N` to produce `Tor₁`; the obstruction proxy `ker(×M on ℤ/N)`
(`card_ker_mulLeft`, `ker_mulLeft_addEquiv`) is exactly its first homology.  The
remaining categorical `Tor` identification is unavailable because Mathlib defines no
module `Tor` functor. -/
theorem resolution_shortExact (M : ℕ) [NeZero M] :
    Function.Injective ((M : ℤ) * ·) ∧
      Function.Exact ((M : ℤ) * ·) ((↑) : ℤ → ZMod M) ∧
      Function.Surjective ((↑) : ℤ → ZMod M) :=
  ⟨resolution_mul_injective (by exact_mod_cast (NeZero.ne M)),
   resolution_exact M, resolution_mk_surjective M⟩

/-- **C2 (arithmetic obstruction equivalence, UNCONDITIONAL).**  With no geometric
input whatsoever, coprimality is equivalent to the vanishing of the derived
obstruction group: `gcd(M,N)=1 ⟺ ker(×M on ℤ/N) = 0`.  This is the genuine,
unconditional half of Theorem 20; the paper's further identification with geometric
smoothness `H¹(L_{X_p})=0` is the EXTRA bridge hypothesis (`derived_equalizer_tfae`),
for which there is no actual morphism between an arbitrary modulus `M` and a fibre
`X_p` — hence it is correctly isolated as a hypothesis, not proved. -/
theorem obstruction_free_iff_arith (M N : ℕ) [NeZero N] (hM : M ≠ 0) :
    Nat.Coprime M N ↔ (AddMonoidHom.mulLeft (M : ZMod N)).ker = ⊥ :=
  (obstruction_tfae hM).out 0 2

end Spt3

namespace Spt3Cert

/-- **C1(a) (lightweight layers are insufficient — the dilemma, second horn).**  The
three lightweight gates (size `1<X`, parity, mod-3) do NOT characterise primality:
`X = 25 = 5²` is composite yet passes all three.  Hence the framework's soundness
genuinely REQUIRES a complete terminating layer (EC/AKS, or here Lucas–Pratt); the
"four lightweight gates exclude every composite" claim is false without it. -/
theorem lightweight_layers_insufficient :
    ∃ X : ℕ, ¬ X.Prime ∧ 1 < X ∧ (¬ 2 ∣ X ∨ X = 2) ∧ (¬ 3 ∣ X ∨ X = 3) :=
  ⟨25, by decide, by decide, Or.inl (by decide), Or.inl (by decide)⟩

/-- **C1(b) (a complete layer makes the others redundant — the dilemma, first horn).**
If `FEC` is already a complete primality test (`Prime ↔ FEC`), then the whole
certification collapses to `FEC` alone: the other three layers can be trivial `True`
without changing the verdict.  So the four layers cannot be simultaneously
"each necessary" and "EC complete" — exactly the formalization-revealed dilemma. -/
theorem complete_layer_makes_others_redundant
    (FEC : ℕ → Prop) (hcomplete : ∀ X, X.Prime ↔ FEC X) (X : ℕ) :
    X.Prime ↔ (True ∧ True ∧ True ∧ FEC X) := by
  rw [hcomplete X]; tauto

end Spt3Cert

/-! ## Axiom audit for Category J. -/
section CategoryJAxiomAudit
#print axioms Spt3.resolution_shortExact
#print axioms Spt3.obstruction_free_iff_arith
#print axioms Spt3Cert.lightweight_layers_insufficient
#print axioms Spt3Cert.complete_layer_makes_others_redundant
end CategoryJAxiomAudit


/-! ============================================================================
    Category K — a GENUINE derived `Tor` functor on `ModuleCat ℤ` (NEW, B1/B6).

    Per the request to actually CONTRIBUTE a module `Tor` functor (Mathlib has none —
    only the `Functor.leftDerived` machinery): we DEFINE the real left-derived functor
    of `N ⊗ -` on `ModuleCat ℤ` and prove its characteristic derived-functor identities.
    This is no longer the `ker(×M)` proxy — it is the genuine `Torₙ(N, -)`.

      • `Tor N n`                    the genuine derived functor `Torₙ(N, -)`.
      • `torZeroIso`                 `Tor₀(N, -) ≅ N ⊗ -`            (derived-functor axiom).
      • `torSucc_projective_isZero`  `Torₙ₊₁(N, P) = 0` for projective `P`  (axiom).
      • `tensorLeftNatTrans`,`torCoeffMap`   B6: functoriality + a coefficient map
                                     `M ⟶ N` induces a natural transformation
                                     `Tor M n ⟶ Tor N n` (naturality of the derived functor).
      • `tor1_value`                 the closed-form VALUE the paper asserts:
                                     `Tor₁(ℤ/M, ℤ/N)`, computed through the standard
                                     length-one free resolution `0→ℤ→^{×M}ℤ→ℤ/M→0`, is the
                                     homology `ker(×M on ℤ/N) ≃+ ℤ/gcd(N,M)` (`ker_mulLeft_addEquiv`).

    ⚠ The remaining purely-bureaucratic step — wiring the categorical object iso
    `(Tor (ℤ/M) 1).obj (ℤ/N) ≅ ℤ/gcd` through a HAND-BUILT `ProjectiveResolution`
    (`ChainComplex` + `QuasiIso` + homology identification) — is a Mathlib-PR-scale
    construction (Mathlib has no SES→resolution constructor); we provide the genuine
    functor and the homology-group value rather than fake the object iso with `sorry`. -/

namespace Spt3Tor

open CategoryTheory MonoidalCategory CategoryTheory.Limits

/-- `ModuleCat ℤ`, the abelian category of `ℤ`-modules (= abelian groups). -/
abbrev ModZ := ModuleCat.{0} ℤ

/-- **B1 (genuine derived `Tor`).** The actual left-derived functor of `N ⊗ -` on
`ModuleCat ℤ`; `(Tor N n).obj X` is `Torₙ(N, X)`.  This is a true derived functor,
not the `ker(×M)` proxy. -/
noncomputable def Tor (N : ModZ) (n : ℕ) : ModZ ⥤ ModZ :=
  Functor.leftDerived (MonoidalCategory.tensorLeft N) n

/-- **B2 key lemma (NEW, proved).** The chosen-projective-resolution functor
`projectiveResolutions C : C ⥤ HomotopyCategory C` is additive.  This was the precise
blocker for functor-level Tor additivity: it is proved here from the homotopy-uniqueness
of lifts (`ProjectiveResolution.liftHomotopy`) — `lift (f+g) ≃ lift f + lift g` up to
homotopy, hence equal in the homotopy category (`HomotopyCategory.eq_of_homotopy`). -/
instance projectiveResolutions_additive {C : Type*} [Category C] [Abelian C]
    [HasProjectiveResolutions C] : (projectiveResolutions C).Additive where
  map_add {X Y f g} := by
    have hcomm :
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
          ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y)) ≫
            (projectiveResolution Y).π =
          (projectiveResolution X).π ≫ (ChainComplex.single₀ C).map (f + g) := by
      rw [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp,
          ProjectiveResolution.lift_commutes, ProjectiveResolution.lift_commutes]
    have h := ProjectiveResolution.liftHomotopy (f + g) _ _
      (ProjectiveResolution.lift_commutes (f + g) _ _) hcomm
    have e1 : (projectiveResolutions C).map (f + g) =
        (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
            ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y)) :=
      HomotopyCategory.eq_of_homotopy _ _ h
    rw [e1]
    exact Functor.map_add _

/-- **B2 (genuine `Tor` is additive).** The derived functor `Torₙ(N, -)` is an additive
functor — now an instance (was the missing piece), via `projectiveResolutions_additive`. -/
instance torAdditive (N : ModZ) (n : ℕ) : (Tor N n).Additive := by
  unfold Tor Functor.leftDerived Functor.leftDerivedToHomotopyCategory; infer_instance

/-- **B2 (n-fold/binary Tor additivity, functor level — the paper's `Tor(⊕Bᵢ)≅⊕Tor(Bᵢ)`).**
The genuine derived functor `Torₙ(N, -)` carries the binary direct sum to the binary
direct sum: `Torₙ(N, X ⊞ Y) ≅ Torₙ(N, X) ⊞ Torₙ(N, Y)`.  Proved from `Tor`'s additivity
(`torAdditive`) via biproduct preservation of additive functors — no longer a proxy. -/
noncomputable def torBiprod (N : ModZ) (n : ℕ) (X Y : ModZ) :
    (Tor N n).obj (X ⊞ Y) ≅ (Tor N n).obj X ⊞ (Tor N n).obj Y := by
  haveI : PreservesBinaryBiproducts (Tor N n) :=
    preservesBinaryBiproducts_of_preservesBiproducts (Tor N n)
  exact (Tor N n).mapBiprod X Y

/-- **Derived-functor axiom 1.** `Tor₀(N, -) ≅ N ⊗ -`. -/
noncomputable def torZeroIso (N : ModZ) : Tor N 0 ≅ MonoidalCategory.tensorLeft N :=
  Functor.leftDerivedZeroIsoSelf (MonoidalCategory.tensorLeft N)

/-- **Derived-functor axiom 2.** Higher `Tor` of a projective module vanishes. -/
theorem torSucc_projective_isZero (N : ModZ) (n : ℕ) (X : ModZ) [Projective X] :
    IsZero ((Tor N (n + 1)).obj X) :=
  Functor.isZero_leftDerived_obj_projective_succ (MonoidalCategory.tensorLeft N) n X

/-- A coefficient morphism `f : M ⟶ N` induces a natural transformation `M ⊗ - ⟶ N ⊗ -`. -/
noncomputable def tensorLeftNatTrans {M N : ModZ} (f : M ⟶ N) :
    MonoidalCategory.tensorLeft M ⟶ MonoidalCategory.tensorLeft N where
  app X := f ▷ X
  naturality _ _ g := whisker_exchange f g

/-- **B6 (Tor naturality in the coefficient).** A module map `f : M ⟶ N` derives to a
natural transformation `Tor M n ⟶ Tor N n` — the genuine naturality of the derived
functor, supplied by `NatTrans.leftDerived`. -/
noncomputable def torCoeffMap {M N : ModZ} (f : M ⟶ N) (n : ℕ) : Tor M n ⟶ Tor N n :=
  NatTrans.leftDerived (tensorLeftNatTrans f) n

/-- **Closed-form value of `Tor₁` (the paper's `Tor₁(ℤ/M, ℤ/N) ≅ ℤ/gcd`).**  Through the
standard length-one free resolution `0 → ℤ --(×M)--> ℤ → ℤ/M → 0` (whose exactness is
`Spt3.resolution_shortExact`), `Tor₁(ℤ/M, ℤ/N)` is the first homology `ker(×M on ℤ/N)`,
and that group is `≃+ ℤ/gcd(N,M)` by `Spt3.ker_mulLeft_addEquiv`.  This records the
arithmetic value the genuine functor `Tor` above takes in degree 1. -/
theorem tor1_value (N M : ℕ) [NeZero N] :
    Nonempty ((AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod (Nat.gcd N M)) :=
  ⟨Spt3.ker_mulLeft_addEquiv N M⟩

end Spt3Tor

/-! ## Axiom audit for Category K. -/
section CategoryKAxiomAudit
#print axioms Spt3Tor.Tor
#print axioms Spt3Tor.torZeroIso
#print axioms Spt3Tor.torSucc_projective_isZero
#print axioms Spt3Tor.projectiveResolutions_additive
#print axioms Spt3Tor.torAdditive
#print axioms Spt3Tor.torBiprod
#print axioms Spt3Tor.torCoeffMap
#print axioms Spt3Tor.tor1_value
end CategoryKAxiomAudit


/-! ============================================================================
    Integrated B1 resolution file

    This final block incorporates the separately supplied
    `B1_resolution_VERIFIED.lean`.  It is namespaced so that its short, convenient
    names (`resC`, `mulN`, `piN`, ...) do not collide with the main `Spt3`
    namespace.  The block packages the standard length-one free projective
    resolution of `ZMod N` in `ModuleCat ℤ`.
============================================================================ -/

namespace Spt3B1Resolution

open CategoryTheory Limits

/-- `ModuleCat ℤ`, the category of abelian groups as `ℤ`-modules. -/
abbrev ModZ := ModuleCat.{0} ℤ

/-- The free rank-one `ℤ`-module. -/
abbrev Zz : ModZ := ModuleCat.of ℤ ℤ

/-- A zero object represented by the subsingleton module `PUnit`. -/
abbrev Zp : ModZ := ModuleCat.of ℤ PUnit

/-- Multiplication by `N` as an endomorphism of the free rank-one module. -/
noncomputable def mulN (N : ℕ) : Zz ⟶ Zz :=
  ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ (N : ℤ))

/-- Objects of the two-term free resolution, padded by zero objects above degree 1. -/
def Xf : ℕ → ModZ := fun n => match n with | 0 => Zz | 1 => Zz | _ => Zp

/-- Differential of the resolution: degree `1 → 0` is multiplication by `N`. -/
noncomputable def df (N : ℕ) : ∀ n, Xf (n + 1) ⟶ Xf n :=
  fun n => match n with | 0 => mulN N | _ => 0

theorem resC_sq (N : ℕ) : ∀ n, df N (n + 1) ≫ df N n = 0 :=
  fun n => by
    have : df N (n + 1) = 0 := rfl
    rw [this, zero_comp]

/-- The chain complex `ℤ --N→ ℤ`, concentrated in degrees `1` and `0`. -/
noncomputable def resC (N : ℕ) : ChainComplex ModZ ℕ :=
  ChainComplex.of Xf (df N) (resC_sq N)

theorem resC_proj (N : ℕ) (n : ℕ) : Projective ((resC N).X n) := by
  rw [resC, ChainComplex.of_x]
  match n with
  | 0 => exact (inferInstanceAs (Projective Zz))
  | 1 => exact (inferInstanceAs (Projective Zz))
  | (_ + 2) => exact (ModuleCat.isZero_of_subsingleton Zp).projective

theorem resC_d10 (N : ℕ) : (resC N).d 1 0 = mulN N :=
  ChainComplex.of_d Xf (df N) (resC_sq N) 0

theorem resC_d21 (N : ℕ) : (resC N).d 2 1 = 0 :=
  ChainComplex.of_d Xf (df N) (resC_sq N) 1

theorem mulN_mono (N : ℕ) [NeZero N] : Mono (mulN N) := by
  rw [ModuleCat.mono_iff_injective]
  intro a b hab
  have h2 : (N : ℤ) * a = (N : ℤ) * b := hab
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr (NeZero.ne N)) h2

theorem resC_exactAt_succ (N : ℕ) [NeZero N] (n : ℕ) :
    (resC N).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' (resC N) (n + 2) (n + 1) n (by simp) (by simp)]
  match n with
  | 0 =>
    have hf : ((resC N).sc' 2 1 0).f = 0 := by
      show (resC N).d 2 1 = 0
      exact resC_d21 N
    rw [ShortComplex.exact_iff_mono _ hf]
    have hg : ((resC N).sc' 2 1 0).g = mulN N := by
      show (resC N).d 1 0 = mulN N
      exact resC_d10 N
    rw [hg]
    exact mulN_mono N
  | (_ + 1) =>
    apply ShortComplex.exact_of_isZero_X₂
    show IsZero Zp
    exact ModuleCat.isZero_of_subsingleton Zp

/-- The quotient map `ℤ → ZMod N`. -/
noncomputable def quotN (N : ℕ) : Zz ⟶ ModuleCat.of ℤ (ZMod N) :=
  ModuleCat.ofHom ((Int.castAddHom (ZMod N)).toIntLinearMap)

theorem mulN_quotN (N : ℕ) : mulN N ≫ quotN N = 0 := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x => ?_
  show ((((N : ℤ) • x : ℤ)) : ZMod N) = 0
  rw [smul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

theorem sc_exact (N : ℕ) :
    (ShortComplex.mk (mulN N) (quotN N) (mulN_quotN N)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    show (((N : ℤ) • x : ℤ) : ZMod N) = 0
    rw [smul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  · intro y hy
    have hdvd : (N : ℤ) ∣ y := by
      rwa [LinearMap.mem_ker, show (quotN N).hom y = ((y : ZMod N)) from rfl,
        ZMod.intCast_zmod_eq_zero_iff_dvd] at hy
    obtain ⟨k, rfl⟩ := hdvd
    exact ⟨k, by
      show (N : ℤ) • k = N * k
      rw [smul_eq_mul]⟩

noncomputable def piN (N : ℕ) :
    resC N ⟶ (ChainComplex.single₀ ModZ).obj (ModuleCat.of ℤ (ZMod N)) :=
  (ChainComplex.toSingle₀Equiv (resC N) (ModuleCat.of ℤ (ZMod N))).symm
    ⟨quotN N, by
      rw [resC_d10]
      exact mulN_quotN N⟩

/-- The projective resolution of `ZMod N` used by the B1 Tor computation. -/
noncomputable def resP (N : ℕ) [NeZero N] :
    ProjectiveResolution (ModuleCat.of ℤ (ZMod N)) where
  complex := resC N
  projective := resC_proj N
  π := piN N
  quasiIso := ⟨fun n => by
    match n with
    | 0 =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨sc_exact N, ?_⟩
        · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
            (by aesop_cat) (by aesop_cat)
        · rw [ModuleCat.epi_iff_surjective]
          exact ZMod.intCast_surjective
      all_goals rfl
    | (k + 1) =>
      rw [quasiIsoAt_iff_exactAt']
      · exact resC_exactAt_succ N k
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

section AxiomAudit
#print axioms resC
#print axioms resC_proj
#print axioms resC_exactAt_succ
#print axioms sc_exact
#print axioms resP
end AxiomAudit

end Spt3B1Resolution


/-! ============================================================================
    Final checklist closure

    This section is the honest endpoint for the requested "fill the checklist with
    actual proofs" task.  Every declaration below is a theorem/definition accepted
    by the Lean kernel.  When a paper-level sentence is not a theorem as stated
    (for example arbitrary global certification, or an unconditional
    arithmetic-to-smoothness bridge with no geometric data), the file closes the
    item by proving the precise obstruction rather than introducing an axiom.
============================================================================ -/

namespace Spt3FinalChecklist

open CategoryTheory TopologicalSpace

/-! ### 1. `Spec ℤ`, principal/open-cover site, and subsheaf amalgam. -/

/-- The site used throughout is the open-cover Grothendieck topology on `Spec ℤ`. -/
theorem specZ_site_is_open_cover_topology :
    Spt3Sheaf.siteJ = Opens.grothendieckTopology Spt3Sheaf.S := rfl

/-- The four-layer amalgam is a genuine subpresheaf intersection over the ambient `B`. -/
theorem sheaf_amalgam_membership
    (Fnum Fmod Fpadic FEC : Subfunctor Spt3Sheaf.B)
    {U : (Opens Spt3Sheaf.S)ᵒᵖ} (s : Spt3Sheaf.B.obj U) :
    s ∈ (Spt3Sheaf.amalgam Fnum Fmod Fpadic FEC).obj U
      ↔ s ∈ Fnum.obj U ∧ s ∈ Fmod.obj U ∧
        s ∈ Fpadic.obj U ∧ s ∈ FEC.obj U :=
  Spt3Sheaf.mem_amalgam Fnum Fmod Fpadic FEC s

/-- Once the ambient object and the four layers are sheaves, their amalgam is a sheaf. -/
theorem sheaf_amalgam_is_sheaf
    (hB : Presieve.IsSheaf Spt3Sheaf.siteJ Spt3Sheaf.B)
    (Fnum Fmod Fpadic FEC : Subfunctor Spt3Sheaf.B)
    (hn : Presieve.IsSheaf Spt3Sheaf.siteJ Fnum.toFunctor)
    (hm : Presieve.IsSheaf Spt3Sheaf.siteJ Fmod.toFunctor)
    (hp : Presieve.IsSheaf Spt3Sheaf.siteJ Fpadic.toFunctor)
    (he : Presieve.IsSheaf Spt3Sheaf.siteJ FEC.toFunctor) :
    Presieve.IsSheaf Spt3Sheaf.siteJ
      (Spt3Sheaf.amalgam Fnum Fmod Fpadic FEC).toFunctor :=
  Spt3Sheaf.amalgam_isSheaf hB Fnum Fmod Fpadic FEC hn hm hp he

/-! ### 2. Concrete layer predicates and a complete certificate layer. -/

/-- The concrete Lucas-backed four layers really characterize primality. -/
theorem concrete_four_layers_iff_prime (X : ℕ) :
    X.Prime ↔
      (Spt3Cert.Fnum_layer X ∧ Spt3Cert.Fmod_layer X ∧
        Spt3Cert.Fpadic_layer X ∧ Spt3Cert.FEC_layer X) := by
  constructor
  · intro hX
    refine ⟨hX.one_lt, ?_, ?_, Spt3Cert.LucasCert_complete hX⟩
    · by_cases h2 : 2 ∣ X
      · rcases Nat.Prime.eq_one_or_self_of_dvd hX 2 h2 with h | h
        · exact False.elim (by norm_num at h)
        · exact Or.inr h.symm
      · exact Or.inl h2
    · by_cases h3 : 3 ∣ X
      · rcases Nat.Prime.eq_one_or_self_of_dvd hX 3 h3 with h | h
        · exact False.elim (by norm_num at h)
        · exact Or.inr h.symm
      · exact Or.inl h3
  · rintro ⟨_, _, _, hEC⟩
    exact Spt3Cert.LucasCert_sound hEC

/-- The EC/Lucas layer is not cosmetic: `25` passes the lightweight gates but fails it. -/
theorem lightweight_layers_do_not_suffice :
    Spt3Cert.Fnum_layer 25 ∧ Spt3Cert.Fmod_layer 25 ∧
      Spt3Cert.Fpadic_layer 25 ∧ ¬ Spt3Cert.FEC_layer 25 :=
  Spt3Cert.layer_indep_EC

/-! ### 3. p-adic-log arithmetic core. -/

/-- Kernel-checked arithmetic core of the truncated `p`-adic logarithm survival bound. -/
theorem padic_log_termwise_survival
    {p : ℕ} [Fact p.Prime] {n k : ℕ} (hn : n ≠ 0) (hk : 1 ≤ k) :
    padicValNat p n + k ≤ n * k :=
  Spt3.padic_log_term_survives hn hk

/-! ### 4. Hensel/discriminant/good-prime components. -/

/-- Formal étaleness gives the Hensel-style unique lift along square-zero extensions. -/
theorem hensel_unique_lift
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  Spt3.hensel_multivar_unique_lift I hI

/-- Away from the discriminant, a reduced Weierstrass equation is nonsingular. -/
theorem elliptic_good_reduction
    {W : WeierstrassCurve ℤ} {p : ℕ} [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ W.Δ) (x y : ZMod p) :
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation x y ↔
      (W.map (Int.castRingHom (ZMod p))).toAffine.Nonsingular x y :=
  Spt3.ec_good_reduction hp x y

/-! ### 5. Literal derived-functor API and the `Tor₁` arithmetic value. -/

/-- The literal left-derived functor used as `Tor`. -/
noncomputable def literalTor (N : Spt3Tor.ModZ) (n : ℕ) : Spt3Tor.ModZ ⥤ Spt3Tor.ModZ :=
  Spt3Tor.Tor N n

/-- The literal derived functor is additive in the second argument. -/
instance literalTor_additive (N : Spt3Tor.ModZ) (n : ℕ) :
    (literalTor N n).Additive :=
  Spt3Tor.torAdditive N n

/-- The computed degree-one value supplied by the length-one resolution. -/
theorem tor1_value_as_gcd_kernel (N M : ℕ) [NeZero N] :
    Nonempty ((AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod (Nat.gcd N M)) :=
  Spt3Tor.tor1_value N M

/-- The separately supplied B1 projective resolution is integrated as a real object. -/
noncomputable def integrated_projective_resolution (N : ℕ) [NeZero N] :
    ProjectiveResolution (ModuleCat.of ℤ (ZMod N)) :=
  Spt3B1Resolution.resP N

/-! ### 6. Theorem 20: what is unconditional, and why a bridge hypothesis is necessary. -/

/-- The unconditional arithmetic half: coprimality iff the kernel obstruction vanishes. -/
theorem obstruction_vanishes_iff_coprime (M N : ℕ) [NeZero N] (hM : M ≠ 0) :
    Nat.Coprime M N ↔ (AddMonoidHom.mulLeft (M : ZMod N)).ker = ⊥ :=
  Spt3.obstruction_free_iff_arith M N hM

/-- The honest cotangent-complex algebraic bridge available in Mathlib. -/
theorem formal_smooth_iff_h1_and_projective
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    Algebra.FormallySmooth R A ↔
      (Module.Projective A (KaehlerDifferential R A) ∧
        Subsingleton (Algebra.H1Cotangent R A)) :=
  Spt3.formallySmooth_iff_h1_and_projective R A

/-- No theorem can identify `gcd = 1` with an arbitrary `smooth = True` predicate. -/
theorem unconditional_gcd_smooth_bridge_false_true_case :
    ¬ ((Nat.gcd 2 4 = 1) ↔ True) := by
  norm_num

/-- Nor can it identify a coprime overlap with an arbitrary `smooth = False` predicate. -/
theorem unconditional_gcd_smooth_bridge_false_false_case :
    ¬ ((Nat.gcd 2 3 = 1) ↔ False) := by
  norm_num

/-! ### 7. Global-section certification: closed with a complete layer, false arbitrarily. -/

/-- With a complete Lucas-Pratt layer, the certification criterion is a theorem. -/
theorem global_certification_with_lucas (X : ℕ) :
    X.Prime ↔ (True ∧ True ∧ True ∧ Spt3Cert.LucasCert X) :=
  Spt3Cert.prime_iff_section X

/-- Arbitrary/trivial layers cannot certify primality: `4` would be accepted. -/
theorem arbitrary_layers_cannot_certify :
    ¬ (∀ X : ℕ, X.Prime ↔ (True ∧ True ∧ True ∧ True)) := by
  intro h
  have h4 : Nat.Prime 4 := (h 4).mpr ⟨trivial, trivial, trivial, trivial⟩
  exact (by decide : ¬ Nat.Prime 4) h4

/-! ### 8. The min/max correction is fully formalized. -/

/-- Intersection membership uses `lcm`, hence max-valuations. -/
theorem intersection_membership_uses_lcm (M N T : ℤ) :
    (T ∈ Ideal.span {M} ⊓ Ideal.span {N}) ↔ lcm M N ∣ T :=
  Spt3.zeroClass_mem_iff_lcm M N T

/-- The gcd/Tor thickness uses `min`. -/
theorem gcd_thickness_uses_min {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p =
      min (M.factorization p) (N.factorization p) :=
  Spt3.factorization_gcd_apply hM hN p

/-- The intersection/lcm thickness uses `max`. -/
theorem intersection_thickness_uses_max {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p =
      max (M.factorization p) (N.factorization p) :=
  Spt3.factorization_lcm_apply hM hN p

/-- Concrete counterexample to the paper's incorrect min/intersection reading. -/
theorem paper_min_intersection_reading_is_false :
    ¬ (∀ T : ℕ, ((3 : ℕ) ∣ T ↔ (12 : ℕ) ∣ T ∧ (9 : ℕ) ∣ T)) := by
  intro h
  have h3 : (3 : ℕ) ∣ 3 ↔ (12 : ℕ) ∣ 3 ∧ (9 : ℕ) ∣ 3 := h 3
  have hleft : (3 : ℕ) ∣ 3 := by norm_num
  have hbad := h3.mp hleft
  exact (by norm_num : ¬ ((12 : ℕ) ∣ 3 ∧ (9 : ℕ) ∣ 3)) hbad

section AxiomAudit
#print axioms specZ_site_is_open_cover_topology
#print axioms sheaf_amalgam_membership
#print axioms sheaf_amalgam_is_sheaf
#print axioms concrete_four_layers_iff_prime
#print axioms lightweight_layers_do_not_suffice
#print axioms padic_log_termwise_survival
#print axioms hensel_unique_lift
#print axioms elliptic_good_reduction
#print axioms literalTor
#print axioms literalTor_additive
#print axioms tor1_value_as_gcd_kernel
#print axioms integrated_projective_resolution
#print axioms obstruction_vanishes_iff_coprime
#print axioms formal_smooth_iff_h1_and_projective
#print axioms unconditional_gcd_smooth_bridge_false_true_case
#print axioms unconditional_gcd_smooth_bridge_false_false_case
#print axioms global_certification_with_lucas
#print axioms arbitrary_layers_cannot_certify
#print axioms intersection_membership_uses_lcm
#print axioms gcd_thickness_uses_min
#print axioms intersection_thickness_uses_max
#print axioms paper_min_intersection_reading_is_false
end AxiomAudit

end Spt3FinalChecklist


/-! ============================================================================
    Category L — T1-1 (genuine Tor OBJECT iso) + T3-2 (n-fold gluing) (NEW).

    The two genuinely-new last-mile closures, kernel-verified (sorry-free,
    axiom-free; audited below):

      • T3-2 `crt_glue_finset` — CRT gluing over an ARBITRARY finite family of
              pairwise-coprime moduli (generalizes `crt_glue_triple`).
      • T1-1 `tor1_obj_iso` — the **genuine derived-functor object isomorphism**
              `(Spt3Tor.Tor (ℤ/M) 1).obj (ℤ/N) ≅ ℤ/gcd(M,N)` in `ModuleCat ℤ`,
              computed THROUGH the explicit projective resolution
              `Spt3B1Resolution.resP N` via `ProjectiveResolution.isoLeftDerivedObj`:
              the value is the degree-1 homology of the tensored resolution, which
              (since the incoming differential vanishes) is the kernel of
              `(×N) ⊗ id` on `(ℤ/M) ⊗ ℤ`, transported by the right unitor to
              `ker(×N on ℤ/M)`, hence `≃ ℤ/gcd(M,N)` by `ker_mulLeft_addEquiv`.
              This closes the object-level wiring left open by Category K
              (`Spt3Tor.tor1_value` was only the group-level value).
============================================================================ -/

namespace Spt3TorValue

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct
open Spt3B1Resolution

/-- **T3-2 (n-fold CRT gluing, normalized/coprime regime).**  For any finite index
set `t`, pairwise-coprime moduli `m`, and arbitrary residues `s`, there is a single
global witness `x` with `m i ∣ (x - s i)` for every `i ∈ t`.  Generalizes the
two-face and three-face equalizers (`overlap_glue_iff_lcm`, `crt_glue_triple`) to
an arbitrary finite cover. -/
theorem crt_glue_finset {ι : Type*} [DecidableEq ι] (m s : ι → ℤ) :
    ∀ t : Finset ι,
      (∀ i ∈ t, ∀ j ∈ t, i ≠ j → IsCoprime (m i) (m j)) →
      ∃ x : ℤ, ∀ i ∈ t, m i ∣ (x - s i) := by
  intro t
  induction t using Finset.induction with
  | empty => intro _; exact ⟨0, by simp⟩
  | @insert i₀ t hi₀ ih =>
    intro hpair
    obtain ⟨x₁, hx₁⟩ := ih (fun i hi j hj hij =>
      hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    set P : ℤ := ∏ j ∈ t, m j with hP
    have hcop : IsCoprime (m i₀) P := by
      rw [hP]
      refine IsCoprime.prod_right (fun j hj => ?_)
      exact hpair i₀ (Finset.mem_insert_self i₀ t) j (Finset.mem_insert_of_mem hj)
        (fun h => hi₀ (h ▸ hj))
    have hgcd : (Int.gcd (m i₀) P : ℤ) ∣ (s i₀ - x₁) := by
      rw [Int.isCoprime_iff_gcd_eq_one.mp hcop, Nat.cast_one]; exact one_dvd _
    obtain ⟨x, hxi, hxP⟩ := Spt3.crt_noncoprime_exists (m i₀) P (s i₀) x₁ hgcd
    refine ⟨x, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hit
    · exact hxi
    · have hdvdP : m i ∣ P := by rw [hP]; exact Finset.dvd_prod_of_mem m hit
      have h1 : m i ∣ (x - x₁) := dvd_trans hdvdP hxP
      have h2 : m i ∣ (x₁ - s i) := hx₁ i hit
      have hsplit : x - s i = (x - x₁) + (x₁ - s i) := by ring
      rw [hsplit]; exact dvd_add h1 h2

/-- Transport of a kernel along an intertwining linear equivalence. -/
def kerEquivOfIntertwine {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (f : A →ₗ[ℤ] A) (g : B →ₗ[ℤ] B) (h : ∀ a, e (f a) = g (e a)) :
    (LinearMap.ker f) ≃ₗ[ℤ] (LinearMap.ker g) where
  toFun x := ⟨e x.1, by
    rw [LinearMap.mem_ker, ← h x.1, (LinearMap.mem_ker.mp x.2), map_zero]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  invFun y := ⟨e.symm y.1, by
    rw [LinearMap.mem_ker]; apply e.injective
    rw [h, e.apply_symm_apply, (LinearMap.mem_ker.mp y.2), map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

/-- The kernel of `(×N) ⊗ id` on `(ℤ/M) ⊗ ℤ` is linearly equivalent to `ℤ/gcd(M,N)`. -/
noncomputable def kerLTensor_equiv_gcd (M N : ℕ) [NeZero M] :
    (LinearMap.ker (((LinearMap.lsmul ℤ ℤ (N : ℤ)).lTensor (ZMod M))))
      ≃ₗ[ℤ] ZMod (Nat.gcd M N) := by
  have hint : ∀ a : (ZMod M) ⊗[ℤ] ℤ,
      (TensorProduct.rid ℤ (ZMod M)) (((LinearMap.lsmul ℤ ℤ (N : ℤ)).lTensor (ZMod M)) a)
        = (LinearMap.lsmul ℤ (ZMod M) (N : ℤ)) ((TensorProduct.rid ℤ (ZMod M)) a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul m z =>
        simp only [LinearMap.lTensor_tmul, LinearMap.lsmul_apply, TensorProduct.rid_tmul,
          smul_eq_mul]
        exact mul_smul _ _ _
    | add a b ha hb => simp [map_add, ha, hb]
  let e1 := kerEquivOfIntertwine (TensorProduct.rid ℤ (ZMod M))
    ((LinearMap.lsmul ℤ ℤ (N : ℤ)).lTensor (ZMod M))
    (LinearMap.lsmul ℤ (ZMod M) (N : ℤ)) hint
  have hval : ∀ x : ZMod M,
      (LinearMap.lsmul ℤ (ZMod M) (N : ℤ)) x = (AddMonoidHom.mulLeft (N : ZMod M)) x := by
    intro x
    rw [LinearMap.lsmul_apply, zsmul_eq_mul, Int.cast_natCast]
    rfl
  have hset : ∀ x : ZMod M, (LinearMap.lsmul ℤ (ZMod M) (N : ℤ)) x = 0
      ↔ (AddMonoidHom.mulLeft (N : ZMod M)) x = 0 := fun x => by rw [hval x]
  let e2 : (LinearMap.ker (LinearMap.lsmul ℤ (ZMod M) (N : ℤ)))
      ≃+ (AddMonoidHom.mulLeft (N : ZMod M)).ker :=
    { toFun := fun x => ⟨x.1, (hset x.1).mp (LinearMap.mem_ker.mp x.2)⟩
      invFun := fun x => ⟨x.1, LinearMap.mem_ker.mpr ((hset x.1).mpr x.2)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  exact e1.trans ((e2.trans (Spt3.ker_mulLeft_addEquiv M N)).toIntLinearEquiv)

/-- **T1-1 (the genuine Tor OBJECT isomorphism).**  Through the explicit length-one
projective resolution `Spt3B1Resolution.resP N`, the value of the genuine derived
functor `Spt3Tor.Tor (ℤ/M) 1` at `ℤ/N` is identified with `ℤ/gcd(M,N)`:
`(Spt3Tor.Tor (ℤ/M) 1).obj (ℤ/N) ≅ ℤ/gcd(M,N)` in `ModuleCat ℤ`.  This is the genuine
derived-functor value, no longer the bare group proxy `Spt3Tor.tor1_value`. -/
noncomputable def tor1_obj_iso (M N : ℕ) [NeZero M] [NeZero N] :
    (Spt3Tor.Tor (ModuleCat.of ℤ (ZMod M)) 1).obj (ModuleCat.of ℤ (ZMod N))
      ≅ ModuleCat.of ℤ (ZMod (Nat.gcd M N)) := by
  set A : ModZ := ModuleCat.of ℤ (ZMod M) with hA
  let iso1 := (resP N).isoLeftDerivedObj (MonoidalCategory.tensorLeft A) 1
  set G := ((MonoidalCategory.tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (resC N) with hG
  let iso2 := (HomologicalComplex.homologyFunctorIso' ModZ (ComplexShape.down ℕ) 2 1 0
    (by simp) (by simp)).app G
  set S := G.sc' 2 1 0 with hS
  have hSf : S.f = 0 := by
    show (((MonoidalCategory.tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resC N)).d 2 1 = 0
    rw [Functor.mapHomologicalComplex_obj_d, resC_d21]
    exact Functor.map_zero _ _ _
  haveI : IsIso S.homologyπ := S.isIso_homologyπ hSf
  let iso3 := (asIso S.homologyπ).symm
  let iso4 := S.moduleCatCyclesIso
  have hSg : S.g.hom = ((LinearMap.lsmul ℤ ℤ (N : ℤ)).lTensor (ZMod M)) := by
    show ((((MonoidalCategory.tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resC N)).d 1 0).hom = ((LinearMap.lsmul ℤ ℤ (N : ℤ)).lTensor (ZMod M))
    rw [Functor.mapHomologicalComplex_obj_d, resC_d10]
    rfl
  let iso5 : S.moduleCatLeftHomologyData.K ≅ ModuleCat.of ℤ (ZMod (Nat.gcd M N)) := by
    refine LinearEquiv.toModuleIso ?_
    exact (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hSg)).trans (kerLTensor_equiv_gcd M N)
  exact iso1 ≪≫ iso2 ≪≫ iso3 ≪≫ iso4 ≪≫ iso5

end Spt3TorValue

/-! ## Axiom audit for Category L. -/
section CategoryLAxiomAudit
#print axioms Spt3TorValue.crt_glue_finset
#print axioms Spt3TorValue.kerLTensor_equiv_gcd
#print axioms Spt3TorValue.tor1_obj_iso
end CategoryLAxiomAudit


/-! ============================================================================
    Category M — T1-2 (n-fold Tor⊕ split), T1-3 (coefficient bifunctor laws),
    T1-4 (truncated p-adic log gate).  All kernel-verified, sorry-free,
    axiom-free (audited below).

      • T1-2 `Spt3Tor.torBiproduct` — the genuine derived functor carries an
              ARBITRARY finite biproduct to the biproduct:
              `(Tor N n).obj (⨁ᵢ Xᵢ) ≅ ⨁ᵢ (Tor N n).obj Xᵢ`
              (n-fold upgrade of the binary `torBiprod`), via `mapBiproduct` and
              the additive functor `Tor N n` preserving finite biproducts.
      • T1-3 `Spt3Tor.tensorLeftNatTrans_id/comp`, `torCoeffMap_id/comp` — the
              coefficient functoriality laws making `Tor · n` a genuine functor in
              the coefficient (bifunctor `M ↦ Tor M n`): identities and composites
              are preserved.
      • T1-4 `Spt3.padicLogTerm` + `padicLogTerm_valuation_ge` — the truncated
              p-adic logarithm term `Lₙ(u) = (-1)^{n+1} uⁿ/n` as an actual `ℚ`
              function, with the termwise p-adic valuation gate
              `v_p(Lₙ(u)) ≥ k` for `u ∈ pᵏℤ` (i.e. `pᵏ ∣ u`), `n ≥ 1`, `k ≥ 1`.
              This lifts the Nat core `padic_log_term_survives` to the genuine
              `padicValRat`.  (The full-sum bound `v_p(∑ₙ Lₙ) ≥ k` is NOT stated:
              it is false when the truncated sum vanishes, since `v_p(0) = 0`; the
              honest, always-true content is the termwise gate.)
============================================================================ -/

namespace Spt3Tor

open CategoryTheory MonoidalCategory CategoryTheory.Limits

/-- **T1-2 (n-fold Tor of a biproduct).**  The genuine derived functor `Tor N n`
carries an arbitrary finite biproduct to the biproduct of the values:
`(Tor N n).obj (⨁ f) ≅ ⨁ (fun j => (Tor N n).obj (f j))`.  This is the n-fold
upgrade of the binary `torBiprod`, the paper's `Tor(⊕ Bᵢ) ≅ ⊕ Tor(Bᵢ)`. -/
noncomputable def torBiproduct (N : ModZ) (n : ℕ) {J : Type} [Finite J] (f : J → ModZ)
    [HasBiproduct f] [HasBiproduct (fun j => (Tor N n).obj (f j))] :
    (Tor N n).obj (⨁ f) ≅ ⨁ (fun j => (Tor N n).obj (f j)) :=
  (Tor N n).mapBiproduct f

/-- **T1-3 (coefficient identity law).** `tensorLeftNatTrans` preserves identities. -/
theorem tensorLeftNatTrans_id (M : ModZ) :
    tensorLeftNatTrans (𝟙 M) = 𝟙 (MonoidalCategory.tensorLeft M) := by
  apply NatTrans.ext; funext X
  exact id_whiskerRight M X

/-- **T1-3 (coefficient composition law).** `tensorLeftNatTrans` preserves composites. -/
theorem tensorLeftNatTrans_comp {M N P : ModZ} (f : M ⟶ N) (g : N ⟶ P) :
    tensorLeftNatTrans (f ≫ g) = tensorLeftNatTrans f ≫ tensorLeftNatTrans g := by
  apply NatTrans.ext; funext X
  exact comp_whiskerRight f g X

/-- **T1-3 (Tor coefficient functor — identity).** `torCoeffMap (𝟙 M) n = 𝟙 (Tor M n)`. -/
theorem torCoeffMap_id (M : ModZ) (n : ℕ) :
    torCoeffMap (𝟙 M) n = 𝟙 (Tor M n) := by
  show NatTrans.leftDerived (tensorLeftNatTrans (𝟙 M)) n
     = 𝟙 ((MonoidalCategory.tensorLeft M).leftDerived n)
  rw [tensorLeftNatTrans_id, NatTrans.leftDerived_id]

/-- **T1-3 (Tor coefficient functor — composition).**
`torCoeffMap (f ≫ g) n = torCoeffMap f n ≫ torCoeffMap g n`.  Together with
`torCoeffMap_id` this exhibits `M ↦ Tor M n` as a genuine functor in the coefficient
(the second-variable side of the `Tor` bifunctor). -/
theorem torCoeffMap_comp {M N P : ModZ} (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    torCoeffMap (f ≫ g) n = torCoeffMap f n ≫ torCoeffMap g n := by
  show NatTrans.leftDerived (tensorLeftNatTrans (f ≫ g)) n
     = NatTrans.leftDerived (tensorLeftNatTrans f) n ≫ NatTrans.leftDerived (tensorLeftNatTrans g) n
  rw [tensorLeftNatTrans_comp, NatTrans.leftDerived_comp]

end Spt3Tor

namespace Spt3

open scoped BigOperators

/-- **T1-4 (truncated p-adic logarithm term).**  `Lₙ(u) = (-1)^{n+1} · uⁿ / n`, the
`n`-th term of the truncated logarithm `L(u) = ∑_{n≥1} (-1)^{n+1} uⁿ/n`, as a genuine
`ℚ`-valued function of `u : ℤ`. -/
noncomputable def padicLogTerm (u : ℤ) (n : ℕ) : ℚ := (-1) ^ (n + 1) * (u : ℚ) ^ n / (n : ℚ)

/-- **T1-4 (termwise p-adic survival gate).**  For `u ∈ pᵏℤ` (`pᵏ ∣ u`), `n ≥ 1`,
`k ≥ 1`, the `n`-th truncated-log term has p-adic valuation `≥ k`:
`v_p(Lₙ(u)) ≥ k`.  This is the genuine `padicValRat` form of the gate, with the
Nat engine `padic_log_term_survives` supplying `v_p(n) + k ≤ n·k`. -/
theorem padicLogTerm_valuation_ge {p : ℕ} [Fact p.Prime] {u : ℤ} {k n : ℕ}
    (hu : (p : ℤ) ^ k ∣ u) (hu0 : u ≠ 0) (hn : n ≠ 0) (hk : 1 ≤ k) :
    (k : ℤ) ≤ padicValRat p (padicLogTerm u n) := by
  have huq : (u : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hu0
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow : ((u : ℚ) ^ n) ≠ 0 := pow_ne_zero _ huq
  have hsign : ((-1 : ℚ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnum : ((-1 : ℚ) ^ (n + 1) * (u : ℚ) ^ n) ≠ 0 := mul_ne_zero hsign hpow
  have hval : padicValRat p (padicLogTerm u n)
      = (n : ℤ) * (padicValInt p u : ℤ) - (padicValNat p n : ℤ) := by
    show padicValRat p ((-1) ^ (n + 1) * (u : ℚ) ^ n / (n : ℚ)) = _
    rw [padicValRat.div hnum hnq, padicValRat.mul hsign hpow, padicValRat.pow huq,
        padicValRat.pow (show (-1 : ℚ) ≠ 0 by norm_num), padicValRat.neg, padicValRat.one,
        mul_zero, padicValRat.of_int, padicValRat.of_nat]
    ring
  rw [hval]
  have hge : (k : ℤ) ≤ (padicValInt p u : ℤ) := by
    rcases (padicValInt_dvd_iff k u).mp hu with h | h
    · exact absurd h hu0
    · exact_mod_cast h
  have hsurvZ : (padicValNat p n : ℤ) + (k : ℤ) ≤ (n : ℤ) * (k : ℤ) := by
    exact_mod_cast padic_log_term_survives hn hk
  have hnk : (n : ℤ) * (k : ℤ) ≤ (n : ℤ) * (padicValInt p u : ℤ) :=
    mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg n)
  linarith

end Spt3

/-! ## Axiom audit for Category M. -/
section CategoryMAxiomAudit
#print axioms Spt3Tor.torBiproduct
#print axioms Spt3Tor.tensorLeftNatTrans_id
#print axioms Spt3Tor.tensorLeftNatTrans_comp
#print axioms Spt3Tor.torCoeffMap_id
#print axioms Spt3Tor.torCoeffMap_comp
#print axioms Spt3.padicLogTerm_valuation_ge
end CategoryMAxiomAudit


/-! ============================================================================
    Category N — T1-3 (naturality square at degree 0).  Kernel-verified,
    sorry-free, axiom-free (audited below).

      • `Spt3TorNat.fromLeftDerivedZero'_natTrans` and
        `Spt3TorNat.fromLeftDerivedZero_naturality_natTrans` — the functor-naturality
        of `Functor.fromLeftDerivedZero` in the functor argument (a lemma absent from
        Mathlib): for additive `F G : C ⥤ D` and `α : F ⟶ G`,
        `NatTrans.leftDerived α 0 ≫ G.fromLeftDerivedZero = F.fromLeftDerivedZero ≫ α`.
      • `Spt3Tor.torCoeffMap_torZeroIso_naturality` — the paper's naturality square:
        the coefficient map `torCoeffMap f`, the degree-0 iso `torZeroIso`, and the
        tensor natural transformation `tensorLeftNatTrans f` commute:
        `torCoeffMap f 0 ≫ (torZeroIso N).hom = (torZeroIso M).hom ≫ tensorLeftNatTrans f`.
============================================================================ -/

namespace Spt3TorNat

open CategoryTheory CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasProjectiveResolutions C]

omit [HasProjectiveResolutions C] in
/-- **Key lemma.** `ProjectiveResolution.fromLeftDerivedZero'` is natural in the functor:
for `α : F ⟶ G`, the opcycles map of `α` followed by `fromLeftDerivedZero' G` equals
`fromLeftDerivedZero' F` followed by `α`. -/
lemma fromLeftDerivedZero'_natTrans {X : C} (P : ProjectiveResolution X)
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0
        ≫ P.fromLeftDerivedZero' G
      = P.fromLeftDerivedZero' F ≫ α.app X := by
  rw [← cancel_epi (HomologicalComplex.pOpcycles
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) 0),
      HomologicalComplex.p_opcyclesMap_assoc,
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  exact (α.naturality (P.π.f 0)).symm

/-- **T1-3 (functor-naturality of `fromLeftDerivedZero`).**  For additive `F G` and
`α : F ⟶ G`, `NatTrans.leftDerived α 0 ≫ G.fromLeftDerivedZero = F.fromLeftDerivedZero ≫ α`.
This is the functor-variable naturality of the canonical map `leftDerived 0 ⟶ self`,
not currently in Mathlib. -/
theorem fromLeftDerivedZero_naturality_natTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.fromLeftDerivedZero = F.fromLeftDerivedZero ≫ α := by
  ext X
  rw [NatTrans.comp_app, NatTrans.comp_app,
      ProjectiveResolution.leftDerived_app_eq α (projectiveResolution X) 0,
      ProjectiveResolution.fromLeftDerivedZero_eq (projectiveResolution X) G,
      ProjectiveResolution.fromLeftDerivedZero_eq (projectiveResolution X) F]
  set P := projectiveResolution X with hP
  set φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex with hφ
  have hnat : HomologicalComplex.homologyMap φ 0 ≫
        (ChainComplex.isoHomologyι₀
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom
      = (ChainComplex.isoHomologyι₀
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom ≫
        HomologicalComplex.opcyclesMap φ 0 := by
    rw [← cancel_epi (ChainComplex.isoHomologyι₀
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).inv]
    simp
  have key : HomologicalComplex.opcyclesMap φ 0 ≫ P.fromLeftDerivedZero' G
      = P.fromLeftDerivedZero' F ≫ α.app X := fromLeftDerivedZero'_natTrans P α
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left,
    HomologicalComplex.homologyFunctor_map]
  simp [reassoc_of% hnat, reassoc_of% key, key]

end Spt3TorNat

namespace Spt3Tor

open CategoryTheory MonoidalCategory CategoryTheory.Limits

/-- **T1-3 (the naturality square, paper form).**  The coefficient map `torCoeffMap f`,
the derived-functor degree-0 iso `torZeroIso`, and the tensor natural transformation
`tensorLeftNatTrans f` commute:
`torCoeffMap f 0 ≫ (torZeroIso N).hom = (torZeroIso M).hom ≫ tensorLeftNatTrans f`. -/
theorem torCoeffMap_torZeroIso_naturality {M N : ModZ} (f : M ⟶ N) :
    torCoeffMap f 0 ≫ (torZeroIso N).hom
      = (torZeroIso M).hom ≫ tensorLeftNatTrans f := by
  show NatTrans.leftDerived (tensorLeftNatTrans f) 0
        ≫ (MonoidalCategory.tensorLeft N).fromLeftDerivedZero
      = (MonoidalCategory.tensorLeft M).fromLeftDerivedZero ≫ tensorLeftNatTrans f
  exact Spt3TorNat.fromLeftDerivedZero_naturality_natTrans (tensorLeftNatTrans f)

end Spt3Tor

/-! ## Axiom audit for Category N. -/
section CategoryNAxiomAudit
#print axioms Spt3TorNat.fromLeftDerivedZero'_natTrans
#print axioms Spt3TorNat.fromLeftDerivedZero_naturality_natTrans
#print axioms Spt3Tor.torCoeffMap_torZeroIso_naturality
end CategoryNAxiomAudit


/-! ============================================================================
    Category O — T2-3, T3-1(b), T3-3, T3-4.  Kernel-verified, sorry-free,
    axiom-free (audited below).

      • T3-1(b) `Spt3Sheaf.constLayer` — CONCRETE arithmetic layer subfunctors of the
            ambient `B` (the constant presheaf `ℕ`): each arithmetic predicate
            `P : ℕ → Prop` yields a genuine `Subfunctor B` (restriction is the identity
            on the constant presheaf, so any constant predicate is restriction-stable).
            The four decision layers are now concrete (`Fnum/Fmod/Fpadic/FEC_sheaf`),
            removing the "arbitrary `Subfunctor` variable, no content" gap.  The amalgam
            of the four concrete layers has sections EXACTLY the primes
            (`amalgam_concrete_prime_iff`), via `concrete_four_layers_iff_prime`.
      • T2-3 `Spt3Sheaf.amalgam_no_bad_primes_arith` + `coprimeLayer_proper` — the
            "no bad primes" statement with genuine ARITHMETIC content: the coprimality
            gate `coprimeLayer N` is the full subfunctor `⊤` iff there are no bad primes
            (`N = 1`), and is a PROPER subfunctor when `1 < N` (it really excludes the
            multiples of the bad primes).  Replaces the vacuous `⊤⊓⊤⊓⊤⊓⊤ = ⊤`.
      • T3-4 `Spt3.ec_certification_chain` — the EC discriminant→nonsingular chain on
            `D(Δ)`: `p ∤ Δ(W) ⟹ Δ(W mod p) ≠ 0 ∧ (every reduced solution is nonsingular)`
            — good reduction at every prime off the discriminant, connecting the isolated
            `ec_good_reduction` into the gate the certification uses.
      • T3-3 `Spt3.ab_linearization_sum` — the AB-linearization congruence core: a linear
            combination `∑ⱼ aⱼ φⱼ` is `≡ target (mod pᵏ)` whenever each term is termwise
            congruent and the targets sum to `target`.  This is the structural telescoping
            identity behind `∑ aⱼ φⱼ(A) ≡ log X − pⁿ log A (mod pᵏ)`.
============================================================================ -/

namespace Spt3Sheaf

open CategoryTheory TopologicalSpace

/-- **T3-1(b) (concrete arithmetic layer).**  An arithmetic predicate `P : ℕ → Prop`
defines a genuine subfunctor of the constant ambient presheaf `B = ℕ`: on every open the
section set is `{x | P x}`, and since restriction along `B` is the identity, the predicate
is automatically restriction-stable. -/
def constLayer (P : ℕ → Prop) : Subfunctor B where
  obj _ := {x | P x}
  map _ _ hx := hx

@[simp] theorem constLayer_obj (P : ℕ → Prop) (U : (Opens S)ᵒᵖ) :
    (constLayer P).obj U = {x | P x} := rfl

/-- The four DECISION LAYERS as concrete arithmetic subfunctors (matching the
verified `Spt3Cert` predicates), no longer arbitrary variables. -/
def Fnum_sheaf : Subfunctor B := constLayer Spt3Cert.Fnum_layer
def Fmod_sheaf : Subfunctor B := constLayer Spt3Cert.Fmod_layer
def Fpadic_sheaf : Subfunctor B := constLayer Spt3Cert.Fpadic_layer
def FEC_sheaf : Subfunctor B := constLayer Spt3Cert.FEC_layer

/-- The amalgam of four concrete layers is the concrete layer of their conjunction. -/
theorem amalgam_concrete_eq (P₁ P₂ P₃ P₄ : ℕ → Prop) :
    amalgam (constLayer P₁) (constLayer P₂) (constLayer P₃) (constLayer P₄)
      = constLayer (fun X => P₁ X ∧ P₂ X ∧ P₃ X ∧ P₄ X) := by
  ext U x
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- **T3-1(b) (concrete amalgam certifies primality).**  The amalgam of the four concrete
arithmetic layers has, on every open, section set EXACTLY the primes:
`s ∈ Γ(U, F) ↔ s prime`.  This is the genuine arithmetic content the abstract amalgam
lacked — the four-layer sheaf amalgam over `Spec ℤ` detects exactly the primes. -/
theorem amalgam_concrete_prime_iff {U : (Opens S)ᵒᵖ} (s : B.obj U) :
    s ∈ (amalgam Fnum_sheaf Fmod_sheaf Fpadic_sheaf FEC_sheaf).obj U ↔ Nat.Prime s := by
  rw [mem_amalgam]
  exact (Spt3FinalChecklist.concrete_four_layers_iff_prime s).symm

/-- **T2-3 (coprimality gate).**  The arithmetic "no bad primes" gate `coprimeLayer N`:
sections are the integers coprime to `N`. -/
def coprimeLayer (N : ℕ) : Subfunctor B := constLayer (fun X => Nat.Coprime X N)

/-- **T2-3 (no bad primes ⟹ full).**  With no bad primes (`N = 1`) the coprimality gate
admits everything: `coprimeLayer 1 = ⊤`. -/
theorem coprimeLayer_one : coprimeLayer 1 = ⊤ := by
  ext U x
  simp only [coprimeLayer, constLayer_obj, Set.mem_setOf_eq, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Nat.coprime_one_right x

/-- **T2-3 (the amalgam in the normalized regime, with ARITHMETIC content).**  In the
normalized "no bad primes" profile the four coprimality gates are each full, hence the
amalgam is full — but now `coprimeLayer 1 = ⊤` is the genuine arithmetic statement
"coprime to 1", not a vacuous `⊤`. -/
theorem amalgam_no_bad_primes_arith :
    amalgam (coprimeLayer 1) (coprimeLayer 1) (coprimeLayer 1) (coprimeLayer 1)
      = (⊤ : Subfunctor B) := by
  simp only [amalgam, coprimeLayer_one, inf_top_eq]

/-- **T2-3 (bad primes ⟹ proper).**  When there IS a bad prime (`1 < N`) the gate is a
PROPER subfunctor: it excludes `N` itself (and every multiple of a common prime), so the
gate genuinely restricts.  This is the arithmetic content the old `⊤⊓⊤⊓⊤⊓⊤=⊤` lacked. -/
theorem coprimeLayer_proper {N : ℕ} (hN : 1 < N) : coprimeLayer N ≠ (⊤ : Subfunctor B) := by
  intro h
  have hmem : N ∈ (coprimeLayer N).obj (Opposite.op ⊤) := by rw [h]; trivial
  have hcop : Nat.Coprime N N := hmem
  have hN1 : N = 1 := by simpa [Nat.Coprime, Nat.gcd_self] using hcop
  omega

end Spt3Sheaf

namespace Spt3

open scoped BigOperators

/-- **T3-4 (EC discriminant → nonsingular chain, on `D(Δ)`).**  If `p ∤ Δ(W)` then the
reduced discriminant `Δ(W mod p)` is nonzero AND every solution of the reduced Weierstrass
equation is nonsingular: the curve has good (smooth) reduction at `p`.  This assembles the
isolated `ec_good_reduction` into the discriminant-gate chain the certification uses on the
principal open `D(Δ)`. -/
theorem ec_certification_chain {W : WeierstrassCurve ℤ} {p : ℕ} [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ W.Δ) :
    (W.map (Int.castRingHom (ZMod p))).Δ ≠ 0 ∧
      ∀ x y : ZMod p, (W.map (Int.castRingHom (ZMod p))).toAffine.Equation x y ↔
        (W.map (Int.castRingHom (ZMod p))).toAffine.Nonsingular x y := by
  refine ⟨?_, fun x y => ec_good_reduction hp x y⟩
  rw [WeierstrassCurve.map_Δ]
  intro hc
  exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd W.Δ p).mp hc)

/-- **T3-3 (AB-linearization congruence core).**  A linear combination `∑ⱼ aⱼ φⱼ` is
congruent to `target` modulo `pᵏ` whenever each term `aⱼ φⱼ` is congruent to `tⱼ` and the
`tⱼ` sum to `target`.  This is the structural telescoping identity behind the paper's
`∑ aⱼ φⱼ(A) ≡ log X − pⁿ log A (mod pᵏ)` AB-linearization (the per-term congruences come
from the truncated-log term bound `padicLogTerm_valuation_ge`). -/
theorem ab_linearization_sum {ι : Type*} (J : Finset ι) (p k : ℕ) (a φ t : ι → ℤ)
    (target : ℤ)
    (hterm : ∀ j ∈ J, a j * φ j ≡ t j [ZMOD ((p : ℤ) ^ k)])
    (hsum : ∑ j ∈ J, t j = target) :
    (∑ j ∈ J, a j * φ j) ≡ target [ZMOD ((p : ℤ) ^ k)] := by
  subst hsum
  rw [Int.modEq_iff_dvd, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun j hj => Int.modEq_iff_dvd.mp (hterm j hj)

end Spt3

/-! ## Axiom audit for Category O. -/
section CategoryOAxiomAudit
#print axioms Spt3Sheaf.constLayer
#print axioms Spt3Sheaf.amalgam_concrete_eq
#print axioms Spt3Sheaf.amalgam_concrete_prime_iff
#print axioms Spt3Sheaf.coprimeLayer_one
#print axioms Spt3Sheaf.amalgam_no_bad_primes_arith
#print axioms Spt3Sheaf.coprimeLayer_proper
#print axioms Spt3.ec_certification_chain
#print axioms Spt3.ab_linearization_sum
end CategoryOAxiomAudit

/-! ============================================================================
    Category P — last-mile targets from the B-audit, stated without pretending away
    the genuinely analytic/categorical inputs.

      • P1  the empty-open repair is encoded as `RepointedSection`: over `∅` there is
             only the distinguished section, while over a nonempty open the sections
             are exactly the arithmetic predicate.
      • P2  the H-5 reverse implication is named directly: projective differentials
             plus vanishing `H¹Cotangent` produce `FormallySmooth`.
      • P3  the true p-adic logarithm is defined as the `tsum` of the logarithm
             series on `1 + pℤ_p`; its partial-sum convergence is proved from
             the actual `Summable` hypothesis, and `log(1)=0` is proved directly.
      • P4  the AB-linearization statement now contains the actual displayed
             `φ_j(A) = M S_j(A)/(gcd(j!,m)Y)` term, not only an anonymous `φ`.

    Current Mathlib gives the p-adic fields/integers and the termwise valuation
    tools used above.  The remaining analytic hard parts are exactly the global
    summability/homomorphism/Lipschitz estimates for the `tsum` series; no axiom
    or structure field below pretends those are already constructed.
============================================================================ -/

namespace Spt3Sheaf

/-- Empty-open repaired constant sections for an arithmetic predicate.  The value
`none` is forced precisely on the empty open; on nonempty opens the value is
`some n` with `P n`. -/
def RepointedSection (P : ℕ → Prop) (U : (Opens S)ᵒᵖ) : Type :=
  {o : Option ℕ // (o = none ↔ U.unop = ⊥) ∧ ∀ n, o = some n → P n}

/-- The repaired fibre over `∅` is a singleton. -/
theorem repointedSection_empty_subsingleton (P : ℕ → Prop) {U : (Opens S)ᵒᵖ}
    (hU : U.unop = ⊥) : Subsingleton (RepointedSection P U) := by
  refine ⟨fun x y => ?_⟩
  apply Subtype.ext
  have hx : x.1 = none := x.2.1.mpr hU
  have hy : y.1 = none := y.2.1.mpr hU
  rw [hx, hy]

/-- On a nonempty open, repaired constant sections are exactly the predicate
sections. -/
noncomputable def repointedSection_nonempty_equiv (P : ℕ → Prop)
    {U : (Opens S)ᵒᵖ} (hU : U.unop ≠ ⊥) :
    RepointedSection P U ≃ {n : ℕ // P n} where
  toFun x := by
    cases hx : x.1 with
    | none => exact False.elim (hU (x.2.1.mp hx))
    | some n => exact ⟨n, x.2.2 n hx⟩
  invFun n :=
    ⟨some n.1,
      ⟨by
        constructor
        · intro hnone
          cases hnone
        · intro hbot
          exact False.elim (hU hbot),
       by
        intro m hm
        have hm' : n.1 = m := Option.some.inj hm
        simpa [← hm'] using n.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    cases hx : x.1 with
    | none => exact False.elim (hU (x.2.1.mp hx))
    | some n => rfl
  right_inv n := by
    ext
    rfl

/-- The repaired primality layer has prime sections on every nonempty open. -/
noncomputable def repointedPrimeSections_nonempty_equiv
    {U : (Opens S)ᵒᵖ} (hU : U.unop ≠ ⊥) :
    RepointedSection Nat.Prime U ≃ {n : ℕ // Nat.Prime n} :=
  repointedSection_nonempty_equiv Nat.Prime hU

end Spt3Sheaf

namespace Spt3

open scoped BigOperators

/-- **P2 / H-5 reverse direction.**  The exact Mathlib algebraic hypothesis needed
for the reverse implication: projectivity of Kähler differentials together with
vanishing first cotangent cohomology is formal smoothness. -/
theorem formallySmooth_of_projective_h1Cotangent
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (hΩ : Module.Projective A (KaehlerDifferential R A))
    (hH1 : Subsingleton (Algebra.H1Cotangent R A)) :
    Algebra.FormallySmooth R A :=
  ⟨hΩ, hH1⟩

/-- The multiplicative one-neighbourhood `1 + pℤ_p`, represented inside `ℤ_p`.
The logarithm package below maps this domain to `ℚ_p`. -/
abbrev PadicOnePlusP (p : ℕ) [Fact p.Prime] : Type :=
  {x : ℤ_[p] // ∃ u : ℤ_[p], x = 1 + (p : ℤ_[p]) * u}

instance (p : ℕ) [Fact p.Prime] : One (PadicOnePlusP p) where
  one := ⟨1, ⟨0, by simp⟩⟩

instance (p : ℕ) [Fact p.Prime] : Mul (PadicOnePlusP p) where
  mul x y := by
    rcases x.2 with ⟨a, rfl⟩
    rcases y.2 with ⟨b, rfl⟩
    refine ⟨(1 + (p : ℤ_[p]) * a) * (1 + (p : ℤ_[p]) * b),
      ⟨a + b + (p : ℤ_[p]) * a * b, ?_⟩⟩
    ring

@[simp] theorem padicOnePlusP_one_val (p : ℕ) [Fact p.Prime] :
    ((1 : PadicOnePlusP p).1 : ℤ_[p]) = 1 := rfl

@[simp] theorem padicOnePlusP_mul_val (p : ℕ) [Fact p.Prime]
    (x y : PadicOnePlusP p) : (x * y).1 = x.1 * y.1 := by
  rcases x.2 with ⟨a, rfl⟩
  rcases y.2 with ⟨b, rfl⟩
  rfl

/-- The `n`th p-adic logarithm series term in `ℚ_p`, indexed from zero:
`(-1)^n u^(n+1)/(n+1)`. -/
noncomputable def padicLogQpTerm {p : ℕ} [Fact p.Prime] (u : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1 : ℚ_[p]) ^ n * u ^ (n + 1) / ((n + 1 : ℕ) : ℚ_[p])

/-- The finite partial sums of the genuine p-adic logarithm series. -/
noncomputable def padicLogQpPartial {p : ℕ} [Fact p.Prime] (u : ℚ_[p]) (N : ℕ) : ℚ_[p] :=
  ∑ n in Finset.range N, padicLogQpTerm u n

/-- The genuine p-adic logarithm series on `1 + pℤ_p`, defined as an infinite sum
in `ℚ_p`.  The convergence theorem below is deliberately stated with the real
`Summable` hypothesis rather than hidden in a structure field. -/
noncomputable def padicLogSeries {p : ℕ} [Fact p.Prime] (x : PadicOnePlusP p) : ℚ_[p] :=
  ∑' n : ℕ, padicLogQpTerm (((x.1 : ℤ_[p]) : ℚ_[p]) - 1) n

@[simp] theorem padicLogQpTerm_zero {p : ℕ} [Fact p.Prime] (n : ℕ) :
    padicLogQpTerm (0 : ℚ_[p]) n = 0 := by
  simp [padicLogQpTerm]

/-- If the logarithm series is summable, its finite partial sums converge to
`padicLogSeries`.  This is the actual `tsum` bridge needed before proving the
homomorphism and Lipschitz estimates. -/
theorem padicLogSeries_tendsto_partial {p : ℕ} [Fact p.Prime] (x : PadicOnePlusP p)
    (hsum : Summable fun n : ℕ =>
      padicLogQpTerm (((x.1 : ℤ_[p]) : ℚ_[p]) - 1) n) :
    Filter.Tendsto
      (fun N : ℕ => padicLogQpPartial (((x.1 : ℤ_[p]) : ℚ_[p]) - 1) N)
      Filter.atTop
      (nhds (padicLogSeries x)) := by
  simpa [padicLogSeries, padicLogQpPartial] using hsum.hasSum.tendsto_sum_nat

/-- The series definition gives `log_p(1)=0` without any extra analytic input. -/
@[simp] theorem padicLogSeries_one {p : ℕ} [Fact p.Prime] :
    padicLogSeries (1 : PadicOnePlusP p) = 0 := by
  simp [padicLogSeries]

/-- The partial sums at `1` are constantly zero, hence converge to `0`. -/
theorem padicLogSeries_tendsto_partial_one {p : ℕ} [Fact p.Prime] :
    Filter.Tendsto
      (fun N : ℕ => padicLogQpPartial ((((1 : PadicOnePlusP p).1 : ℤ_[p]) : ℚ_[p]) - 1) N)
      Filter.atTop
      (nhds (0 : ℚ_[p])) := by
  simpa [padicLogQpPartial] using
    (show Filter.Tendsto (fun _ : ℕ => (0 : ℚ_[p])) Filter.atTop (nhds 0) from
      tendsto_const_nhds)

/-- Once the analytic Cauchy-product identity for the p-adic logarithm series is
proved, the homomorphism law follows immediately for the `tsum` definition.  This
is intentionally not a structure-field projection: the hypothesis is the exact
remaining analytic identity. -/
theorem padicLogSeries_map_mul_of_tsum_identity {p : ℕ} [Fact p.Prime]
    (x y : PadicOnePlusP p)
    (h :
      (∑' n : ℕ, padicLogQpTerm ((((x * y).1 : ℤ_[p]) : ℚ_[p]) - 1) n)
        =
      (∑' n : ℕ, padicLogQpTerm (((x.1 : ℤ_[p]) : ℚ_[p]) - 1) n)
        +
      (∑' n : ℕ, padicLogQpTerm (((y.1 : ℤ_[p]) : ℚ_[p]) - 1) n)) :
    padicLogSeries (x * y) = padicLogSeries x + padicLogSeries y := by
  simpa [padicLogSeries] using h

/-- The displayed AB-linearization coefficient
`φ_j(A) = M S_j(A)/(gcd(j!,m)Y)`, with `idx j` carrying the displayed natural
number `j` when the finite index type is not literally `ℕ`. -/
noncomputable def abPhiInt {ι : Type*} (M Y : ℤ) (m : ℕ)
    (idx : ι → ℕ) (S : ι → ℤ) (j : ι) : ℤ :=
  M * S j / ((Nat.gcd (Nat.factorial (idx j)) m : ℤ) * Y)

/-- The integral target form of `log X - p^n log A` used by the modular
AB-linearization congruence. -/
def abLogTargetInt (p n : ℕ) (logX logA : ℤ) : ℤ :=
  logX - (p : ℤ) ^ n * logA

/-- **P4 / AB-linearization with the actual displayed `φ_j(A)`.**  Once each
coefficient term built from `M S_j(A)/(gcd(j!,m)Y)` matches the corresponding
integral logarithm term modulo `p^k`, and those logarithm terms telescope to
`log X - p^n log A`, the whole AB sum has the advertised congruence. -/
theorem ab_linearization_identity {ι : Type*} (J : Finset ι)
    (p k n m : ℕ) (M Y : ℤ) (idx : ι → ℕ) (S a logTerm : ι → ℤ)
    (logX logA : ℤ)
    (hterm : ∀ j ∈ J,
      a j * abPhiInt M Y m idx S j ≡ logTerm j [ZMOD ((p : ℤ) ^ k)])
    (htelescope : ∑ j ∈ J, logTerm j = abLogTargetInt p n logX logA) :
    (∑ j ∈ J, a j * abPhiInt M Y m idx S j)
      ≡ abLogTargetInt p n logX logA [ZMOD ((p : ℤ) ^ k)] :=
  ab_linearization_sum J p k a (abPhiInt M Y m idx S) logTerm
    (abLogTargetInt p n logX logA) hterm htelescope

end Spt3

/-! ## Axiom audit for Category P. -/
section CategoryPAxiomAudit
#print axioms Spt3Sheaf.repointedSection_empty_subsingleton
#print axioms Spt3Sheaf.repointedSection_nonempty_equiv
#print axioms Spt3.formallySmooth_of_projective_h1Cotangent
#print axioms Spt3.padicLogSeries_tendsto_partial
#print axioms Spt3.padicLogSeries_one
#print axioms Spt3.padicLogSeries_map_mul_of_tsum_identity
#print axioms Spt3.ab_linearization_identity
end CategoryPAxiomAudit
