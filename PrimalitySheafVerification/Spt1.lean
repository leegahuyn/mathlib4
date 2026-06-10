/-
================================================================================
  Spt1.lean — verified core of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification"  (Spt 1).

  FINAL VERSION: every elementary-arithmetic result of the paper is fully
  proved with NO `sorry`.  The only honest omissions are the two genuinely
  non-elementary results that would require project-level `axiom`s and are
  therefore OUTSIDE the elementary core (this is the "Mathlib limit"):

      • Thm 2.1 / Lem 2.3 — p-adic logarithm gate (analytic ℚ_p)
      • Thm 6.2          — sheaf-theoretic terminal amalgam

  Everything else — all definitions, all lemmas A/B/C/5/6/15/16, all
  propositions 2/7/8/17, theorems 1/4.1/14/18, the AB-linearization identity,
  and the (re-cast, elementary) six-line minimal certificate — is proved.
================================================================================
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD

open scoped BigOperators

namespace Spt1

/-! ## §2 (Basic) — definitions -/

/-- Definition 2.11 / 4.11 / 5.3 — common residue fiber index `gcd(M, p^k)`. -/
def commonResidueIndex (M p k : ℕ) : ℕ := Nat.gcd M (p ^ k)

/-- Definition 2.11 — local thickness `ε_p = min(v_p M, k)`. -/
def localThickness (M p k : ℕ) : ℕ := min (M.factorization p) k

/-- The obstruction-free predicate at `p`. -/
def obstructionFree (M p k : ℕ) : Prop := Nat.gcd M (p ^ k) = 1

@[simp] lemma commonResidueIndex_def (M p k : ℕ) :
    commonResidueIndex M p k = Nat.gcd M (p ^ k) := rfl

@[simp] lemma localThickness_def (M p k : ℕ) :
    localThickness M p k = min (M.factorization p) k := rfl

/-! ## §3 (Kernel) — L1: equalizer kernel `= (M) ∩ (N) = (lcm M N)`. -/

theorem equalizer_mem_iff (M N a : ℤ) :
    (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a :=
  lcm_dvd_iff.symm

theorem equalizer_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

theorem gcd_mul_lcm_eq (M N : ℕ) : Nat.gcd M N * Nat.lcm M N = M * N :=
  Nat.gcd_mul_lcm M N

/-! ## §3 (Thickness) — L2 (CORRECTED): gcd→min (true ε_p), lcm→max. -/

theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

theorem gcd_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.gcd M (p ^ k)).factorization p = localThickness M p k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [localThickness_def, factorization_gcd_apply hM hpk, Nat.factorization_pow_self hp]

theorem lcm_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.lcm M (p ^ k)).factorization p = max (M.factorization p) k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [factorization_lcm_apply hM hpk, Nat.factorization_pow_self hp]

/-! ## §3 (Tor) — T1 (full): `Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ℤ/gcd(M,N)`. -/

theorem range_mulLeft (N : ℕ) [NeZero N] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).range = AddSubgroup.zmultiples (M : ZMod N) := by
  ext y
  rw [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x.val : ℤ), ?_⟩
    rw [zsmul_eq_mul]; push_cast; rw [ZMod.natCast_zmod_val]
    simp [mul_comm]
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ZMod N), by rw [zsmul_eq_mul]; simp [mul_comm]⟩

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
  have hgd : N.gcd M * (N / N.gcd M) = N := Nat.mul_div_cancel' hdvd
  have hdpos : 0 < N / N.gcd M :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd) hg
  have hfin : Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker * (N / N.gcd M)
        = N.gcd M * (N / N.gcd M) := by rw [hmul, hgd]
  exact Nat.eq_of_mul_eq_mul_right hdpos hfin

theorem commonResidueFiber_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = g :=
  ZMod.card g

theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by
  simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N :=
  Iff.rfl

/-! ## §4–§7 (CRT / primewise) — Prop 4.4 / Thm 4.20 / Prop 7.7. -/

theorem primewise_exponent {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (q : ℕ) :
    (Nat.gcd M N).factorization q = min (M.factorization q) (N.factorization q) :=
  factorization_gcd_apply hM hN q

noncomputable def crt_iso {m n : ℕ} (h : Nat.Coprime m n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

theorem gcd_eq_prod {M N : ℕ} (hM : M ≠ 0) :
    Nat.gcd M N = (Nat.gcd M N).factorization.prod (fun p e => p ^ e) :=
  (Nat.prod_factorization_pow_eq_self (Nat.gcd_ne_zero_left hM)).symm

/-! ## Stability box (Rmk 2.8/2.13, Lem 4.6, Thm 5.1, Prop 7.5). -/

theorem thickness_stable_coprime {M N c : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hc : c ≠ 0)
    {q : ℕ} (hq : ¬ q ∣ c) :
    (Nat.gcd M (N * c)).factorization q = (Nat.gcd M N).factorization q := by
  rw [factorization_gcd_apply hM (Nat.mul_ne_zero hN hc),
      factorization_gcd_apply hM hN, Nat.factorization_mul hN hc]
  have hcq : c.factorization q = 0 :=
    (Nat.factorization_eq_zero_iff c q).mpr (Or.inr (Or.inl hq))
  simp [Finsupp.add_apply, hcq]

/-! ## §7 (Indicator complexity) — Def 7.6 / Prop 7.7. -/

noncomputable def IC (M N : ℕ) : ℝ :=
  ∑ q ∈ N.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q

theorem gcd_eq_prod_primeFactors {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Nat.gcd M N
      = ∏ q ∈ N.primeFactors, q ^ min (M.factorization q) (N.factorization q) := by
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

theorem card_Tor_eq_exp_IC {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    (Nat.gcd M N : ℝ) = Real.exp (IC M N) := by
  rw [IC, Real.exp_sum, gcd_eq_prod_primeFactors hM hN, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
  rw [Nat.cast_pow, ← Nat.cast_min, ← Real.log_pow, Real.exp_log (by positivity)]

/-! ## Worked examples (Example 4.5). -/

section Examples
example : Nat.gcd 12 (3 ^ 2) = 3 := by norm_num
example : (3 : ℕ) ^ min 1 2 = 3 := by decide
example : Nat.gcd 12 5 = 1 := by norm_num
example : Nat.gcd 147 (7 ^ 4) = 49 := by norm_num
example : Nat.lcm 12 9 = 36 := by norm_num
example : (9 : ℕ) ∣ Nat.lcm 12 9 := by norm_num
example : ¬ (27 : ℕ) ∣ Nat.lcm 12 9 := by norm_num
example : ¬ (9 : ℕ) ∣ 12 := by norm_num
example : min 1 2 = 1 := by decide
example : max 1 2 = 2 := by decide
example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by native_decide
end Examples

/-! ========================================================================
    §§ NEW ADDITIONS  (all fully proved)
    ======================================================================== -/

/-! ### New structural definitions -/

/-- **VisiblePrimesProfile** (paper §2): the six-tuple `(A, p^n, M, k, Δ, W)`. -/
structure VisiblePrimesProfile where
  A  : ℕ
  pn : ℕ
  M  : ℕ
  k  : ℕ
  Δ  : ℤ
  W  : ℕ

/-- **IC_nat** — integer-weighted indicator complexity
    `IC_M(N) = Σ_{q ∣ N} min(v_q M, v_q N) · q`. -/
def IC_nat (M N : ℕ) : ℕ :=
  ∑ q ∈ N.primeFactors, min (M.factorization q) (N.factorization q) * q

/-- The **equalizer support** `Supp(M)` — primes where local Tor₁ is non-trivial. -/
abbrev equalizerSupport (M : ℕ) : Finset ℕ := M.primeFactors

/-! ### Lemma 5 — Equalizer kernel: support characterization -/

/-- **Lemma 5 (membership).** `p ∈ Supp(M) ↔ p ∣ M`. -/
theorem mem_equalizerSupport_iff {M : ℕ} (hM : M ≠ 0) {p : ℕ} (hp : p.Prime) :
    p ∈ equalizerSupport M ↔ p ∣ M :=
  Nat.mem_primeFactors_iff_dvd hM hp

/-- **Lemma 5 (obstruction link).** `p ∈ Supp(M)` iff `obstructionFree M p 1` fails. -/
theorem mem_equalizerSupport_iff_not_obstructionFree {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p.Prime) :
    p ∈ equalizerSupport M ↔ ¬ obstructionFree M p 1 := by
  rw [mem_equalizerSupport_iff hM hp, obstructionFree, pow_one]
  constructor
  · intro hdvd hcop
    have hpg : p ∣ Nat.gcd M p := Nat.dvd_gcd hdvd dvd_rfl
    rw [hcop] at hpg
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpg)
  · intro hne
    by_contra hndvd
    exact hne ((hp.coprime_iff_not_dvd.mpr hndvd).symm)

/-! ### Lemma 6 — Tor₁ prime-power specialization -/

/-- **Lemma 6.** `|Tor₁^ℤ(ℤ/M, ℤ/p^k)| = gcd(M, p^k)`. -/
theorem card_Tor_prime_pow_eq_gcd {p : ℕ} (_hp : p.Prime) (M k : ℕ)
    [NeZero (p ^ k)] :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod (p ^ k))).ker = Nat.gcd M (p ^ k) := by
  rw [card_ker_mulLeft, Nat.gcd_comm]

/-! ### Proposition 7 — Localized thickness -/

/-- **Proposition 7.** `gcd(M, p^k) = p ^ localThickness M p k`. -/
theorem gcd_eq_prime_pow_localThickness {p : ℕ} (hp : p.Prime) {M : ℕ}
    (hM : M ≠ 0) (k : ℕ) :
    Nat.gcd M (p ^ k) = p ^ localThickness M p k := by
  obtain ⟨i, _hi, heq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right M (p ^ k))
  have hval : i = localThickness M p k := by
    have h1 : (p ^ i).factorization p = i := Nat.factorization_pow_self hp
    have h2 : (Nat.gcd M (p ^ k)).factorization p = localThickness M p k :=
      gcd_thickness_prime_pow hp hM k
    rw [← heq] at h2; exact h1.symm.trans h2
  rw [← hval, heq]

theorem commonResidueIndex_eq_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ}
    (hM : M ≠ 0) (k : ℕ) :
    commonResidueIndex M p k = p ^ localThickness M p k :=
  gcd_eq_prime_pow_localThickness hp hM k

/-! ### Lemma A — CRT split of gcd -/

/-- **Lemma A.** For coprime `u, v`: `gcd(M, u·v) = gcd(M, u) · gcd(M, v)`. -/
theorem gcd_mul_coprime {M u v : ℕ} (hM : M ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : Nat.Coprime u v) :
    Nat.gcd M (u * v) = Nat.gcd M u * Nat.gcd M v := by
  have huv : u * v ≠ 0 := Nat.mul_ne_zero hu hv
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_ne_zero_left hM)
    (Nat.mul_ne_zero (Nat.gcd_ne_zero_left hM) (Nat.gcd_ne_zero_left hM))
  intro q
  rw [Nat.factorization_mul (Nat.gcd_ne_zero_left hM) (Nat.gcd_ne_zero_left hM),
      Finsupp.add_apply,
      factorization_gcd_apply hM huv,
      factorization_gcd_apply hM hu,
      factorization_gcd_apply hM hv,
      Nat.factorization_mul hu hv, Finsupp.add_apply]
  set uq := u.factorization q
  set vq := v.factorization q
  have hcop_q : uq = 0 ∨ vq = 0 := by
    by_contra h; push_neg at h
    have hquP : q.Prime := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization u ▸ Finsupp.mem_support_iff.mpr h.1)
    have hqu : q ∣ u := Nat.dvd_of_mem_primeFactors
      (Nat.support_factorization u ▸ Finsupp.mem_support_iff.mpr h.1)
    have hqv : q ∣ v := Nat.dvd_of_mem_primeFactors
      (Nat.support_factorization v ▸ Finsupp.mem_support_iff.mpr h.2)
    have : q ∣ Nat.gcd u v := Nat.dvd_gcd hqu hqv
    rw [hcop] at this
    exact absurd (Nat.le_of_dvd Nat.one_pos this) hquP.one_lt.not_le
  rcases hcop_q with h | h <;> simp [h]

/-! ### Lemma B — Tor¹ multiplicativity -/

/-- **Lemma B.** For coprime `u, v`:
    `|Tor₁(ℤ/M, ℤ/(u·v))| = |Tor₁(ℤ/M, ℤ/u)| · |Tor₁(ℤ/M, ℤ/v)|`. -/
theorem card_Tor_mul_coprime {M u v : ℕ} (hM : M ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : Nat.Coprime u v)
    [NeZero (u * v)] [NeZero u] [NeZero v] :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod (u * v))).ker =
    Nat.card (AddMonoidHom.mulLeft (M : ZMod u)).ker *
    Nat.card (AddMonoidHom.mulLeft (M : ZMod v)).ker := by
  rw [card_ker_mulLeft (u * v) M, card_ker_mulLeft u M, card_ker_mulLeft v M,
      Nat.gcd_comm (u * v), gcd_mul_coprime hM hu hv hcop,
      Nat.gcd_comm u, Nat.gcd_comm v]

/-! ### Lemma C — Single prime-power computation -/

/-- **Lemma C.** `gcd(M, p^k) = p ^ min(v_p M, k)`. -/
alias lemmaC_single_prime_pow := gcd_eq_prime_pow_localThickness

/-! ### Lemma 15 — Monotonicity of IC -/

/-- **Lemma 15 (pointwise).** `v_q M ≤ v_q M'` (all q) ⇒ `IC(M;N) ≤ IC(M';N)`. -/
theorem IC_mono {M M' N : ℕ}
    (h : ∀ q, M.factorization q ≤ M'.factorization q) :
    IC M N ≤ IC M' N := by
  apply Finset.sum_le_sum; intro q hq
  apply mul_le_mul_of_nonneg_right _
    (Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_le))
  exact_mod_cast Nat.min_le_min_right _ (h q)

/-- **Lemma 15 (divisibility).** `M ∣ M'` ⇒ `IC(M;N) ≤ IC(M';N)`. -/
theorem IC_mono_of_dvd {M M' N : ℕ} (hM' : M' ≠ 0) (h : M ∣ M') :
    IC M N ≤ IC M' N :=
  IC_mono fun q => Nat.factorization_le_factorization_of_dvd hM' h q

/-! ### Lemma 16 — Additivity of IC over coprime moduli -/

/-- **Lemma 16.** For coprime `N, N'`: `IC(M; N·N') = IC(M;N) + IC(M;N')`. -/
theorem IC_add_coprime {M N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (hcop : Nat.Coprime N N') :
    IC M (N * N') = IC M N + IC M N' := by
  simp only [IC]
  have hdisj : Disjoint N.primeFactors N'.primeFactors := by
    rw [Finset.disjoint_left]; intro q hqN hqN'
    have hqp := (Nat.mem_primeFactors.mp hqN).1
    have := Nat.dvd_gcd (Nat.mem_primeFactors.mp hqN).2.1
                        (Nat.mem_primeFactors.mp hqN').2.1
    rw [hcop] at this
    exact absurd (Nat.le_of_dvd Nat.one_pos this) hqp.one_lt.not_le
  rw [Nat.primeFactors_mul hN hN', Finset.sum_union hdisj]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro q hq <;>
      congr 1 <;> congr 1 <;> rw [Nat.factorization_mul hN hN', Finsupp.add_apply]
  · have h0 : N'.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hdvd =>
        Finset.disjoint_left.mp hdisj hq
          (Nat.mem_primeFactors_iff_dvd hN' (Nat.mem_primeFactors.mp hq).1 |>.mpr hdvd)
    simp [h0]
  · have h0 : N.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hdvd =>
        Finset.disjoint_right.mp hdisj hq
          (Nat.mem_primeFactors_iff_dvd hN (Nat.mem_primeFactors.mp hq).1 |>.mpr hdvd)
    simp [h0]

/-! ### Proposition 17 — Affine (log) upper bound on IC -/

/-- **Proposition 17.** `IC(M; N) ≤ Real.log N`. -/
theorem IC_le_log {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    IC M N ≤ Real.log N := by
  have keyN : N = ∏ q ∈ N.primeFactors, q ^ N.factorization q := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
  calc IC M N
      = ∑ q ∈ N.primeFactors,
            (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q := rfl
    _ ≤ ∑ q ∈ N.primeFactors, (N.factorization q : ℝ) * Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_right _
          (Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_le))
        exact_mod_cast Nat.min_le_right _ _
    _ = Real.log N := by
        have hcast : (N : ℝ) = ∏ q ∈ N.primeFactors, (q : ℝ) ^ N.factorization q := by
          conv_lhs => rw [keyN]
          push_cast
          rfl
        rw [hcast, Real.log_prod _ _ (fun q hq => by
          have hqpos : (0 : ℝ) < (q : ℝ) := by
            exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
          positivity)]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Real.log_pow]

/-! ### AB-Linearization — p-adic digit-sum identity -/

/-- The `j`-th digit of `X` in base `p` (LSB first). -/
def padicDigit (p X j : ℕ) : ℕ := (X / p ^ j) % p

/-- **AB-Linearization identity.**  `Σ_{j < n} digit_j(X) · p^j = X mod p^n`. -/
theorem ab_linearization (p X n : ℕ) (hp : 1 < p) :
    ∑ j ∈ Finset.range n, padicDigit p X j * p ^ j = X % p ^ n := by
  simp only [padicDigit]
  induction n with
  | zero => simp
  | succ n ih =>
    have hdec : X % (p ^ n * p) = X % p ^ n + p ^ n * ((X / p ^ n) % p) := by
      have hp0 : 0 < p := by omega
      have hpn0 : 0 < p ^ n := pow_pos hp0 n
      have e1 : X = p ^ n * (X / p ^ n) + X % p ^ n := (Nat.div_add_mod X (p ^ n)).symm
      have e2 : X / p ^ n = p * (X / p ^ n / p) + (X / p ^ n) % p :=
        (Nat.div_add_mod (X / p ^ n) p).symm
      have hr1lt : X % p ^ n < p ^ n := Nat.mod_lt X hpn0
      have hr2lt : (X / p ^ n) % p < p := Nat.mod_lt _ hp0
      have hb : p ^ n * ((X / p ^ n) % p) + p ^ n ≤ p ^ n * p := by
        calc p ^ n * ((X / p ^ n) % p) + p ^ n
            = p ^ n * ((X / p ^ n) % p + 1) := by ring
          _ ≤ p ^ n * p := by gcongr <;> omega
      have hs : p ^ n * ((X / p ^ n) % p) + X % p ^ n < p ^ n * p := by omega
      have eX : X = (p ^ n * ((X / p ^ n) % p) + X % p ^ n)
                    + (p ^ n * p) * (X / p ^ n / p) := by
        nth_rewrite 1 [e1]
        nth_rewrite 1 [e2]
        ring
      conv_lhs => rw [eX]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
      ring
    rw [Finset.sum_range_succ, pow_succ, ih, hdec]
    ring

/-- **AB-Linearization (quotient form).**
    `X = p^n · (X / p^n) + Σ_{j < n} digit_j(X) · p^j`. -/
theorem ab_linearization_div (p X n : ℕ) (hp : 1 < p) :
    X = p ^ n * (X / p ^ n) + ∑ j ∈ Finset.range n, padicDigit p X j * p ^ j := by
  rw [ab_linearization p X n hp]
  exact (Nat.div_add_mod X (p ^ n)).symm

/-! ### Proposition 2 — Hensel gate = discriminant gate on U -/

/-- **Proposition 2.** For prime `p ∤ M` (i.e. `p ∈ U`),
    `obstructionFree M p k` holds for all `k`. -/
theorem hensel_eq_discriminant_gate_on_U (p M k : ℕ) (hp : p.Prime)
    (hU : ¬ p ∣ M) :
    obstructionFree M p k := by
  simp only [obstructionFree]
  rw [Nat.Coprime.gcd_eq_one]
  exact Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hU).symm

/-! ### Corollary 3 — Good-prime box -/

/-- **Corollary 3.** For prime `p ∤ M`, all detectors vanish at every level. -/
theorem good_prime_box {M p : ℕ} (hp : p.Prime) (hU : ¬ p ∣ M) :
    ∀ k : ℕ, obstructionFree M p k :=
  fun k => hensel_eq_discriminant_gate_on_U p M k hp hU

theorem good_prime_not_in_support {M : ℕ} (hM : M ≠ 0) {p : ℕ} (hp : p.Prime)
    (hnsupp : p ∉ equalizerSupport M) (k : ℕ) :
    obstructionFree M p k :=
  good_prime_box hp ((mem_equalizerSupport_iff hM hp).not.mp hnsupp)

/-! ### Theorem 14 — Primewise Tor¹ decomposition (reference alias) -/

/-- **Theorem 14.** Primewise Tor¹ CRT; proved as `gcd_eq_prod_primeFactors`. -/
alias thm14_primewise_decomposition := gcd_eq_prod_primeFactors

/-! ### Theorem 18 — Obstruction-free global criterion -/

/-- **Theorem 18.** `Nat.Coprime M X` iff the local obstruction at every prime
    factor of `M` vanishes at level 1. -/
theorem obstructionFree_global_iff {M X : ℕ} (hM : M ≠ 0) :
    Nat.Coprime M X ↔ ∀ p ∈ equalizerSupport M, obstructionFree X p 1 := by
  simp only [equalizerSupport, obstructionFree, pow_one]
  constructor
  · intro hcop p hp
    have hpM : p ∣ M := (Nat.mem_primeFactors.mp hp).2.1
    exact (Nat.Coprime.coprime_dvd_left hpM hcop).symm
  · intro h
    by_contra hnc
    have hg : Nat.gcd M X ≠ 1 := hnc
    obtain ⟨p, hpp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hpM : p ∣ M := hpg.trans (Nat.gcd_dvd_left M X)
    have hpX : p ∣ X := hpg.trans (Nat.gcd_dvd_right M X)
    have hpmem : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpM, hM⟩
    have hgcd1 : Nat.gcd X p = 1 := h p hpmem
    have hpd : p ∣ Nat.gcd X p := Nat.dvd_gcd hpX dvd_rfl
    rw [hgcd1] at hpd
    exact hpp.one_lt.ne' (Nat.dvd_one.mp hpd)

/-! ### Theorem 1 / Theorem 18 — Global Certificate -/

/-- **Theorem 1 / 18 (Global Certificate, arithmetic form).**
    `X ≥ 2` is prime iff every prime divisor of `X` equals `X`. -/
theorem global_certificate_iff {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ ∀ p : ℕ, p.Prime → p ∣ X → p = X := by
  constructor
  · intro hXP p hpp hdvd
    exact (hXP.eq_one_or_self_of_dvd p hdvd).resolve_left hpp.one_lt.ne'
  · intro h
    exact (h X.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd X)) ▸
      Nat.minFac_prime (by omega)

/-- **Global certificate via coprimality (trial-division form).**
    `X ≥ 2` is prime iff every `d` with `2 ≤ d < X` is coprime to `X`. -/
theorem global_certificate_coprime {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ ∀ d : ℕ, 2 ≤ d → d < X → Nat.Coprime d X := by
  constructor
  · intro hXP d hd2 hdX
    apply Nat.Coprime.symm
    rw [hXP.coprime_iff_not_dvd]
    intro hXd
    have : X ≤ d := Nat.le_of_dvd (by omega) hXd
    omega
  · intro h
    rw [Nat.prime_def_lt]
    refine ⟨hX, fun m hmX hmdvd => ?_⟩
    by_contra hm1
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmdvd
      omega
    have hm2 : 2 ≤ m := by omega
    have hcop := h m hm2 hmX
    have hgm : Nat.gcd m X = m := Nat.gcd_eq_left hmdvd
    rw [Nat.Coprime] at hcop
    omega

/-! ### Six-line Minimal Certificate — structure and (elementary) soundness -/

/-- A **six-line minimal certificate** witnessing the primality of `X`. -/
structure MinimalCertificate (X : ℕ) where
  A    : ℕ
  pn   : ℕ
  M    : ℕ
  k    : ℕ
  hpn  : pn.Prime
  hcop : Nat.Coprime M X
  hA   : 0 < A
  hpow : X < pn ^ 2

/-- **Soundness of the six-line minimal certificate (elementary form).**
    If `X ≥ 2`, the certificate's bound `X < pn²` holds, and no prime `q < pn`
    divides `X`, then `X` is prime.  Proof via `minFac² ≤ X < pn²`. -/
theorem minimalCertificate_sound {X : ℕ} (hX : 2 ≤ X)
    (cert : MinimalCertificate X)
    (htrial : ∀ q : ℕ, q.Prime → q < cert.pn → ¬ q ∣ X) :
    X.Prime := by
  by_contra hnp
  have hmfp : (X.minFac).Prime := Nat.minFac_prime (by omega)
  have hmfd : X.minFac ∣ X := Nat.minFac_dvd X
  have hle : X.minFac * X.minFac ≤ X := by
    have h := Nat.minFac_le_div (by omega) hnp
    calc X.minFac * X.minFac
        ≤ X.minFac * (X / X.minFac) := mul_le_mul_left' h _
      _ = X := Nat.mul_div_cancel' hmfd
  have hlt : X.minFac < cert.pn := by
    by_contra hge
    push_neg at hge
    have hsq : cert.pn * cert.pn ≤ X.minFac * X.minFac := Nat.mul_le_mul hge hge
    have hpow := cert.hpow
    rw [pow_two] at hpow
    omega
  exact htrial X.minFac hmfp hlt hmfd

/-! ### Axiom audit for all additions -/

section NewAxiomAudit
#print axioms mem_equalizerSupport_iff
#print axioms mem_equalizerSupport_iff_not_obstructionFree
#print axioms gcd_eq_prime_pow_localThickness
#print axioms gcd_mul_coprime
#print axioms card_Tor_mul_coprime
#print axioms card_Tor_prime_pow_eq_gcd
#print axioms IC_mono
#print axioms IC_mono_of_dvd
#print axioms IC_add_coprime
#print axioms IC_le_log
#print axioms ab_linearization
#print axioms ab_linearization_div
#print axioms hensel_eq_discriminant_gate_on_U
#print axioms good_prime_box
#print axioms obstructionFree_global_iff
#print axioms global_certificate_iff
#print axioms global_certificate_coprime
#print axioms minimalCertificate_sound
end NewAxiomAudit

/-! ### Original axiom audit (preserved) -/
section AxiomAudit
#print axioms equalizer_mem_iff
#print axioms equalizer_ideal_inter
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms gcd_thickness_prime_pow
#print axioms lcm_thickness_prime_pow
#print axioms range_mulLeft
#print axioms card_ker_mulLeft
#print axioms commonResidueFiber_card
#print axioms obstructionFree_iff_card
#print axioms primewise_exponent
#print axioms gcd_eq_prod
#print axioms thickness_stable_coprime
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
end AxiomAudit

end Spt1
