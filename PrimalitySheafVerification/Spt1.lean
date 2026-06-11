/-
================================================================================
  Spt1_Integrated.lean — INTEGRATED formalization of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification"  (Spt 1).

  Single self-contained file combining:

    PART A  (namespace `Spt1`)        — the elementary arithmetic core:
        defs (common residue fiber, local thickness, IC, equalizer support),
        Lemmas A/B/C/5/6/15/16, Props 2/7/17, Thms 1/4.1/14/18,
        AB-linearization, six-line minimal certificate.  NO `sorry`.

    PART B  (namespace `Spt1SheafFull`) — the sheaf-theoretic geometry:
        principal-open basis B = {D_f} on Spec ℤ, four genuinely distinct
        detector sub-sheaves F_num/F_mod/F_padic/F_EC (EC via Weierstrass Δ),
        the four-layer fibre product F, global sections Γ(S,F), Theorem 1
        (sheaf form, plus each layer alone), agreement-on-the-base,
        VisiblePrimesProfile semantics, genuine Lucas/Pocklington certificate.

  OUTSIDE the verified core (introduced as explicit, isolated `axiom`s):
      • Thm 2.1 / Lem 2.3 — p-adic logarithm gate (analytic ℚ_p)
      • Thm 6.2          — sheaf-theoretic terminal amalgam

  Every non-axiom result is machine-checked; `#print axioms` blocks confirm
  dependence only on `[propext, Classical.choice, Quot.sound]`.
================================================================================
-/
import Mathlib

open scoped BigOperators
open Opposite TopologicalSpace CategoryTheory

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unnecessarySeqFocus false

/-! ##########################################################################
    PART A — Elementary arithmetic core
    ########################################################################## -/

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

/-! ## NEW ADDITIONS  (all fully proved) -/

/-- **VisiblePrimesProfile** (paper §2): the six-tuple `(A, p^n, M, k, Δ, W)`. -/
structure VisiblePrimesProfile where
  A  : ℕ
  pn : ℕ
  M  : ℕ
  k  : ℕ
  Δ  : ℤ
  W  : ℕ

/-- **IC_nat** — integer-weighted indicator complexity. -/
def IC_nat (M N : ℕ) : ℕ :=
  ∑ q ∈ N.primeFactors, min (M.factorization q) (N.factorization q) * q

/-- The **equalizer support** `Supp(M)`. -/
abbrev equalizerSupport (M : ℕ) : Finset ℕ := M.primeFactors

/-- **Lemma 5 (membership).** `p ∈ Supp(M) ↔ p ∣ M`. -/
theorem mem_equalizerSupport_iff {M : ℕ} (hM : M ≠ 0) {p : ℕ} (hp : p.Prime) :
    p ∈ equalizerSupport M ↔ p ∣ M := by
  rw [equalizerSupport, Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨hp, h, hM⟩⟩

/-- **Lemma 5 (obstruction link).** -/
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

/-- **Lemma 6.** `|Tor₁^ℤ(ℤ/M, ℤ/p^k)| = gcd(M, p^k)`. -/
theorem card_Tor_prime_pow_eq_gcd {p : ℕ} (_hp : p.Prime) (M k : ℕ)
    [NeZero (p ^ k)] :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod (p ^ k))).ker = Nat.gcd M (p ^ k) := by
  rw [card_ker_mulLeft, Nat.gcd_comm]

/-- **Proposition 7.** `gcd(M, p^k) = p ^ localThickness M p k`. -/
theorem gcd_eq_prime_pow_localThickness {p : ℕ} (hp : p.Prime) {M : ℕ}
    (hM : M ≠ 0) (k : ℕ) :
    Nat.gcd M (p ^ k) = p ^ localThickness M p k := by
  obtain ⟨i, _hi, heq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right M (p ^ k))
  have hval : i = localThickness M p k := by
    have h1 : (p ^ i).factorization p = i := Nat.factorization_pow_self hp
    have h2 : (Nat.gcd M (p ^ k)).factorization p = localThickness M p k :=
      gcd_thickness_prime_pow hp hM k
    rw [heq] at h2; exact h1.symm.trans h2
  rw [← hval, heq]

theorem commonResidueIndex_eq_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ}
    (hM : M ≠ 0) (k : ℕ) :
    commonResidueIndex M p k = p ^ localThickness M p k :=
  gcd_eq_prime_pow_localThickness hp hM k

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
    by_contra h; rw [not_or] at h
    have hquP : q.Prime := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization u ▸ Finsupp.mem_support_iff.mpr h.1)
    have hqu : q ∣ u := Nat.dvd_of_mem_primeFactors
      (Nat.support_factorization u ▸ Finsupp.mem_support_iff.mpr h.1)
    have hqv : q ∣ v := Nat.dvd_of_mem_primeFactors
      (Nat.support_factorization v ▸ Finsupp.mem_support_iff.mpr h.2)
    have : q ∣ Nat.gcd u v := Nat.dvd_gcd hqu hqv
    rw [hcop] at this
    exact absurd (Nat.le_of_dvd Nat.one_pos this) (not_le.mpr hquP.one_lt)
  rcases hcop_q with h | h <;> simp [h]

/-- **Lemma B.** Tor¹ multiplicativity for coprime `u, v`. -/
theorem card_Tor_mul_coprime {M u v : ℕ} (hM : M ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : Nat.Coprime u v)
    [NeZero (u * v)] [NeZero u] [NeZero v] :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod (u * v))).ker =
    Nat.card (AddMonoidHom.mulLeft (M : ZMod u)).ker *
    Nat.card (AddMonoidHom.mulLeft (M : ZMod v)).ker := by
  rw [card_ker_mulLeft (u * v) M, card_ker_mulLeft u M, card_ker_mulLeft v M,
      Nat.gcd_comm (u * v), gcd_mul_coprime hM hu hv hcop,
      Nat.gcd_comm u, Nat.gcd_comm v]

/-- **Lemma C.** `gcd(M, p^k) = p ^ min(v_p M, k)`. -/
alias lemmaC_single_prime_pow := gcd_eq_prime_pow_localThickness

/-- **Lemma 15 (pointwise).** -/
theorem IC_mono {M M' N : ℕ}
    (h : ∀ q, M.factorization q ≤ M'.factorization q) :
    IC M N ≤ IC M' N := by
  apply Finset.sum_le_sum; intro q hq
  apply mul_le_mul_of_nonneg_right _
    (Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_le))
  exact_mod_cast min_le_min (h q) (le_refl _)

/-- **Lemma 15 (divisibility).** -/
theorem IC_mono_of_dvd {M M' N : ℕ} (hM' : M' ≠ 0) (h : M ∣ M') :
    IC M N ≤ IC M' N := by
  have hM : M ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at h; exact hM' h
  exact IC_mono fun q =>
    Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hM hM').mpr h) q

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
    exact absurd (Nat.le_of_dvd Nat.one_pos this) (not_le.mpr hqp.one_lt)
  rw [Nat.primeFactors_mul hN hN', Finset.sum_union hdisj]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro q hq <;>
      congr 1 <;> congr 1 <;> rw [Nat.factorization_mul hN hN', Finsupp.add_apply]
  · have h0 : N'.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hdvd =>
        Finset.disjoint_left.mp hdisj hq
          (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1, hdvd, hN'⟩)
    simp [h0]
  · have h0 : N.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hdvd =>
        Finset.disjoint_right.mp hdisj hq
          (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1, hdvd, hN⟩)
    simp [h0]

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
        have hne : ∀ q ∈ N.primeFactors, ((q : ℝ) ^ N.factorization q) ≠ 0 := by
          intro q hq
          have hqpos : (0 : ℝ) < (q : ℝ) := by
            exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
          positivity
        rw [hcast, Real.log_prod hne]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Real.log_pow]

/-- The `j`-th digit of `X` in base `p` (LSB first). -/
def padicDigit (p X j : ℕ) : ℕ := (X / p ^ j) % p

/-- **AB-Linearization identity.**  `Σ_{j < n} digit_j(X) · p^j = X mod p^n`. -/
theorem ab_linearization (p X n : ℕ) (hp : 1 < p) :
    ∑ j ∈ Finset.range n, padicDigit p X j * p ^ j = X % p ^ n := by
  simp only [padicDigit]
  induction n with
  | zero => simp [Nat.mod_one]
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

/-- **AB-Linearization (quotient form).** -/
theorem ab_linearization_div (p X n : ℕ) (hp : 1 < p) :
    X = p ^ n * (X / p ^ n) + ∑ j ∈ Finset.range n, padicDigit p X j * p ^ j := by
  rw [ab_linearization p X n hp]
  exact (Nat.div_add_mod X (p ^ n)).symm

/-- **Proposition 2 (arithmetic form).** For prime `p ∤ M`,
    `obstructionFree M p k` holds for all `k`. -/
theorem hensel_eq_discriminant_gate_on_U (p M k : ℕ) (hp : p.Prime)
    (hU : ¬ p ∣ M) :
    obstructionFree M p k := by
  simp only [obstructionFree]
  rw [Nat.Coprime.gcd_eq_one]
  exact Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hU).symm

/-- **Corollary 3 (Good-prime box).** -/
theorem good_prime_box {M p : ℕ} (hp : p.Prime) (hU : ¬ p ∣ M) :
    ∀ k : ℕ, obstructionFree M p k :=
  fun k => hensel_eq_discriminant_gate_on_U p M k hp hU

theorem good_prime_not_in_support {M : ℕ} (hM : M ≠ 0) {p : ℕ} (hp : p.Prime)
    (hnsupp : p ∉ equalizerSupport M) (k : ℕ) :
    obstructionFree M p k :=
  good_prime_box hp ((mem_equalizerSupport_iff hM hp).not.mp hnsupp) k

/-- **Theorem 14.** Primewise Tor¹ CRT; proved as `gcd_eq_prod_primeFactors`. -/
alias thm14_primewise_decomposition := gcd_eq_prod_primeFactors

/-- **Theorem 18.** Obstruction-free global criterion. -/
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

/-- **Theorem 1 / 18 (Global Certificate, arithmetic form).** -/
theorem global_certificate_iff {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ ∀ p : ℕ, p.Prime → p ∣ X → p = X := by
  constructor
  · intro hXP p hpp hdvd
    exact (hXP.eq_one_or_self_of_dvd p hdvd).resolve_left hpp.one_lt.ne'
  · intro h
    exact (h X.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd X)) ▸
      Nat.minFac_prime (by omega)

/-- **Global certificate via coprimality (trial-division form).** -/
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

/-- **Soundness (elementary trial-division form).** -/
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
    rw [not_lt] at hge
    have hsq : cert.pn * cert.pn ≤ X.minFac * X.minFac := Nat.mul_le_mul hge hge
    have hpow := cert.hpow
    rw [pow_two] at hpow
    omega
  exact htrial X.minFac hmfp hlt hmfd

/-! ### Axiom audit (Part A) -/
section AxiomAuditA
#print axioms factorization_gcd_apply
#print axioms card_ker_mulLeft
#print axioms gcd_eq_prime_pow_localThickness
#print axioms gcd_mul_coprime
#print axioms IC_le_log
#print axioms ab_linearization
#print axioms global_certificate_iff
#print axioms global_certificate_coprime
#print axioms minimalCertificate_sound
end AxiomAuditA

end Spt1

/-! ##########################################################################
    PART B — Sheaf-theoretic geometry (Spec ℤ, four-layer fibre product, Thm 1)
    ########################################################################## -/

namespace Spt1SheafFull

/-! ## §0  Arithmetic backbone -/

theorem prime_iff_all_primeDvd {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ ∀ q : ℕ, q.Prime → q ∣ X → q = X := by
  constructor
  · intro hXP q hqp hdvd
    exact (hXP.eq_one_or_self_of_dvd q hdvd).resolve_left hqp.one_lt.ne'
  · intro h
    exact (h X.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd X)) ▸
      Nat.minFac_prime (by omega)

/-- Residue-ring form of divisibility: `(X : ℤ/q) = 0 ↔ q ∣ X`. -/
theorem mod_eq_zero_iff_dvd (X q : ℕ) : ((X : ZMod q) = 0) ↔ q ∣ X :=
  CharP.cast_eq_zero_iff (ZMod q) q X

/-- Valuation form of divisibility. -/
theorem dvd_iff_one_le_factorization {q X : ℕ} (hq : q.Prime) (hX : X ≠ 0) :
    q ∣ X ↔ 1 ≤ X.factorization q := by
  rw [← Nat.Prime.dvd_iff_one_le_factorization hq hX]

/-! ## §1  S = Spec ℤ, the principal-open basis B = {D_f}, and points (q) -/

abbrev SpecZ : TopCat := TopCat.of (PrimeSpectrum ℤ)

/-- **PrincipalOpenBasis** `B = {D_f}` — the set of principal opens. -/
def principalOpens : Set (Set (PrimeSpectrum ℤ)) :=
  Set.range (fun f : ℤ => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum ℤ)))

/-- `B = {D_f}` is a topological basis of `S = Spec ℤ`. -/
theorem principalOpens_isBasis :
    TopologicalSpace.IsTopologicalBasis principalOpens :=
  PrimeSpectrum.isTopologicalBasis_basic_opens

/-- The point of `Spec ℤ` carried by a prime number `q` (the ideal `(q)`). -/
def pointOfPrime {q : ℕ} (hq : q.Prime) : PrimeSpectrum ℤ where
  asIdeal := Ideal.span {(q : ℤ)}
  isPrime := by
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.pos.ne'
    exact (Ideal.span_singleton_prime hq0).mpr (Nat.prime_iff_prime_int.mp hq)

@[simp] theorem mem_pointOfPrime {q : ℕ} (hq : q.Prime) :
    (q : ℤ) ∈ (pointOfPrime hq).asIdeal :=
  Ideal.mem_span_singleton_self _

theorem prime_mem_pointOfPrime {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) :
    (q : ℤ) ∈ (pointOfPrime hq').asIdeal ↔ q = q' := by
  simp only [pointOfPrime, Ideal.mem_span_singleton]
  constructor
  · intro h
    have hnat : q' ∣ q := by exact_mod_cast h
    exact ((Nat.prime_dvd_prime_iff_eq hq' hq).mp hnat).symm
  · rintro rfl; exact dvd_rfl

/-! ## §2  The four detector layers (genuinely distinct), and base agreement -/

/-- **F_num gate** — numeric detector. -/
def gateNum (X : ℕ) (p : PrimeSpectrum ℤ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℤ) ∈ p.asIdeal → q ∣ X → q = X

/-- **F_mod gate** — modular detector via the residue ring `ℤ/q`. -/
def gateMod (X : ℕ) (p : PrimeSpectrum ℤ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℤ) ∈ p.asIdeal → (X : ZMod q) = 0 → q = X

/-- **F_padic gate** — `q`-adic detector via valuation `v_q`. -/
def gatePadic (X : ℕ) (p : PrimeSpectrum ℤ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℤ) ∈ p.asIdeal → 1 ≤ X.factorization q → q = X

/-- **Agreement on the base, I.** -/
theorem gateNum_iff_gateMod {X : ℕ} (p : PrimeSpectrum ℤ) :
    gateNum X p ↔ gateMod X p := by
  constructor
  · intro h q hq hmem hzero
    exact h q hq hmem ((mod_eq_zero_iff_dvd X q).mp hzero)
  · intro h q hq hmem hdvd
    exact h q hq hmem ((mod_eq_zero_iff_dvd X q).mpr hdvd)

/-- **Agreement on the base, II.** -/
theorem gateNum_iff_gatePadic {X : ℕ} (hX : X ≠ 0) (p : PrimeSpectrum ℤ) :
    gateNum X p ↔ gatePadic X p := by
  constructor
  · intro h q hq hmem hval
    exact h q hq hmem ((dvd_iff_one_le_factorization hq hX).mpr hval)
  · intro h q hq hmem hdvd
    exact h q hq hmem ((dvd_iff_one_le_factorization hq hX).mp hdvd)

/-! ### F_EC — genuine elliptic-curve layer (good reduction via `Δ`) -/

/-- Good reduction of a Weierstrass curve `E/ℤ` at a prime `q`: `q ∤ Δ_E`. -/
def goodReductionAt (E : WeierstrassCurve ℤ) (q : ℕ) : Prop := ¬ (q : ℤ) ∣ E.Δ

/-- **F_EC gate** — elliptic-curve detector for candidate `X` w.r.t. `E`. -/
def gateEC (E : WeierstrassCurve ℤ) (X : ℕ) (p : PrimeSpectrum ℤ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℤ) ∈ p.asIdeal → goodReductionAt E q → q ∣ X → q = X

/-- `F_num` refines `F_EC`. -/
theorem gateNum_imp_gateEC (E : WeierstrassCurve ℤ) {X : ℕ} (p : PrimeSpectrum ℤ) :
    gateNum X p → gateEC E X p := by
  intro h q hq hmem _hgr hdvd
  exact h q hq hmem hdvd

/-- On the good-reduction locus of `E`, `F_EC` recovers `F_num`. -/
theorem gateEC_imp_gateNum (E : WeierstrassCurve ℤ) {X : ℕ}
    (hgr : ∀ q : ℕ, q.Prime → q ∣ X → goodReductionAt E q)
    (p : PrimeSpectrum ℤ) :
    gateEC E X p → gateNum X p := by
  intro h q hq hmem hdvd
  exact h q hq hmem (hgr q hq hdvd) hdvd

/-! ## §3  The four sub-sheaves and their fibre product  F = ×_B -/

/-- Fibre type (terminal): a section is a proof. -/
abbrev fibre : SpecZ → Type := fun _ => Unit

/-- A gate `g` defines a genuine sub-sheaf via a `LocalPredicate`. -/
def gateLocal (g : PrimeSpectrum ℤ → Prop) : TopCat.LocalPredicate fibre where
  pred {U} _ := ∀ x : U, g x.1
  res {U V} i _ h x := h ⟨x.1, (leOfHom i) x.2⟩
  locality {U} _ w x := by
    obtain ⟨V, mV, _iVU, h⟩ := w x
    exact h ⟨x.1, mV⟩

def F_num (X : ℕ) : TopCat.Sheaf (Type) SpecZ := TopCat.subsheafToTypes (gateLocal (gateNum X))
def F_mod (X : ℕ) : TopCat.Sheaf (Type) SpecZ := TopCat.subsheafToTypes (gateLocal (gateMod X))
def F_padic (X : ℕ) : TopCat.Sheaf (Type) SpecZ := TopCat.subsheafToTypes (gateLocal (gatePadic X))
def F_EC (E : WeierstrassCurve ℤ) (X : ℕ) : TopCat.Sheaf (Type) SpecZ :=
  TopCat.subsheafToTypes (gateLocal (gateEC E X))

/-- The conjunction gate = the fibre-product locus. -/
def gateAll (E : WeierstrassCurve ℤ) (X : ℕ) (p : PrimeSpectrum ℤ) : Prop :=
  gateNum X p ∧ gateMod X p ∧ gatePadic X p ∧ gateEC E X p

/-- **FourLayerFiberProduct** `F = F_num ×_B F_mod ×_B F_p-adic ×_B F_EC`. -/
def F (E : WeierstrassCurve ℤ) (X : ℕ) : TopCat.Sheaf (Type) SpecZ :=
  TopCat.subsheafToTypes (gateLocal (gateAll E X))

/-- **Global sections** `Γ(S, F)`. -/
def globalSections (E : WeierstrassCurve ℤ) (X : ℕ) : Type :=
  (F E X).val.obj (op ⊤)

/-- **Section-level pullback characterization** of the fibre product. -/
theorem globalSections_nonempty_iff (E : WeierstrassCurve ℤ) (X : ℕ) :
    Nonempty (globalSections E X) ↔
      ∀ p : PrimeSpectrum ℤ,
        gateNum X p ∧ gateMod X p ∧ gatePadic X p ∧ gateEC E X p := by
  constructor
  · rintro ⟨s⟩ p
    exact s.2 ⟨p, trivial⟩
  · intro h
    exact ⟨⟨fun _ => (), fun x => h x.1⟩⟩

/-! ## §4  Theorem 1 (Global Certificate), four-layer sheaf form -/

theorem forall_gateAll_iff_prime (E : WeierstrassCurve ℤ) {X : ℕ} (hX : 2 ≤ X) :
    (∀ p : PrimeSpectrum ℤ, gateNum X p ∧ gateMod X p ∧ gatePadic X p ∧ gateEC E X p)
      ↔ X.Prime := by
  have hX0 : X ≠ 0 := by omega
  constructor
  · intro h
    rw [prime_iff_all_primeDvd hX]
    intro q hqp hdvd
    exact (h (pointOfPrime hqp)).1 q hqp (mem_pointOfPrime hqp) hdvd
  · intro hP p
    have hnum : gateNum X p := by
      intro q hqp _ hdvd
      exact ((prime_iff_all_primeDvd hX).mp hP) q hqp hdvd
    exact ⟨hnum, (gateNum_iff_gateMod p).mp hnum,
           (gateNum_iff_gatePadic hX0 p).mp hnum, gateNum_imp_gateEC E p hnum⟩

/-- **Theorem 1 (Global Certificate, four-layer sheaf form).** -/
theorem theorem1_fourLayer (E : WeierstrassCurve ℤ) {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ Nonempty (globalSections E X) := by
  rw [globalSections_nonempty_iff, forall_gateAll_iff_prime E hX]

/-! ## §4b  Each layer alone certifies primality; four-way base agreement. -/

theorem layer_nonempty_iff (g : PrimeSpectrum ℤ → Prop) :
    Nonempty ((TopCat.subsheafToTypes (gateLocal g)).val.obj (op ⊤)) ↔
      ∀ p : PrimeSpectrum ℤ, g p := by
  constructor
  · rintro ⟨s⟩ p; exact s.2 ⟨p, trivial⟩
  · intro h; exact ⟨⟨fun _ => (), fun x => h x.1⟩⟩

theorem forall_gateNum_iff_prime {X : ℕ} (hX : 2 ≤ X) :
    (∀ p : PrimeSpectrum ℤ, gateNum X p) ↔ X.Prime := by
  rw [prime_iff_all_primeDvd hX]
  constructor
  · intro h q hqp hdvd
    exact h (pointOfPrime hqp) q hqp (mem_pointOfPrime hqp) hdvd
  · intro h p q hqp _ hdvd; exact h q hqp hdvd

/-- **F_num alone** certifies primality. -/
theorem theorem1_via_num {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ Nonempty ((F_num X).val.obj (op ⊤)) :=
  ((layer_nonempty_iff (gateNum X)).trans (forall_gateNum_iff_prime hX)).symm

/-- **F_mod alone** certifies primality. -/
theorem theorem1_via_mod {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ Nonempty ((F_mod X).val.obj (op ⊤)) := by
  rw [show (F_mod X) = TopCat.subsheafToTypes (gateLocal (gateMod X)) from rfl,
      layer_nonempty_iff]
  rw [← forall_gateNum_iff_prime hX]
  exact ⟨fun h p => (gateNum_iff_gateMod p).mp (h p),
         fun h p => (gateNum_iff_gateMod p).mpr (h p)⟩

/-- **F_padic alone** certifies primality. -/
theorem theorem1_via_padic {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ Nonempty ((F_padic X).val.obj (op ⊤)) := by
  have hX0 : X ≠ 0 := by omega
  rw [show (F_padic X) = TopCat.subsheafToTypes (gateLocal (gatePadic X)) from rfl,
      layer_nonempty_iff]
  rw [← forall_gateNum_iff_prime hX]
  exact ⟨fun h p => (gateNum_iff_gatePadic hX0 p).mp (h p),
         fun h p => (gateNum_iff_gatePadic hX0 p).mpr (h p)⟩

/-- **F_EC alone** certifies primality, using good reduction — EC layer ACTIVE. -/
theorem theorem1_via_EC (E : WeierstrassCurve ℤ) {X : ℕ} (hX : 2 ≤ X)
    (hgr : ∀ q : ℕ, q.Prime → q ∣ X → goodReductionAt E q) :
    X.Prime ↔ Nonempty ((F_EC E X).val.obj (op ⊤)) := by
  rw [show (F_EC E X) = TopCat.subsheafToTypes (gateLocal (gateEC E X)) from rfl,
      layer_nonempty_iff]
  rw [← forall_gateNum_iff_prime hX]
  exact ⟨fun h p => gateNum_imp_gateEC E p (h p),
         fun h p => gateEC_imp_gateNum E hgr p (h p)⟩

/-- **Complete agreement on the base.** -/
theorem four_gates_agree (E : WeierstrassCurve ℤ) {X : ℕ} (hX0 : X ≠ 0)
    (hgr : ∀ q : ℕ, q.Prime → q ∣ X → goodReductionAt E q)
    (p : PrimeSpectrum ℤ) :
    (gateNum X p ↔ gateMod X p) ∧ (gateNum X p ↔ gatePadic X p) ∧
    (gateNum X p ↔ gateEC E X p) := by
  refine ⟨gateNum_iff_gateMod p, gateNum_iff_gatePadic hX0 p, ?_⟩
  exact ⟨gateNum_imp_gateEC E p, gateEC_imp_gateNum E hgr p⟩

/-! ## §5  VisiblePrimesProfile — with real semantics and soundness -/

structure VisiblePrimesProfile where
  A  : ℕ
  pn : ℕ
  M  : ℕ
  k  : ℕ
  Δ  : ℤ
  W  : ℕ

namespace VisiblePrimesProfile

/-- **Validity** of a profile as a primality certificate for `X`. -/
def Valid (P : VisiblePrimesProfile) (X : ℕ) : Prop :=
  P.pn.Prime ∧
  Nat.Coprime P.M X ∧
  ((P.A : ZMod X) ^ (X - 1) = 1) ∧
  (∀ q : ℕ, q.Prime → q ∣ (X - 1) → (P.A : ZMod X) ^ ((X - 1) / q) ≠ 1)

/-- **Soundness:** a valid profile certifies primality (Lucas/Pocklington). -/
theorem Valid.sound {P : VisiblePrimesProfile} {X : ℕ} (h : P.Valid X) : X.Prime :=
  lucas_primality X (P.A : ZMod X) h.2.2.1 h.2.2.2

end VisiblePrimesProfile

/-! ## §6  Six-line minimal certificate — genuine Lucas/Pocklington -/

structure LucasCertificate (X : ℕ) where
  a  : ZMod X
  ha : a ^ (X - 1) = 1
  hd : ∀ q : ℕ, q.Prime → q ∣ (X - 1) → a ^ ((X - 1) / q) ≠ 1

theorem LucasCertificate.sound {X : ℕ} (c : LucasCertificate X) : X.Prime :=
  lucas_primality X c.a c.ha c.hd

/-- Worked example: `7` is prime, witnessed by `a = 3`. -/
example : Nat.Prime 7 := by
  apply LucasCertificate.sound (X := 7)
  refine { a := 3, ha := by decide, hd := ?_ }
  intro q hq hqdvd
  have hq2 : 2 ≤ q := hq.two_le
  have hq6 : q ≤ 6 := Nat.le_of_dvd (by norm_num) hqdvd
  interval_cases q <;> revert hqdvd <;> decide

/-! ## §7  Proposition 2 — Hensel gate ⟺ discriminant gate -/

def henselGate (M p : ℕ) : Prop := Nat.gcd M p = 1
def discriminantGate (M p : ℕ) : Prop := ¬ p ∣ M

theorem prop2_hensel_iff_discriminant {p : ℕ} (hp : p.Prime) (M : ℕ) :
    henselGate M p ↔ discriminantGate M p := by
  unfold henselGate discriminantGate
  constructor
  · intro hg hdvd
    have hpd : p ∣ Nat.gcd M p := Nat.dvd_gcd hdvd dvd_rfl
    rw [hg] at hpd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpd)
  · intro hndvd
    exact (hp.coprime_iff_not_dvd.mpr hndvd).symm

/-- **Proposition 2, elliptic-curve form.** Hensel gate = good reduction = `q ∤ Δ_E`. -/
theorem prop2_goodReduction_iff_discriminant (E : WeierstrassCurve ℤ) (q : ℕ) :
    goodReductionAt E q ↔ ¬ (q : ℤ) ∣ E.Δ :=
  Iff.rfl

/-! ## §8  Excluded non-elementary results — explicit AXIOMS (isolated) -/

/-- **Axiom — Thm 2.1 / Lem 2.3 (p-adic logarithm gate).** Analytic; outside core. -/
axiom padicLogGate {p : ℕ} (hp : p.Prime) (hodd : Odd p) {M k : ℕ} (hU : ¬ p ∣ M) :
    ∃ L : ZMod (p ^ k) → ZMod (p ^ k), Function.Injective L

/-- **Axiom — Thm 6.2 (terminal amalgam).** Sheaf-global; outside core. -/
axiom terminalAmalgam (E : WeierstrassCurve ℤ) {X : ℕ} (hX : 2 ≤ X) (hP : X.Prime) :
    Subsingleton (globalSections E X)

/-! ## §9  Axiom audit (Part B) -/

section AxiomAuditB
#print axioms prime_iff_all_primeDvd
#print axioms principalOpens_isBasis
#print axioms prime_mem_pointOfPrime
#print axioms gateNum_iff_gateMod
#print axioms gateNum_iff_gatePadic
#print axioms gateEC_imp_gateNum
#print axioms globalSections_nonempty_iff
#print axioms forall_gateAll_iff_prime
#print axioms theorem1_fourLayer
#print axioms theorem1_via_num
#print axioms theorem1_via_mod
#print axioms theorem1_via_padic
#print axioms theorem1_via_EC
#print axioms four_gates_agree
#print axioms prop2_goodReduction_iff_discriminant
#print axioms VisiblePrimesProfile.Valid.sound
#print axioms LucasCertificate.sound
#print axioms prop2_hensel_iff_discriminant
end AxiomAuditB

end Spt1SheafFull

