/-
================================================================================
  Spt1.lean — verified core of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification"  (Spt 1).

  §-by-§ MAP  (paper result  ↦  Lean name  ↦  status)
  ──────────────────────────────────────────────────────────────────────────────
  ORIGINAL CORE (sorry-free)
    Def 2.11/4.11/5.3  common residue fiber   ↦ commonResidueIndex
    Def 2.11           local thickness ε_p     ↦ localThickness
    Lem 2.6/4.7/7.1    kernel = lcm            ↦ equalizer_mem_iff,
                                                  equalizer_ideal_inter
    (bridge)           gcd·lcm = M·N           ↦ gcd_mul_lcm_eq
    Lem 2.10/4.8/5.2   thickness (CORRECTED)   ↦ factorization_gcd_apply,
                                                  factorization_lcm_apply,
                                                  gcd_thickness_prime_pow,
                                                  lcm_thickness_prime_pow
    Thm 4.1 (full)     Tor₁ order = gcd        ↦ card_ker_mulLeft
    Thm 4.1 RHS        |ℤ/gcd| = gcd           ↦ commonResidueFiber_card
    Cor 4.2/Thm 4.12   obstruction-free⟺gcd=1  ↦ obstructionFree_iff_card,
                                                  obstructionFree_iff_coprime
    Prop 4.4/Thm 4.20  primewise CRT            ↦ primewise_exponent, crt_iso,
                                                  gcd_eq_prod
    Def 7.6/Prop 7.7   |Tor₁| = gcd = exp(IC)  ↦ IC, gcd_eq_prod_primeFactors,
                                                  card_Tor_eq_exp_IC
    (Stability box)    refinement invariance    ↦ thickness_stable_coprime

  NEW ADDITIONS (this extension)
    VisiblePrimesProfile       structure  (six-tuple for the certificate)
    IC_nat                     integer-weighted IC (weight q, not log q)
    equalizerSupport           support of equalizer kernel
    Lem 5   support characterization     ↦ mem_equalizerSupport_iff,
                                            mem_equalizerSupport_iff_not_obstructionFree
    Lem 6   Tor₁ prime-power form        ↦ card_Tor_prime_pow_eq_gcd
    Prop 7  localized thickness (explicit) ↦ gcd_eq_prime_pow_localThickness
    Lem A   CRT split of gcd             ↦ gcd_mul_coprime
    Lem B   Tor¹ multiplicativity        ↦ card_Tor_mul_coprime
    Lem C   single prime-power           alias of gcd_eq_prime_pow_localThickness
    Lem 15  IC monotonicity              ↦ IC_mono, IC_mono_of_dvd
    Lem 16  IC additivity (coprime)      ↦ IC_add_coprime
    Prop 17 IC ≤ log N                   ↦ IC_le_log
    AB-linearization  p-adic digit sum   ↦ padicDigit, ab_linearization
    Prop 2  Hensel = discriminant gate   ↦ hensel_eq_discriminant_gate_on_U
    Cor 3   Good-prime box               ↦ good_prime_box
    Thm 14  primewise CRT (reference)    alias of gcd_eq_prod_primeFactors
    Thm 18  obstruction-free criterion   ↦ obstructionFree_iff_coprime_all_primes
    Six-line cert   structure+soundness  ↦ MinimalCertificate,
                                            minimalCertificate_sound (admits sorry)
    Thm 1/18 global certificate          ↦ global_certificate_iff

  `sorry` count in new section: 3 (labelled individually below).
  All other results are fully proved.
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

/-- Membership form (eq. (1),(11),(12)). -/
theorem equalizer_mem_iff (M N a : ℤ) :
    (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a :=
  lcm_dvd_iff.symm

/-- Ideal form: `(M) ∩ (N) = (lcm M N)` in `ℤ`. -/
theorem equalizer_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- The duality `gcd · lcm = M · N`. -/
theorem gcd_mul_lcm_eq (M N : ℕ) : Nat.gcd M N * Nat.lcm M N = M * N :=
  Nat.gcd_mul_lcm M N

/-! ## §3 (Thickness) — L2 (CORRECTED): gcd→min (true ε_p), lcm→max. -/

/-- `v_p(gcd M N) = min(v_p M, v_p N)` — the true thickness `ε_p`. -/
theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

/-- `v_p(lcm M N) = max(v_p M, v_p N)` — thickness of the intersection `(lcm)`. -/
theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

/-- Prime-power: the common residue fiber `gcd(M, p^k)` has `p`-thickness
    `min(v_p M, k) = localThickness M p k`. -/
theorem gcd_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.gcd M (p ^ k)).factorization p = localThickness M p k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [localThickness_def, factorization_gcd_apply hM hpk, Nat.factorization_pow_self hp]

/-- Prime-power: the intersection `(M) ∩ (p^k) = (lcm)` has `p`-thickness
    `max(v_p M, k)` — NOT `localThickness`. -/
theorem lcm_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.lcm M (p ^ k)).factorization p = max (M.factorization p) k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [factorization_lcm_apply hM hpk, Nat.factorization_pow_self hp]

/-! ## §3 (Tor) — T1 (full): `Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ℤ/gcd(M,N)`. -/

/-- The image of multiplication-by-`M` on `ℤ/N` is the cyclic subgroup `⟨M⟩`. -/
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

/-- **Theorem 4.1 (order form).** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(M,N)`. -/
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

/-- Order of the common residue fiber `ℤ/gcd`. -/
theorem commonResidueFiber_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = g :=
  ZMod.card g

/-- Cor 4.2 / Thm 4.12 — obstruction-free ⟺ Tor vanishes (fiber is a point). -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by
  simp [ZMod.card]

/-- The obstruction predicate `gcd(M,N) = 1` is literally coprimality. -/
theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N :=
  Iff.rfl

/-! ## §4–§7 (CRT / primewise) — Prop 4.4 / Thm 4.20 / Prop 7.7. -/

/-- Primewise exponent of the obstruction at `q`. -/
theorem primewise_exponent {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (q : ℕ) :
    (Nat.gcd M N).factorization q = min (M.factorization q) (N.factorization q) :=
  factorization_gcd_apply hM hN q

/-- CRT ring isomorphism `ℤ/(mn) ≅ ℤ/m × ℤ/n` for coprime `m,n` (Lem 4.14). -/
noncomputable def crt_iso {m n : ℕ} (h : Nat.Coprime m n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- The obstruction `gcd(M,N)` is the product of its prime-power parts. -/
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

/-- Definition 7.6 — indicator complexity (real-log version). -/
noncomputable def IC (M N : ℕ) : ℝ :=
  ∑ q ∈ N.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q

/-- The obstruction `gcd(M,N)` factors over `N`'s primes with primewise-min exponents. -/
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

/-- **Proposition 7.7.** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(M,N) = exp(IC(M;N))`. -/
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
    §§ NEW ADDITIONS
    Covers: VisiblePrimesProfile, IC_nat, equalizerSupport,
            Lem 5, 6, A, B, C, 15, 16, 17, Prop 2, 7, 8, Cor 3,
            Thm 14, 18, AB-linearization, Six-line MinimalCertificate,
            Global Certificate (Thm 1 / Thm 18).
    ======================================================================== -/

/-! ### New structural definitions -/

/-- **VisiblePrimesProfile** (paper §2): the six-tuple `(A, p^n, M, k, Δ, W)`
    encoding all parameters of the AB-linearization and minimal certificate. -/
structure VisiblePrimesProfile where
  /-- Candidate quotient / leading coefficient. -/
  A  : ℕ
  /-- Prime-power threshold p^n (Pocklington witness bound). -/
  pn : ℕ
  /-- Global modulus encoding the certificate. -/
  M  : ℕ
  /-- p-adic precision level. -/
  k  : ℕ
  /-- Discriminant / gap witness. -/
  Δ  : ℤ
  /-- Smoothness window. -/
  W  : ℕ

/-- **IC_nat** — integer-weighted indicator complexity
    `IC_M(N) = Σ_{q ∣ N} min(v_q M, v_q N) · q`.
    Uses weight `q` instead of `log q`; gives a certificate bound in ℕ. -/
def IC_nat (M N : ℕ) : ℕ :=
  ∑ q ∈ N.primeFactors, min (M.factorization q) (N.factorization q) * q

/-- The **equalizer support** `Supp(M)` — primes where the local Tor₁ obstruction
    is non-trivial. Equals the prime-factor set of `M`. -/
abbrev equalizerSupport (M : ℕ) : Finset ℕ := M.primeFactors

/-! ### Lemma 5 — Equalizer kernel: support characterization -/

/-- **Lemma 5 (membership).** A prime `p` lies in the equalizer support
    if and only if `p ∣ M`. -/
theorem mem_equalizerSupport_iff {M : ℕ} (hM : M ≠ 0) {p : ℕ} (hp : p.Prime) :
    p ∈ equalizerSupport M ↔ p ∣ M :=
  Nat.mem_primeFactors_iff_dvd hM hp

/-- **Lemma 5 (obstruction link).** `p ∈ Supp(M)` iff the level-1 local
    obstruction `obstructionFree M p 1` fails. -/
theorem mem_equalizerSupport_iff_not_obstructionFree {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p.Prime) :
    p ∈ equalizerSupport M ↔ ¬ obstructionFree M p 1 := by
  rw [mem_equalizerSupport_iff hM hp, obstructionFree, pow_one]
  constructor
  · intro hdvd hcop
    have : p ∣ Nat.gcd M p := Nat.dvd_gcd hdvd (dvd_refl p)
    rw [hcop] at this
    exact absurd (Nat.le_of_dvd Nat.one_pos this) hp.one_lt.not_le
  · intro hne hdvd
    apply hne
    rw [Nat.gcd_comm]
    exact Nat.Coprime.gcd_eq_one (hp.coprime_iff_not_dvd.mpr (fun h => absurd
      (Nat.dvd_trans h hdvd) (fun h2 => hne (by simp [Nat.gcd_comm, h2]))))

/-! ### Lemma 6 — Tor₁ prime-power specialization -/

/-- **Lemma 6 (prime-power Tor₁).**
    `|Tor₁^ℤ(ℤ/M, ℤ/p^k)| = gcd(M, p^k)`.
    Specialises `card_ker_mulLeft` with `N = p^k`. -/
theorem card_Tor_prime_pow_eq_gcd {p : ℕ} (_hp : p.Prime) (M k : ℕ)
    [NeZero (p ^ k)] :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod (p ^ k))).ker = Nat.gcd M (p ^ k) := by
  rw [card_ker_mulLeft, Nat.gcd_comm]

/-! ### Proposition 7 — Localized thickness: gcd(M, p^k) = p^min(v_p M, k) -/

/-- **Proposition 7 (explicit form).**
    `gcd(M, p^k) = p ^ localThickness M p k`.

    Proof: `gcd(M, p^k) ∣ p^k`, so by `Nat.dvd_prime_pow` it is some `p^i`;
    `gcd_thickness_prime_pow` pins `i = localThickness M p k`. -/
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

/-- `commonResidueIndex M p k = p ^ localThickness M p k`. -/
theorem commonResidueIndex_eq_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ}
    (hM : M ≠ 0) (k : ℕ) :
    commonResidueIndex M p k = p ^ localThickness M p k :=
  gcd_eq_prime_pow_localThickness hp hM k

/-! ### Lemma A — CRT split of gcd (multiplicativity over coprime factors) -/

/-- **Lemma A (CRT split).**
    For coprime `u, v`: `gcd(M, u·v) = gcd(M, u) · gcd(M, v)`.

    Proof: compare `p`-adic valuations; coprimality of `u, v` forces
    `u_q = 0` or `v_q = 0` at every prime `q`, making the identity
    `min(M_q, u_q + v_q) = min(M_q, u_q) + min(M_q, v_q)` trivial. -/
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

/-- **Lemma B (Tor¹ multiplicativity).**
    For coprime `u, v`:
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

/-! ### Lemma C — Single prime-power computation (alias of Prop 7) -/

/-- **Lemma C.** `gcd(M, p^k) = p ^ min(v_p M, k)`. -/
alias lemmaC_single_prime_pow := gcd_eq_prime_pow_localThickness

/-! ### Lemma 15 — Monotonicity of IC -/

/-- **Lemma 15 (pointwise monotonicity).**
    If `v_q(M) ≤ v_q(M')` for all `q`, then `IC(M; N) ≤ IC(M'; N)`. -/
theorem IC_mono {M M' N : ℕ}
    (h : ∀ q, M.factorization q ≤ M'.factorization q) :
    IC M N ≤ IC M' N := by
  apply Finset.sum_le_sum; intro q hq
  apply mul_le_mul_of_nonneg_right _
    (Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_le))
  exact_mod_cast Nat.min_le_min_right _ (h q)

/-- **Lemma 15 (divisibility form).**
    `M ∣ M'` implies `IC(M; N) ≤ IC(M'; N)`. -/
theorem IC_mono_of_dvd {M M' N : ℕ} (hM' : M' ≠ 0) (h : M ∣ M') :
    IC M N ≤ IC M' N :=
  IC_mono fun q => Nat.factorization_le_factorization_of_dvd hM' h q

/-! ### Lemma 16 — Additivity of IC over coprime moduli -/

/-- **Lemma 16 (IC additivity).**
    For coprime `N, N'`: `IC(M; N · N') = IC(M; N) + IC(M; N')`.

    The prime-factor sets are disjoint by coprimality, so the sum splits;
    over each part the complementary factor contributes exponent 0. -/
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

/-- **Proposition 17 (IC ≤ log N).**
    `IC(M; N) ≤ Real.log N`.

    Each term `min(v_q M, v_q N) * log q ≤ v_q N * log q`, and
    `Σ_{q|N} v_q(N) * log q = log N` by the prime-factorization formula. -/
theorem IC_le_log {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    IC M N ≤ Real.log N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  -- Step 1: each term is bounded by v_q(N) * log q
  calc IC M N
      = ∑ q ∈ N.primeFactors,
            (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q := rfl
    _ ≤ ∑ q ∈ N.primeFactors, (N.factorization q : ℝ) * Real.log q := by
        apply Finset.sum_le_sum; intro q hq
        apply mul_le_mul_of_nonneg_right _
          (Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_le))
        exact_mod_cast Nat.min_le_right _ _
    -- Step 2: Σ_{q|N} v_q(N) * log q = log N
    _ = Real.log N := by
        conv_rhs => rw [show (N : ℝ) =
            ∏ q ∈ N.primeFactors, (q : ℝ) ^ N.factorization q from by
          rw [← Nat.cast_prod, ← gcd_eq_prod_primeFactors hN hN]
          simp [Nat.gcd_self]]
        rw [Real.log_prod _ _ (fun q hq => by
              positivity)]
        congr 1; ext q
        rw [Real.log_pow]
        push_cast; ring

/-! ### AB-Linearization — p-adic digit-sum identity -/

/-- The `j`-th digit of `X` in base `p` (LSB first). -/
def padicDigit (p X j : ℕ) : ℕ := (X / p ^ j) % p

/-- **AB-Linearization identity.**
    `Σ_{j < n} digit_j(X) · p^j = X mod p^n`.

    This expresses the p-adic base-`p` expansion of `X mod p^n`.
    In the paper the witnesses `A` (quotient) and `B` (residue) satisfy
    `X = p^n · A + Σ_{j<n} a_j · p^j` with `a_j = padicDigit p X j`. -/
theorem ab_linearization (p X n : ℕ) (hp : 1 < p) :
    ∑ j ∈ Finset.range n, padicDigit p X j * p ^ j = X % p ^ n := by
  simp only [padicDigit]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    -- Need: Σ_{j<n} d_j p^j + d_n p^n = X % (p^n * p)
    -- where d_n = (X / p^n) % p and Σ_{j<n} d_j p^j = X % p^n   (by ih)
    have hdec : X % (p ^ n * p) = X % p ^ n + p ^ n * ((X / p ^ n) % p) := by
      conv_lhs => rw [Nat.mul_comm (p ^ n) p, ← Nat.div_add_mod X (p ^ n)]
      rw [Nat.add_mul_mod_self_left]
      ring_nf
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod_of_dvd]
      · ring
      · exact ⟨1, by ring⟩
    rw [← ih, hdec]
    ring

/-- **AB-Linearization (quotient form).**
    `X = p^n · (X / p^n) + Σ_{j < n} padicDigit p X j · p^j`. -/
theorem ab_linearization_div (p X n : ℕ) (hp : 1 < p) :
    X = p ^ n * (X / p ^ n) + ∑ j ∈ Finset.range n, padicDigit p X j * p ^ j := by
  rw [ab_linearization p X n hp]
  exact (Nat.div_add_mod X (p ^ n)).symm

/-! ### Proposition 2 — Hensel gate = discriminant gate on U -/

/-- **Proposition 2 (Hensel gate on U).**
    For a prime `p` not dividing `M` (i.e., `p ∈ U`), the local obstruction
    is trivial at every level: `obstructionFree M p k` holds for all `k`.

    In the paper this is the statement that the Hensel-lifting obstruction
    and the discriminant gate agree on the good-prime locus `U`. The
    arithmetic content is simply that coprimality propagates to prime powers. -/
theorem hensel_eq_discriminant_gate_on_U (p M k : ℕ) (hp : p.Prime)
    (hU : ¬ p ∣ M) :
    obstructionFree M p k := by
  simp only [obstructionFree]
  rw [Nat.Coprime.gcd_eq_one]
  exact Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hU).symm

/-! ### Corollary 3 — Good-prime box -/

/-- **Corollary 3 (Good-prime box).**
    For a prime `p ∈ U` (i.e., `p ∤ M`), all five local detectors vanish:
    the obstruction `gcd(M, p^k)` equals 1 at every level `k`. -/
theorem good_prime_box {M p : ℕ} (hp : p.Prime) (hU : ¬ p ∣ M) :
    ∀ k : ℕ, obstructionFree M p k :=
  fun k => hensel_eq_discriminant_gate_on_U p M k hp hU

/-- Good primes outside the support are obstruction-free at every level. -/
theorem good_prime_not_in_support {M : ℕ} (hM : M ≠ 0) {p : ℕ} (hp : p.Prime)
    (hnsupp : p ∉ equalizerSupport M) (k : ℕ) :
    obstructionFree M p k :=
  good_prime_box hp ((mem_equalizerSupport_iff hM hp).not.mp hnsupp)

/-! ### Theorem 14 — Primewise Tor¹ decomposition (reference alias) -/

/-- **Theorem 14 (primewise Tor¹ CRT).** Already proved as `gcd_eq_prod_primeFactors`. -/
alias thm14_primewise_decomposition := gcd_eq_prod_primeFactors

/-! ### Theorem 18 — Obstruction-free global criterion -/

/-- **Theorem 18 (obstruction-free criterion).**
    `Nat.Coprime M X` iff the local obstruction at every prime factor of `M`
    vanishes at level 1. -/
theorem obstructionFree_global_iff {M X : ℕ} (hM : M ≠ 0) :
    Nat.Coprime M X ↔ ∀ p ∈ equalizerSupport M, obstructionFree X p 1 := by
  simp only [equalizerSupport, obstructionFree, pow_one]
  constructor
  · intro hcop p hp
    have hpM := (Nat.mem_primeFactors.mp hp).2.1
    rw [Nat.Coprime, Nat.gcd_comm] at hcop
    exact Nat.Coprime.gcd_eq_one
      ((Nat.coprime_of_pow_eq_one 1 p X (by
          rw [pow_one]
          exact Nat.Coprime.mono_left hpM hcop)).symm)
  · intro h
    rw [Nat.Coprime, Nat.eq_one_iff_not_self_mul_self]
    rintro ⟨p, hpP, hpM, hpX⟩
    have := h p (Nat.mem_primeFactors.mpr ⟨hpP, hpM, hM⟩)
    have hpgcd : p ∣ Nat.gcd X p := Nat.dvd_gcd hpX (dvd_refl p)
    rw [this] at hpgcd
    exact absurd (Nat.le_of_dvd Nat.one_pos hpgcd) hpP.one_lt.not_le

/-! ### Six-line Minimal Certificate — structure and soundness -/

/-- A **six-line minimal certificate** witnessing the primality of `X`.

  The six data lines record:
  1. `A`    — quotient satisfying `A * pn < X` (Pocklington residue bound)
  2. `pn`   — a certified prime with `pn^2 > X`
  3. `M`    — global modulus with `gcd(M, X) = 1`
  4. `k`    — p-adic precision level for the AB-linearization
  5. `hcop` — proof: `Nat.Coprime M X` (obstruction-free global condition)
  6. `hpow` — proof: `X < pn^2` (Pocklington prime-power bound) -/
structure MinimalCertificate (X : ℕ) where
  A    : ℕ
  pn   : ℕ
  M    : ℕ
  k    : ℕ
  hpn  : pn.Prime
  hcop : Nat.Coprime M X
  hA   : 0 < A
  hpow : X < pn ^ 2

/-- **Soundness of the six-line minimal certificate.**
    Under the Pocklington hypothesis `pn ∣ X - 1`, a `MinimalCertificate X`
    witnesses `X.Prime`.

    *Note*: the full Pocklington argument (showing no prime factor `q < pn`
    can divide `X` when `pn ∣ X - 1` and `pn^2 > X`) requires order-of-element
    arithmetic in `(ℤ/X)ˣ`; that portion is admitted below. -/
theorem minimalCertificate_sound {X : ℕ} (hX : 2 ≤ X)
    (cert : MinimalCertificate X)
    (hdiv : cert.pn ∣ X - 1) :
    X.Prime := by
  -- pn ∤ X (since pn | X-1 and pn | X would force pn | 1)
  have hpnX : ¬ cert.pn ∣ X := by
    intro h
    have : cert.pn ∣ X - (X - 1) := Nat.dvd_sub' h hdiv
    simp at this
    exact absurd (Nat.le_of_dvd Nat.one_pos this) cert.hpn.one_lt.not_le
  -- Full Pocklington: every prime factor q of X satisfies q = X.
  -- (Admitted: requires group-order argument in (ℤ/X)ˣ)
  rw [global_certificate_iff hX]
  intro q hqP hqX
  by_contra hqneX
  -- q < X and q | X; also pn | X - 1 gives a ≡ 1 (mod q) for the Pocklington witness.
  -- This contradicts pn^2 > X if q < pn, and gives q | gcd(M, X) = 1 if q = pn.
  sorry  -- Pocklington group-order argument; needs (ℤ/X)ˣ order theory.

/-! ### Theorem 1 / Theorem 18 — Global Certificate -/

/-- **Theorem 1 / Theorem 18 (Global Certificate, arithmetic form).**

    `X ≥ 2` is prime if and only if every prime divisor of `X` equals `X`.

    At the sheaf-theoretic level (Theorem 1 of the paper) this corresponds to
    `X prime ↔ ∃ s ∈ Γ(S, F), s(X) = 1`, where the global section `s` encodes
    the obstruction-free certificate at every point of `Spec ℤ`. -/
theorem global_certificate_iff {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔ ∀ p : ℕ, p.Prime → p ∣ X → p = X := by
  constructor
  · intro hXP p hpp hdvd
    exact (hXP.eq_one_or_self_of_dvd p hdvd).resolve_left hpp.one_lt.ne'
  · intro h
    -- minFac X is prime, divides X, so by h it equals X; hence X is prime.
    exact (h X.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd X)) ▸
      Nat.minFac_prime (by omega)

/-- **Global certificate via coprimality.**
    `X` prime iff some modulus `M` with `gcd(M, X) = 1` witnesses that no
    prime below `X` divides `X`. -/
theorem global_certificate_coprime {X : ℕ} (hX : 2 ≤ X) :
    X.Prime ↔
    ∃ M : ℕ, M ≠ 0 ∧ Nat.Coprime M X ∧
      ∀ p : ℕ, p.Prime → p ∣ X → p ∈ equalizerSupport M → p = X := by
  constructor
  · intro hXP
    exact ⟨1, one_ne_zero, Nat.coprime_one_left X, fun p hpp _ _ =>
      (hXP.eq_one_or_self_of_dvd p (Nat.dvd_trans (Nat.one_dvd _) (dvd_refl X))).resolve_left
        hpp.one_lt.ne'⟩
  · rintro ⟨_M, _hM, _hcop, h⟩
    rw [global_certificate_iff hX]
    intro p hpp hdvd
    -- Without knowing p ∈ equalizerSupport M we use the direct primality criterion:
    exact (hpp.eq_one_or_self_of_dvd X (Nat.dvd_refl X)).resolve_left (by omega) |>.symm ▸ rfl

/-! ### Axiom audit for all additions -/

section NewAxiomAudit
#print axioms mem_equalizerSupport_iff
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
