/-
================================================================================
  Spt2_CompletionLayer.lean

  Genuine Mathlib-level completions that close the *algebraically reachable*
  gaps left open by the three existing SPT2 layers
  (`Spt2.lean` / `Spt2_AdditionalFormalization.lean` / `Spt2_BypassCertificate.lean`).

  Everything in this file is a real theorem proved from Mathlib — NOT a
  certificate field and NOT a numeric model:

    * Theorem 2.1, condition (1): the resultant/discriminant gate
        `Res(f, f') = 0  ↔  ¬ Squarefree f`              (was missing)
    * Theorem 2.1, condition (4): the geometric critical point over a
        geometric point / algebraic closure
        `¬ Squarefree f ↔ ∃ a ∈ K̄, f(a) = f'(a) = 0`    (only one direction
        was available before; the converse needed a geometric point)
    * The full four-condition Theorem 2.1 TFAE, assembled genuinely.
    * The benchmark `f = xᵖⁿ + yᴬ` non-isolated case as a REAL bivariate
        statement: when `p ∣ pn` and `p ∣ A` the genuine multivariate Jacobian
        ideal collapses to `(f)`, so the Jacobian quotient is the full
        (non-Artinian) hypersurface ring — the algebraic reason `τ = ⊤`.
    * Anchoring: the bypass certificate's `AlgebraicCore` is *constructed* from a
        genuine nonzero polynomial, proving it is inhabited by real objects.

  No `sorry`, no project `axiom`.
================================================================================
-/
import PrimalitySheafVerification.Spt2
import PrimalitySheafVerification.Spt2_AdditionalFormalization
import PrimalitySheafVerification.Spt2_BypassCertificate
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Polynomial

namespace Spt2
namespace CompletionLayer

variable {p : ℕ} [Fact p.Prime]

/-! ## A. Theorem 2.1, condition (1): the resultant / discriminant gate.

The existing layers prove the chain (2)⇔(3)⇔(4)⇔(5) of Theorem 2.1
(`Squarefree f ⇔ IsCoprime f f' ⇔ Jacobian ideal = ⊤ ⇔ quotient trivial ⇔
local length 0`).  The paper's condition (1), `p ∣ Δ(f)`, equivalently
`Res(f, f') = 0`, was not formalized.  We close it with Mathlib's
`resultant_eq_zero_iff`. -/

/-- **Theorem 2.1, (1)⇔(2) — bad resultant gate.**  For nonzero `f` over `𝔽_p`,
the resultant `Res(f, f')` vanishes iff `f` has a multiple root (is not
squarefree).  This is the discriminant gate of the paper. -/
theorem resultant_derivative_eq_zero_iff_not_squarefree
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    f.resultant (derivative f) = 0 ↔ ¬ Squarefree f := by
  rw [resultant_eq_zero_iff, squarefree_iff_coprime_derivative]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨Or.inl hf, h⟩

/-- **Theorem 2.1, good resultant gate.**  For nonzero `f`, the resultant is
nonzero iff `f` is squarefree (the good discriminant open `D(Δ)`). -/
theorem resultant_derivative_ne_zero_iff_squarefree
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    f.resultant (derivative f) ≠ 0 ↔ Squarefree f := by
  rw [ne_eq, resultant_derivative_eq_zero_iff_not_squarefree f hf, not_not]

/-! ## B. Theorem 2.1, condition (4): the geometric critical point.

`Spt2_AdditionalFormalization` proved only the *visible*-point direction
(`HasFpCriticalPoint → ¬ DiscriminantGate`) and explicitly flagged that the
converse requires passing to a splitting field / geometric point.  Over any
algebraically closed extension `K / 𝔽_p` we now prove the full biconditional
using `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`. -/

/-- A geometric critical point of `f` in an extension `K`: a common zero of `f`
and `f'` after scalar extension (the scheme-theoretic singular point of
`{f = 0}` at a geometric point). -/
def HasCriticalPoint (K : Type*) [Field K] [Algebra (ZMod p) K]
    (f : (ZMod p)[X]) : Prop :=
  ∃ a : K, aeval a f = 0 ∧ aeval a (derivative f) = 0

/-- **Theorem 2.1, (2)⇔(4) over a geometric point.**  For any algebraically
closed extension `K / 𝔽_p`, the fiber `{f = 0}` is singular (`f` not squarefree)
iff `f` and `f'` have a common geometric zero in `K`. -/
theorem not_squarefree_iff_hasCriticalPoint
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (f : (ZMod p)[X]) :
    ¬ Squarefree f ↔ HasCriticalPoint K f := by
  rw [squarefree_iff_coprime_derivative,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ZMod p) K f (derivative f)]
  simp only [not_forall, not_or, not_not]
  rfl

/-- The contrapositive good-locus form: smoothness (squarefree) is exactly the
absence of geometric critical points over `K`. -/
theorem squarefree_iff_no_criticalPoint
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (f : (ZMod p)[X]) :
    Squarefree f ↔ ¬ HasCriticalPoint K f := by
  rw [← not_squarefree_iff_hasCriticalPoint K f, not_not]

/-! ## C. The complete Theorem 2.1 (all four paper conditions, genuinely). -/

/-- **Theorem 2.1 (full, genuine).**  Over a geometric point `K = 𝔽̄_p` and for
nonzero `f`, the four conditions of the paper — the discriminant/resultant gate,
the gcd gate, the geometric singular point, and the genuine Jacobian-quotient
(derived) detector — are all equivalent, together with positive local length. -/
theorem theorem_2_1_full_TFAE
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    [ ¬ Squarefree f,
      ¬ IsCoprime f (derivative f),
      f.resultant (derivative f) = 0,
      HasCriticalPoint K f,
      Nontrivial (JacobianReal.JacobianQuotient f),
      JacobianReal.localLength f ≠ 0 ].TFAE := by
  tfae_have 1 ↔ 2 := not_congr (squarefree_iff_coprime_derivative f)
  tfae_have 1 ↔ 3 := (resultant_derivative_eq_zero_iff_not_squarefree f hf).symm
  tfae_have 1 ↔ 4 := not_squarefree_iff_hasCriticalPoint K f
  tfae_have 1 ↔ 5 := (JacobianReal.jacobianQuotient_nontrivial_iff f).symm
  tfae_have 1 ↔ 6 := (not_congr (JacobianReal.localLength_eq_zero_iff f hf)).symm
  tfae_finish

/-! ## D. Benchmark `f = xᵖⁿ + yᴬ`: the genuine non-isolated (`τ = ⊤`) case.

`Spt2.lean` encodes the corrected `τ = ⊤` value in the regime `p ∣ pn ∧ p ∣ A`
inside the ℕ∞ piecewise model.  Here we give the REAL algebraic reason at the
level of the genuine bivariate Jacobian quotient `𝔽_p[x,y]/(f, ∂ₓf, ∂_yf)`:
in that regime both partials vanish identically (their integer coefficients
`pn`, `A` die in characteristic `p`), so the Jacobian ideal collapses to `(f)`
and the quotient is the whole one-dimensional hypersurface ring — a non-isolated
singularity of infinite length. -/

namespace Benchmark

open MvPolynomial

/-- The benchmark hypersurface `f = xᵖⁿ + yᴬ` as a genuine bivariate polynomial
over `𝔽_p`. -/
noncomputable def benchSurface (pn A : ℕ) : MvPolynomial (Fin 2) (ZMod p) :=
  X 0 ^ pn + X 1 ^ A

/-- In residue characteristic dividing `pn`, the `x`-partial of the benchmark
vanishes identically: `∂ₓ(xᵖⁿ + yᴬ) = pn·xᵖⁿ⁻¹ = 0` since `(pn : 𝔽_p) = 0`. -/
theorem pderiv_zero_benchSurface (pn A : ℕ) (hpn : p ∣ pn) :
    pderiv 0 (benchSurface (p := p) pn A) = 0 := by
  have hcast : ((pn : ℕ) : MvPolynomial (Fin 2) (ZMod p)) = 0 := by
    rw [← map_natCast (C : ZMod p →+* MvPolynomial (Fin 2) (ZMod p)) pn,
      (ZMod.natCast_eq_zero_iff pn p).mpr hpn, map_zero]
  have hX1 : pderiv (0 : Fin 2) (X 1 : MvPolynomial (Fin 2) (ZMod p)) = 0 := by
    rw [pderiv_X]; simp
  simp only [benchSurface, map_add, pderiv_pow, pderiv_X_self, hX1,
    mul_one, mul_zero, hcast, zero_mul, add_zero]

/-- In residue characteristic dividing `A`, the `y`-partial vanishes identically. -/
theorem pderiv_one_benchSurface (pn A : ℕ) (hA : p ∣ A) :
    pderiv 1 (benchSurface (p := p) pn A) = 0 := by
  have hcast : ((A : ℕ) : MvPolynomial (Fin 2) (ZMod p)) = 0 := by
    rw [← map_natCast (C : ZMod p →+* MvPolynomial (Fin 2) (ZMod p)) A,
      (ZMod.natCast_eq_zero_iff A p).mpr hA, map_zero]
  have hX0 : pderiv (1 : Fin 2) (X 0 : MvPolynomial (Fin 2) (ZMod p)) = 0 := by
    rw [pderiv_X]; simp
  simp only [benchSurface, map_add, pderiv_pow, pderiv_X_self, hX0,
    mul_one, mul_zero, hcast, zero_mul, add_zero]

/-- **Jacobian-ideal collapse (non-isolated regime).**  When `p ∣ pn` and
`p ∣ A`, the genuine bivariate Jacobian ideal of the benchmark equals the
principal ideal `(f)`: the singularity at the origin is non-isolated. -/
theorem jacobianIdeal_benchSurface_collapse
    (pn A : ℕ) (hpn : p ∣ pn) (hA : p ∣ A) :
    JacobianMv.jacobianIdeal (benchSurface (p := p) pn A)
      = Ideal.span {benchSurface (p := p) pn A} := by
  have h0 : ∀ i : Fin 2, pderiv i (benchSurface (p := p) pn A) = 0 := by
    intro i; fin_cases i
    · exact pderiv_zero_benchSurface pn A hpn
    · exact pderiv_one_benchSurface pn A hA
  have hrange : (Set.range fun i => pderiv i (benchSurface (p := p) pn A))
      = ({0} : Set (MvPolynomial (Fin 2) (ZMod p))) := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; exact h0 i
    · rintro rfl; exact ⟨0, h0 0⟩
  unfold JacobianMv.jacobianIdeal
  rw [hrange]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx0
    · exact Ideal.mem_span_singleton_self _
    · rw [Set.mem_singleton_iff] at hx0; subst hx0
      exact (Ideal.span {benchSurface (p := p) pn A}).zero_mem
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (Set.mem_insert _ _)

/-- The benchmark equation is never a unit: its value at the origin is `0`. -/
theorem benchSurface_not_isUnit (pn A : ℕ) (hpn : 2 ≤ pn) (hA : 2 ≤ A) :
    ¬ IsUnit (benchSurface (p := p) pn A) := by
  intro hu
  have hval : MvPolynomial.eval (fun _ => (0 : ZMod p)) (benchSurface (p := p) pn A) = 0 := by
    simp only [benchSurface, map_add, map_pow, MvPolynomial.eval_X]
    rw [zero_pow (by omega : pn ≠ 0), zero_pow (by omega : A ≠ 0), add_zero]
  have := hu.map (MvPolynomial.eval (fun _ => (0 : ZMod p)))
  rw [hval] at this
  exact not_isUnit_zero this

/-- **Non-isolated singularity (genuine derived detector).**  In the regime
`p ∣ pn ∧ p ∣ A` the genuine bivariate Jacobian quotient
`𝔽_p[x,y]/(f, ∂ₓf, ∂_yf)` is NOT trivial: it is the full hypersurface ring,
of infinite length — the real meaning of the corrected value `τ = ⊤`. -/
theorem benchSurface_jacobianQuotient_nontrivial
    (pn A : ℕ) (hpn : 2 ≤ pn) (hA : 2 ≤ A) (hp : p ∣ pn) (hpA : p ∣ A) :
    ¬ Subsingleton (JacobianMv.JacobianQuotient (benchSurface (p := p) pn A)) := by
  rw [JacobianMv.jacobianQuotient_subsingleton_iff,
    jacobianIdeal_benchSurface_collapse pn A hp hpA, Ideal.span_singleton_eq_top]
  exact benchSurface_not_isUnit pn A hpn hA

/-- **Consistency with the corrected ℕ∞ model.**  The same regime that makes the
genuine Jacobian quotient non-isolated is exactly the regime in which the
piecewise `Spt2.tau` takes the corrected value `⊤`. -/
omit [Fact p.Prime] in
theorem benchSurface_tau_top
    (pn A : ℕ) (hpn : 2 ≤ pn) (hA : 2 ≤ A) (hp : p ∣ pn) (hpA : p ∣ A) :
    Spt2.tau p ⟨pn, A, hpn, hA⟩ = ⊤ :=
  Spt2.tau_both p ⟨pn, A, hpn, hA⟩ hp hpA

end Benchmark

/-! ## E. Anchoring: the bypass certificate's algebraic core is realizable.

`BypassCertificate.AlgebraicCore` is an interface package.  We *construct* one
from any genuine nonzero `f` over `𝔽_p`, proving every field from the real
`JacobianReal` theorems.  This certifies the interface is inhabited by actual
Mathlib objects (squarefreeness, the genuine Jacobian ideal/quotient, the real
finite length), not a vacuous abstraction. -/

/-- A genuine `AlgebraicCore` built from a nonzero univariate `f` over `𝔽_p`.
Each equivalence field is discharged by a real theorem of `JacobianReal`. -/
noncomputable def algebraicCoreOf (f : (ZMod p)[X]) (hf : f ≠ 0) :
    BypassCertificate.AlgebraicCore where
  smooth := Squarefree f
  discriminantGate := IsCoprime f (derivative f)
  jacobianUnit := JacobianReal.jacobianIdeal f = ⊤
  jacobianQuotientSilent := Subsingleton (JacobianReal.JacobianQuotient f)
  localLength := JacobianReal.localLength f
  discriminant_iff_smooth := (squarefree_iff_coprime_derivative f).symm
  discriminant_iff_jacobianUnit := (JacobianReal.jacobianIdeal_eq_top_iff_coprime f).symm
  jacobianUnit_iff_quotientSilent :=
    (JacobianReal.jacobianIdeal_eq_top_iff_squarefree f).trans
      (JacobianReal.jacobianQuotient_subsingleton_iff f).symm
  localLength_zero_iff_jacobianUnit :=
    (JacobianReal.localLength_eq_zero_iff f hf).trans
      (JacobianReal.jacobianIdeal_eq_top_iff_squarefree f).symm

/-- The realized core reproduces the algebraic TFAE of Theorem 2.1 — now with
every entry a genuine Mathlib object attached to the concrete polynomial `f`. -/
theorem algebraicCoreOf_TFAE (f : (ZMod p)[X]) (hf : f ≠ 0) :
    [ (algebraicCoreOf f hf).smooth,
      (algebraicCoreOf f hf).discriminantGate,
      (algebraicCoreOf f hf).jacobianUnit,
      (algebraicCoreOf f hf).jacobianQuotientSilent,
      (algebraicCoreOf f hf).localLength = 0 ].TFAE :=
  (algebraicCoreOf f hf).algebraic_TFAE

end CompletionLayer
end Spt2

/-! ## Axiom audit for the genuine completion layer. -/
section AxiomAudit
#print axioms Spt2.CompletionLayer.resultant_derivative_eq_zero_iff_not_squarefree
#print axioms Spt2.CompletionLayer.not_squarefree_iff_hasCriticalPoint
#print axioms Spt2.CompletionLayer.theorem_2_1_full_TFAE
#print axioms Spt2.CompletionLayer.Benchmark.jacobianIdeal_benchSurface_collapse
#print axioms Spt2.CompletionLayer.Benchmark.benchSurface_jacobianQuotient_nontrivial
#print axioms Spt2.CompletionLayer.Benchmark.benchSurface_tau_top
#print axioms Spt2.CompletionLayer.algebraicCoreOf_TFAE
end AxiomAudit
