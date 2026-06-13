/-
Additional formalization layer for `Spt2.lean`.

This file is intentionally split into two parts.

1. `ActualAlgebra`: extra theorem-level formalizations that are already within
   the algebraic reach of Mathlib/Spt2.
2. `ReplacementTargets`: precise Lean targets for the remaining checklist items
   whose native objects are not yet available in Mathlib at the required level
   (etale cohomology, Voevodsky motives, scheme-level cotangent complexes,
   normalization exact sequences of singular curves, and sheaf/equalizer gluing).

To use inside the original repository, place this file next to `Spt2.lean` and
change the import below to the project path of Spt2, for example:

  import PrimalitySheafVerification.Spt2
-/

import PrimalitySheafVerification.Spt2

open Polynomial

namespace Spt2
namespace AdditionalFormalization

/-! ## 1. Extra algebraic formalization that should be theorem-level now. -/

namespace ActualAlgebra

variable {p : Nat} [Fact p.Prime]

/-- The reduction of an integral univariate equation modulo `p`. -/
noncomputable def reduceIntPolynomial (F : Int[X]) : (ZMod p)[X] :=
  F.map (Int.castRingHom (ZMod p))

/-- The discriminant/Jacobian good gate for a univariate special fiber. -/
def DiscriminantGate (f : (ZMod p)[X]) : Prop :=
  IsCoprime f (derivative f)

/-- The corresponding bad gate: the reduction has nontrivial gcd with its derivative. -/
def BadDiscriminantGate (f : (ZMod p)[X]) : Prop :=
  ¬ DiscriminantGate f

/-- The algebraic smoothness predicate for the univariate special fiber. -/
def UnivariateSmoothGate (f : (ZMod p)[X]) : Prop :=
  Squarefree f

/-! ### Affine hypersurface objects replacing the informal fiber notation.

For a univariate affine hypersurface, the special fiber over `p` is represented
by the genuine coordinate algebra `Fp[X]/(fbar)`, implemented in Mathlib as
`AdjoinRoot fbar`.  This is the affine `Spec` side of the scheme-theoretic fiber.
-/

/-- Integral affine hypersurface coordinate ring `Z[X]/(F)`. -/
abbrev IntegralHypersurfaceRing (F : Int[X]) : Type :=
  Int[X] ⧸ Ideal.span {F}

/-- Special fiber coordinate ring `Fp[X]/(f)`. -/
abbrev SpecialFiberRing (f : (ZMod p)[X]) : Type :=
  AdjoinRoot f

/-- Formal-etale smoothness of the affine special fiber. -/
def SpecialFiberFormallyEtale (f : (ZMod p)[X]) : Prop :=
  Algebra.FormallyEtale (ZMod p) (SpecialFiberRing f)

/-- Formal-unramifiedness of the affine special fiber. -/
def SpecialFiberFormallyUnramified (f : (ZMod p)[X]) : Prop :=
  Algebra.FormallyUnramified (ZMod p) (SpecialFiberRing f)

/-- Kähler detector for the affine special fiber. -/
def KaehlerSilent (f : (ZMod p)[X]) : Prop :=
  Subsingleton (Ω[SpecialFiberRing f ⁄ ZMod p])

/-- First cotangent cohomology detector for the affine special fiber. -/
def H1CotangentSilent (f : (ZMod p)[X]) : Prop :=
  Subsingleton (Algebra.H1Cotangent (ZMod p) (SpecialFiberRing f))

/-- The good gate is exactly squarefreeness.  This is the core of the full
Theorem 2.1 chain that is already genuinely formalized in Spt2. -/
theorem discriminantGate_iff_squarefree (f : (ZMod p)[X]) :
    DiscriminantGate f ↔ UnivariateSmoothGate f := by
  unfold DiscriminantGate UnivariateSmoothGate
  exact (squarefree_iff_coprime_derivative f).symm

/-- On the affine special fiber, Mathlib's genuine formal-etale predicate is
exactly the discriminant/gcd gate. -/
theorem specialFiberFormallyEtale_iff_discriminantGate
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    SpecialFiberFormallyEtale f ↔ DiscriminantGate f := by
  unfold SpecialFiberFormallyEtale SpecialFiberRing DiscriminantGate
  rw [JacobianReal.formallyEtale_iff_squarefree_of_ne_zero f hf,
    squarefree_iff_coprime_derivative]

/-- Monic version: formal-unramifiedness is exactly the discriminant/gcd gate. -/
theorem specialFiberFormallyUnramified_iff_discriminantGate
    (f : (ZMod p)[X]) (hm : f.Monic) :
    SpecialFiberFormallyUnramified f ↔ DiscriminantGate f := by
  unfold SpecialFiberFormallyUnramified SpecialFiberRing DiscriminantGate
  rw [JacobianReal.formallyUnramified_iff_squarefree f hm,
    squarefree_iff_coprime_derivative]

/-- Monic version: the Kähler detector vanishes exactly on the good gate. -/
theorem kaehlerSilent_iff_discriminantGate
    (f : (ZMod p)[X]) (hm : f.Monic) :
    KaehlerSilent f ↔ DiscriminantGate f := by
  unfold KaehlerSilent SpecialFiberRing DiscriminantGate
  rw [JacobianReal.subsingleton_kaehler_iff_squarefree f hm,
    squarefree_iff_coprime_derivative]

/-- Monic squarefree/good fibers have silent first cotangent cohomology. -/
theorem discriminantGate_imp_h1CotangentSilent
    (f : (ZMod p)[X]) (hm : f.Monic) (hgate : DiscriminantGate f) :
    H1CotangentSilent f := by
  unfold H1CotangentSilent SpecialFiberRing
  exact JacobianReal.h1Cotangent_subsingleton_of_squarefree f hm
    ((squarefree_iff_coprime_derivative f).mpr hgate)

/-- Badness is non-squarefreeness. -/
theorem badDiscriminantGate_iff_not_squarefree (f : (ZMod p)[X]) :
    BadDiscriminantGate f ↔ ¬ UnivariateSmoothGate f := by
  unfold BadDiscriminantGate
  rw [discriminantGate_iff_squarefree]

/-- A visible affine singular/critical residue point over the base field. -/
def HasFpCriticalPoint (f : (ZMod p)[X]) : Prop :=
  ∃ a : ZMod p, eval a f = 0 ∧ eval a (derivative f) = 0

/-- A critical point after scalar extension.  This is the correct formal shape
for the geometric clause in Theorem 2.1: a non-squarefree polynomial may fail to
have an `Fp`-rational repeated root, but it has one after passing to a splitting
field/geometric point. -/
def HasCriticalPointIn (A : Type*) [CommSemiring A] [Algebra (ZMod p) A]
    (f : (ZMod p)[X]) : Prop :=
  ∃ a : A,
    eval₂ (algebraMap (ZMod p) A) a f = 0 ∧
      eval₂ (algebraMap (ZMod p) A) a (derivative f) = 0

/-- A visible common zero of `f` and `f'` obstructs the discriminant gate.  The
converse needs a splitting/geometric-point hypothesis: repeated irreducible
factors need not have an `Fp`-rational root. -/
theorem criticalPoint_imp_badDiscriminantGate
    (f : (ZMod p)[X]) (hcrit : HasFpCriticalPoint f) :
    BadDiscriminantGate f := by
  unfold BadDiscriminantGate DiscriminantGate
  intro hcop
  obtain ⟨a, hf, hdf⟩ := hcrit
  obtain ⟨u, v, huv⟩ := hcop
  have h := congrArg (eval a) huv
  simp [eval_add, eval_mul, hf, hdf] at h

/-- The Bezout identity behind the discriminant gate rules out critical points
after every nontrivial scalar extension. -/
theorem isCoprime_imp_noCriticalPointIn
    (A : Type*) [CommSemiring A] [Algebra (ZMod p) A] [Nontrivial A]
    (f : (ZMod p)[X]) (hcop : IsCoprime f (derivative f)) :
    ¬ HasCriticalPointIn A f := by
  intro hcrit
  obtain ⟨a, hf, hdf⟩ := hcrit
  obtain ⟨u, v, huv⟩ := hcop
  have h := congrArg (eval₂ (algebraMap (ZMod p) A) a) huv
  simp [eval₂_add, eval₂_mul, hf, hdf] at h

/-- The good discriminant gate has no critical points over any nontrivial
extension algebra. -/
theorem discriminantGate_imp_noCriticalPointIn
    (A : Type*) [CommSemiring A] [Algebra (ZMod p) A] [Nontrivial A]
    (f : (ZMod p)[X]) (h : DiscriminantGate f) :
    ¬ HasCriticalPointIn A f :=
  isCoprime_imp_noCriticalPointIn A f h

/-- Squarefree fibers have no visible affine critical point over `Fp`. -/
theorem squarefree_imp_no_criticalPoint
    (f : (ZMod p)[X]) (hsf : Squarefree f) :
    ¬ HasFpCriticalPoint f := by
  intro hcrit
  exact criticalPoint_imp_badDiscriminantGate f hcrit
    ((discriminantGate_iff_squarefree f).mpr hsf)

/-- A visible critical point makes the genuine univariate Jacobian quotient
nontrivial. -/
theorem criticalPoint_imp_jacobianQuotient_nontrivial
    (f : (ZMod p)[X]) (hcrit : HasFpCriticalPoint f) :
    Nontrivial (JacobianReal.JacobianQuotient f) := by
  rw [JacobianReal.jacobianQuotient_nontrivial_iff]
  exact (badDiscriminantGate_iff_not_squarefree f).mp
    (criticalPoint_imp_badDiscriminantGate f hcrit)

/-- Bad discriminant gate is exactly nontriviality of the genuine Jacobian
quotient `Fp[X]/(f,f')`. -/
theorem badDiscriminantGate_iff_jacobianQuotient_nontrivial
    (f : (ZMod p)[X]) :
    BadDiscriminantGate f ↔ Nontrivial (JacobianReal.JacobianQuotient f) := by
  unfold BadDiscriminantGate
  rw [JacobianReal.jacobianQuotient_nontrivial_iff,
    discriminantGate_iff_squarefree]

/-- Good discriminant gate is exactly triviality of the genuine Jacobian quotient. -/
theorem discriminantGate_iff_jacobianQuotient_subsingleton
    (f : (ZMod p)[X]) :
    DiscriminantGate f ↔ Subsingleton (JacobianReal.JacobianQuotient f) := by
  unfold DiscriminantGate
  exact (JacobianReal.derived_eq_algebraic_gate f).symm

/-- For nonzero `f`, the good gate is exactly vanishing of the Jacobian-quotient
length. -/
theorem discriminantGate_iff_localLength_eq_zero
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    DiscriminantGate f ↔ JacobianReal.localLength f = 0 := by
  rw [discriminantGate_iff_squarefree,
    ← JacobianReal.localLength_eq_zero_iff f hf]

/-- For nonzero `f`, the bad gate is exactly positive/nonzero local length. -/
theorem badDiscriminantGate_iff_localLength_ne_zero
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    BadDiscriminantGate f ↔ JacobianReal.localLength f ≠ 0 := by
  unfold BadDiscriminantGate
  rw [discriminantGate_iff_localLength_eq_zero f hf]

/-- A theorem-level replacement for the algebraic part of Theorem 2.1:
squarefreeness, gcd gate, Jacobian ideal being the unit ideal, Jacobian quotient
vanishing, and local length vanishing are all equivalent. -/
theorem theorem_2_1_algebraic_TFAE
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    [ UnivariateSmoothGate f,
      DiscriminantGate f,
      JacobianReal.jacobianIdeal f = ⊤,
      Subsingleton (JacobianReal.JacobianQuotient f),
      JacobianReal.localLength f = 0 ].TFAE := by
  tfae_have 1 ↔ 2 := by
    exact (discriminantGate_iff_squarefree f).symm
  tfae_have 2 ↔ 3 := by
    unfold DiscriminantGate
    exact (JacobianReal.jacobianIdeal_eq_top_iff_coprime f).symm
  tfae_have 2 ↔ 4 := discriminantGate_iff_jacobianQuotient_subsingleton f
  tfae_have 2 ↔ 5 := discriminantGate_iff_localLength_eq_zero f hf
  tfae_finish

/-- Singular/bad version of the same algebraic chain. -/
theorem theorem_2_1_bad_algebraic_TFAE
    (f : (ZMod p)[X]) (hf : f ≠ 0) :
    [ BadDiscriminantGate f,
      ¬ UnivariateSmoothGate f,
      Nontrivial (JacobianReal.JacobianQuotient f),
      JacobianReal.localLength f ≠ 0 ].TFAE := by
  tfae_have 1 ↔ 2 := badDiscriminantGate_iff_not_squarefree f
  tfae_have 1 ↔ 3 := badDiscriminantGate_iff_jacobianQuotient_nontrivial f
  tfae_have 1 ↔ 4 := badDiscriminantGate_iff_localLength_ne_zero f hf
  tfae_finish

/-! ### Multivariate Jacobian gate: actual formal-smoothness direction. -/

namespace Multivariate

open MvPolynomial

variable {n : Nat}

/-- The gradient ideal in the hypersurface coordinate algebra
`Fp[x_0,...,x_{n-1}]/(f)`. -/
noncomputable def GradientIdealInQuotient
    (f : MvPolynomial (Fin n) (ZMod p)) :
    Ideal (MvPolynomial (Fin n) (ZMod p) ⧸ Ideal.span {f}) :=
  Ideal.span (Set.range fun i =>
    Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))

/-- The Jacobian full-rank gate for a multivariate hypersurface. -/
def GradientFullRankGate
    (f : MvPolynomial (Fin n) (ZMod p)) : Prop :=
  GradientIdealInQuotient f = ⊤

/-- Actual theorem-level Jacobian criterion direction already supported by
Mathlib/Spt2: if the gradient ideal is the unit ideal in the hypersurface
coordinate algebra, then the affine hypersurface is formally smooth over `Fp`. -/
theorem gradientFullRankGate_imp_formallySmooth
    (f : MvPolynomial (Fin n) (ZMod p))
    (h : GradientFullRankGate f) :
    Algebra.FormallySmooth (ZMod p)
      (MvPolynomial (Fin n) (ZMod p) ⧸ Ideal.span {f}) := by
  unfold GradientFullRankGate GradientIdealInQuotient at h
  exact JacobianMv.formallySmooth_of_grad_span_eq_top f h

/-- Formal smoothness makes the first cotangent cohomology silent after this
multivariate Jacobian gate. -/
theorem gradientFullRankGate_imp_h1CotangentSilent
    (f : MvPolynomial (Fin n) (ZMod p))
    (h : GradientFullRankGate f) :
    Subsingleton
      (Algebra.H1Cotangent (ZMod p)
        (MvPolynomial (Fin n) (ZMod p) ⧸ Ideal.span {f})) := by
  haveI : Algebra.FormallySmooth (ZMod p)
      (MvPolynomial (Fin n) (ZMod p) ⧸ Ideal.span {f}) :=
    gradientFullRankGate_imp_formallySmooth f h
  infer_instance

end Multivariate

/-! ### Benchmark strengthening for `x^(pn) + y^A`.

This does not yet replace the localized two-variable Jacobian quotient length,
but it makes the current `tau` model theorem-level: finiteness, the off-origin
Jacobian gate, and the Hensel union gate are all equivalent.
-/

namespace Benchmark

/-- In the benchmark model, finite `tau`, off-origin Jacobian full rank, and the
Hensel union gate are equivalent. -/
theorem tau_finite_gate_TFAE (p : Nat) (M : Spt2.Model) :
    [ Spt2.tau p M ≠ ⊤,
      Spt2.jacFullRankOffOrigin p M,
      Spt2.henselUnion p M ].TFAE := by
  tfae_have 1 ↔ 2 := by
    rw [Spt2.tau_ne_top_iff]
    rfl
  tfae_have 2 ↔ 3 := (Spt2.gate_eq_jacobian p M).symm
  tfae_finish

/-- On the strict good open `D(A*pn)`, the benchmark has finite local length and
the Jacobian/Hensel gates pass. -/
theorem goodOpen_tau_finite_and_gates (p : Nat) (M : Spt2.Model)
    (h : Spt2.goodOpen p M) :
    Spt2.tau p M ≠ ⊤ ∧
      Spt2.jacFullRankOffOrigin p M ∧
        Spt2.henselUnion p M := by
  have htau :
      Spt2.tau p M =
        (((M.pn - 1) * (M.A - 1) : Nat) : ℕ∞) :=
    Spt2.goodOpen_tau p M h
  have hfinite : Spt2.tau p M ≠ ⊤ := by
    rw [htau]
    exact ENat.coe_ne_top _
  have hunion : Spt2.henselUnion p M := Spt2.goodOpen_imp_union p M h
  have hjac : Spt2.jacFullRankOffOrigin p M :=
    (Spt2.gate_eq_jacobian p M).mp hunion
  exact ⟨hfinite, hjac, hunion⟩

end Benchmark

/-- A certificate replacing the informal statement
`p | Delta <-> gcd(fbar, fbar') != 1`.

For a concrete family this field should be proved from Mathlib's
resultant/discriminant API.  Keeping it as a certificate is strictly better than
burying it as a hidden assumption: every theorem below exposes the exact
remaining input. -/
structure DiscriminantCertificate (F : Int[X]) (Delta : Int) where
  squarefree_mod_iff_not_dvd :
    ∀ (q : Nat) [Fact q.Prime],
      Squarefree (reduceIntPolynomial (p := q) F) ↔ ¬ ((q : Int) ∣ Delta)

/-- Good primes as the principal open `D(Delta)` on `Spec Z`, represented
arithmetically as non-divisibility. -/
def GoodPrimeByDelta (Delta : Int) (q : Nat) : Prop :=
  ¬ ((q : Int) ∣ Delta)

/-- Bad primes are the closed support `V(Delta)`, represented arithmetically as
divisibility. -/
def BadPrimeByDelta (Delta : Int) (q : Nat) : Prop :=
  (q : Int) ∣ Delta

/-- The certified discriminant statement gives the good-prime/squarefree gate. -/
theorem goodPrimeByDelta_iff_squarefree_mod
    {F : Int[X]} {Delta : Int} (C : DiscriminantCertificate F Delta)
    (q : Nat) [Fact q.Prime] :
    GoodPrimeByDelta Delta q ↔ Squarefree (reduceIntPolynomial (p := q) F) := by
  exact (C.squarefree_mod_iff_not_dvd q).symm

/-- The same certificate gives the bad-prime/gcd-failure gate. -/
theorem badPrimeByDelta_iff_badDiscriminantGate
    {F : Int[X]} {Delta : Int} (C : DiscriminantCertificate F Delta)
    (q : Nat) [Fact q.Prime] :
    BadPrimeByDelta Delta q ↔
      BadDiscriminantGate (reduceIntPolynomial (p := q) F) := by
  unfold BadPrimeByDelta BadDiscriminantGate DiscriminantGate
  constructor
  · intro hbad hcop
    have hsf : Squarefree (reduceIntPolynomial (p := q) F) :=
      (squarefree_iff_coprime_derivative _).mpr hcop
    exact ((C.squarefree_mod_iff_not_dvd q).mp hsf) hbad
  · intro hbad
    by_contra hnot
    have hsf : Squarefree (reduceIntPolynomial (p := q) F) :=
      (C.squarefree_mod_iff_not_dvd q).mpr hnot
    exact hbad ((squarefree_iff_coprime_derivative _).mp hsf)

/-- The part of Theorem 2.1 that is mathematically sound over the base field:
a visible critical point implies bad prime.  The reverse direction belongs over
a splitting field or geometric point, not necessarily over `Fp`. -/
theorem theorem_2_1_visible_point_direction
    {F : Int[X]} {Delta : Int} (C : DiscriminantCertificate F Delta)
    (q : Nat) [Fact q.Prime]
    (hcrit : HasFpCriticalPoint (reduceIntPolynomial (p := q) F)) :
    BadPrimeByDelta Delta q := by
  exact (badPrimeByDelta_iff_badDiscriminantGate C q).mpr
    (criticalPoint_imp_badDiscriminantGate _ hcrit)

end ActualAlgebra

/-! ## 2. Replacement targets for the remaining checklist.

The declarations below are not pretending to prove etale/motivic/derived
geometry from nothing.  They are a precise interface showing which current
`ArithmeticCurve` fields in `Spt2.lean` must eventually be replaced by actual
definitions and theorems once the required Mathlib foundations exist.
-/

namespace ReplacementTargets

/-- Target for the arithmetic-curve object layer:
replace the current `Prop`/`Nat` package by actual schemes and morphisms. -/
structure ArithmeticCurveObjects where
  BaseScheme : Type
  TotalScheme : Type
  pi : TotalScheme -> BaseScheme
  FiberAt : Nat -> Type
  LocalizationAtPrincipalOpen : Int -> Type
  CompletionAtPrime : Nat -> Type
  BaseChangeTo : Type -> Type

/-- Target for the discriminant/open layer.  In the final version, `isMaximal`
should state that `D(Delta)` is the maximal open over which the morphism is
smooth. -/
structure DiscriminantOpenPackage where
  FamilyEquation : Int[X]
  Delta : Int
  GoodPrime : Nat -> Prop
  BadPrime : Nat -> Prop
  SmoothFiber : Nat -> Prop
  good_iff_not_dvd_delta : ∀ p, GoodPrime p ↔ ¬ ((p : Int) ∣ Delta)
  bad_iff_dvd_delta : ∀ p, BadPrime p ↔ ((p : Int) ∣ Delta)
  good_iff_smooth : ∀ p, GoodPrime p ↔ SmoothFiber p
  isMaximalSmoothOpen : Prop

/-- Target for Hensel lifting over an actual p-adic integer ring. -/
structure HenselGatePackage where
  p : Nat
  ResidueField : Type
  PadicIntegers : Type
  reduce : PadicIntegers -> ResidueField
  f : PadicIntegers -> PadicIntegers
  df : PadicIntegers -> PadicIntegers
  residueRoot : ResidueField -> Prop
  simpleResidueRoot : ResidueField -> Prop
  liftOf : ResidueField -> PadicIntegers -> Prop
  uniqueLift : ResidueField -> Prop
  hensel_gate_iff_discriminant_gate : Prop

/-- Target for the etale bump.  `H1Et` should eventually be actual etale
cohomology, not a raw natural number. -/
structure EtaleBumpPackage where
  Fiber : Type
  SmoothOpen : Type
  Coefficients : Type
  H1Et : Type -> Type -> Type
  finrankH1Fiber : Nat
  finrankH1SmoothOpen : Nat
  bump : Nat
  bump_eq_difference : bump = finrankH1Fiber - finrankH1SmoothOpen

/-- Target for defect motives and motivic Euler jumps. -/
structure MotivePackage where
  BaseField : Type
  MotiveCategory : Type
  CompactMotive : Type -> MotiveCategory
  jShriek : MotiveCategory -> MotiveCategory
  Cone : MotiveCategory -> MotiveCategory -> MotiveCategory
  DefectMotive : MotiveCategory
  EulerCharacteristic : MotiveCategory -> Int
  realizationCompatible : Prop
  euler_additive_for_localization_triangle : Prop

/-- Target for normalization data of a singular curve. -/
structure NormalizationPackage where
  Curve : Type
  Normalization : Type
  normalizationMap : Normalization -> Curve
  SingularPoint : Type
  singularFinite : Prop
  DualGraph : Type
  firstBetti : DualGraph -> Nat
  deltaInvariant : SingularPoint -> Nat
  deltaFiniteLengthDefinition : Prop

/-- Target for the normalization/LHS exact-sequence calculation. -/
structure NormalizationExactSequencePackage extends NormalizationPackage where
  genusNormalization : Nat
  dimH1Curve : Nat
  dimH1SmoothOpen : Nat
  dualGraph : DualGraph
  deltaSum : Nat
  h1_curve_formula :
    dimH1Curve = 2 * genusNormalization + firstBetti dualGraph + deltaSum
  h1_open_formula :
    dimH1SmoothOpen = 2 * genusNormalization

/-- Target theorem package for etale = motivic on curves. -/
structure EtaleMotivicEqualityPackage where
  bump : Nat
  eulerJump : Nat
  b1 : Nat
  deltaSum : Nat
  bump_formula : bump = b1 + deltaSum
  eulerJump_formula : eulerJump = b1 + deltaSum
  etale_eq_motivic : bump = eulerJump

/-- Target for the scheme-level cotangent-complex detector. -/
structure DerivedDetectorPackage where
  Fiber : Type
  CotangentComplex : Type
  H1CotangentComplex : Type
  Smooth : Prop
  TorAmplitudeInZero : Prop
  H1Vanishes : Prop
  smooth_iff_torAmplitude_zero : Smooth ↔ TorAmplitudeInZero
  torAmplitude_zero_iff_h1_vanishes_for_curves : TorAmplitudeInZero ↔ H1Vanishes
  derived_detector_iff_smooth : H1Vanishes ↔ Smooth

/-- Target for complete-intersection Jacobian rank via minors/Fitting ideals. -/
structure CIJacobianPackage where
  CoordinateRing : Type
  EquationIndex : Type
  VariableIndex : Type
  JacobianMatrix : Type
  MaximalMinorsIdeal : Type
  FittingIdeal : Type
  FullRankAtPoint : Type -> Prop
  SmoothAtPoint : Type -> Prop
  jacobian_rank_iff_smooth_at_point : ∀ x, FullRankAtPoint x ↔ SmoothAtPoint x
  chartwise_global_smoothness : Prop

/-- Target for replacing the piecewise benchmark `tau` by an actual localized
Jacobian quotient length of `x^(pn) + y^A`. -/
structure BenchmarkLengthPackage where
  p pn A : Nat
  hpn : 2 <= pn
  hA : 2 <= A
  PolynomialXY : Type
  OriginLocalRing : Type
  JacobianIdealAtOrigin : Type
  JacobianQuotientAtOrigin : Type
  Length : WithTop Nat
  finite_iff_isolated :
    Length ≠ ⊤ ↔ ¬ (p ∣ pn ∧ p ∣ A)
  agrees_with_piecewise_tau :
    Length = Spt2.tau p ⟨pn, A, hpn, hA⟩

/-- Target for sheaf/equalizer gluing on principal opens. -/
structure PrincipalOpenSheafGluingPackage where
  Section : Type
  D : Int -> Type
  restrict : ∀ {a b : Int}, Section -> Section
  equalizerCondition : Prop
  crtCoverGluing : ∀ a b : Nat, Nat.Coprime a b -> Prop
  detectorPredicateSheaf : Prop

/-- A final status package: in the completed formalization these should be
actual theorems, not fields. -/
structure PaperFieldReplacementStatus where
  alg_iff_motivicSilent_replaced : Prop
  etale_motivic_equality_replaced : Prop
  derived_dimension_formula_replaced : Prop
  transport_stability_replaced : Prop
  all_ArithmeticCurve_bridge_fields_removed : Prop

end ReplacementTargets

end AdditionalFormalization
end Spt2
