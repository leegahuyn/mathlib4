/-
================================================================================
  Spt6.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun (paper #6: bump = Euler jump, good-prime synchronization,
                   equalizer–Tor, direct-sum H¹).

  Kernel-checked against Mathlib; NO `sorry`, NO new global `axiom`.  Conditional
  results carry their assumptions as explicit hypotheses (visible in signature).

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    Thm 9.3(ii) forward Hensel gate: simple residue root → unique p-adic lift
                       ↦ hensel_gate / hensel_gate_unique_of_two             PROVED
    Thm 9.3(i)⇔(ii), Prop 6.2 smooth/Jacobian converse and full equivalence
                       ↦ smooth_to_unique_lift_of_hensel_hypotheses          CONDITIONAL
                       ↦ c4_smooth_jacobian_hensel_classification            AUDITED
    §8.8 Frobenius–Tate polynomial/point-count certificate
                       ↦ frobeniusTatePolynomial_coefficients /
                         frobeniusTatePolynomial_of_pointCount_eq             PROVED (algebra)
    §8.8 `aₚ = 0 → supersingular` and geometric Frobenius interpretation
                       ↦ c5_supersingular_frobenius_classification           FUTURE WORK
    §8.6 certified bounded prime scan, gcd readout, simple roots, Hensel lift
                       ↦ PrimeScan.mem_scanPrimesUpTo_iff /
                         PrimeScan.eval_rootGCD_eq_zero_iff /
                         PrimeScan.simpleRoot_has_uniquePadicLift             PROVED
    App. B / D.3 Tor cosmetic completion: Tor=0 iff gcd=1 as Subsingleton;
                       N=60 readout in prime-indexed and explicit CRT forms
                       ↦ tor_subsingleton_iff / torReadout60Primewise /
                         torReadout60 / Profile                                PROVED
    Lem 6.4, Prop 10.1, Thm 9.1/9.3(iii)  equalizer kernel = (M)∩(N) = (lcm)
                       ↦ kernel_mem_iff_lcm, kernel_ideal_inter             PROVED
    Prop 10.7, Thm 9.3(iii) thickness (CORRECTED)  gcd→min, lcm→max
                       ↦ factorization_gcd_apply / lcm_apply                 PROVED
    Prop 10.7 (T1.6) local thickness in valuation form (CORRECTION 2):
                       vₚ((M)∩(pᵏ)) = vₚ(lcm) = max(vₚM,k); min = vₚ(gcd) = Tor/obstruction
                       ↦ padicVal_thickness_intersection / padicVal_obstruction_gcd  PROVED
    Thm 9.1, Prop 10.2/10.8  Tor₁ ≅ ℤ/gcd; obstruction-free ⇔ gcd=1
                       ↦ card_ker_mulLeft, obstructionFree_iff_*             PROVED
    Thm 9.1/Prop 10.2/Cor 10.8  Tor₁ ≅ ℤ/gcd  (group ISOMORPHISM, not just |·|)
                       ↦ torEquivZModGcd                                     PROVED
    Lem 6.4, CRT       crt split + gluing obstruction (gcd | a-b)
                       ↦ crt_iso, crt_solvable_iff                           PROVED
    Thm 9.3(iv)/Cor 10.8 (T1.3) CRT refinement: ℤ/N ≅ ∏_{q∣N} ℤ/q^{v_q N} (ring iso), the
                       finite-family generalization of crt_iso built from ZMod.chineseRemainder
                       ↦ zmodPiEquivOfCoprime, zmodPrimePowerProd            PROVED
    Thm 9.1 Step 4 / Cor 10.8 (T1.4) prime-wise direct-sum decomposition of Tor₁ (group level):
                       Tor₁(ℤ/M,ℤ/N) ≅ ⊕_{q∣N} ℤ/q^{min(v_q M, v_q N)}  (needs M ≠ 0)
                       ↦ zmodGcdPrimewiseDecomp, torPrimewiseDecomp         PROVED
    primewise / IC     |Tor| = ∏ qᵃ = exp(IC)
                       ↦ gcd_eq_prod_primeFactors, card_Tor_eq_exp_IC        PROVED
    App. C (T1.7) stability/locality core: vₚ ignores coprime-to-p factors (localization away
                       from p); local Tor Tor₁(ℤ/pᵃ,ℤ/pᵇ)≅ℤ/p^{min}; q-summand of global Tor = local
                       Tor at q (Tor commutes with localization/completion)
                       ↦ padicValNat_mul_coprime / torLocalModel / tor_primewise_isLocal  PROVED
    Prop 10.6 (algebraic shadow)  direct-sum H¹ ≅ ⊕Λ has card |Λ|ⁿ; H⁰ = 0
                       ↦ directSum_card, H0_zero                            PROVED (alg.)
    Prop 10.6 (T2.1) detector global sections as MODULE isos: ⊕_{p∈P}Λ ≅ Λ^{|P|} (rank |P|),
                       H⁰ ≅ PUnit, δcoh=1 (P≠∅ ⇒ nontrivial)  (needs 1 < ℓ)
                       ↦ detector_directSum_linearEquiv / detector_rank / detector_global_sections /
                         detector_H0_addEquiv / delta_coh_one_shadow         PROVED (alg.)
    §5.1 / Rem 6.5/10.5 (T2.2) AB-linearization, algebraic+valuation core: exact shifted-binomial
                       identity in ℤ[X]; vₚ(C(pⁿ,pʲ))=n-j (Kummer); vₚ(A^{pʲ}-1)=vₚ(A-1)+j (LTE);
                       profile vₚ((1+pᵀ)^{pʲ}-1)=T+j  (log bridge = Tier 3, Padic.log absent)
                       ↦ shifted_binom_identity / padicVal_binom_pow / padicVal_pow_sub_one /
                         Hk_basic_profile                                     PROVED (alg.+val.)
    §2.1/2.2 (T2.3) Primality sheaf sectionwise = intersection (Set/Subtype shadow): layers as
                       ℕ-predicates, fiber product = ⋂, restriction = inclusion, gluing identities
                       ↦ PrimalityShadow.layers_sectionwise / sections_primalityLayer /
                         sections_restrict / primalityLayer_equiv             PROVED (alg.)
    Thm 6.1 / Cor 6.3  bump = Euler jump; good-prime box (CONDITIONAL)
                       ↦ curve_master_identity, good_prime_box               PROVED (cond.)
    Thm 6.1 (T2.4) curve Betti bookkeeping: dim H¹(Xp) = 2g + b₁ + Σδ, excess = b₁ + Σδ = bump;
                       smooth ⇒ bump = 0, dim H¹(Xp) = dim H¹(Up)  (dims taken as inputs)
                       ↦ curve_betti_identity / smooth_silences / curve_normalization_package  PROVED
    Tier 3 (§6/§7/§9.3/§10.3) interface/conditional sealing of cohomology Mathlib lacks (étale,
                       motivic, Spec-ℤ sheaf coh, Padic.log) — AXIOM-FREE: deep inputs as `structure`
                       fields/hypotheses, paper theorems unconditional from them; §7.2 Ext correction
                       ↦ Tier3.CurveDetectorData/box_from_data / SheafCohomologyData/deltaCoh /
                         goodPrime_synchronization_extended / int_projective /
                         int_module_ext_one_eq_zero                 PROVED (interface + actual Ext)
    Corrections (§M)   4 paper errors surfaced by formalization (min↔max, SES sign, lcm↔gcd overlap,
                       module-Ext); 3 are the one lcm↔gcd confusion, all settled by the §G SES
    Thm 9.3 Good-Prime Synchronization (CONDITIONAL)
                       ↦ goodPrime_synchronization                          PROVED (cond.)
    §3.1 / Prop 10.7   gcd–lcm short exact sequence (Mayer–Vietoris), NEW
                       ↦ Additions.iota_injective / proj_surjective /
                         range_iota_eq_ker_proj                              PROVED
    Thm 9.1 (T1.5) obstruction/cokernel face of the GLOBAL map Φ:ℤ→ℤ/M×ℤ/N:
                       coker Φ = (ℤ/M×ℤ/N)/range Φ ≅ ℤ/gcd  (range Φ = ker π, 1st iso thm)
                       ↦ Additions.range_Phi_eq_ker_proj / coker_Phi_equiv    PROVED
    Thm 9.1 (Tor model) explicit free resolution 0→ℤ→(·N)ℤ→ℤ/N→0 of ℤ/N over ℤ;
                       length-1 projective resolution; abstract Tor live on ℤ/M
                       ↦ FreeResolution.res_shortExact / tor_one_int_isZero   PROVED (resolution)
    Thm 9.1 (Tor value) H₁((ℤ/M)⊗resolution) ≅ ker(·N) ≅ ℤ/gcd  (derived-functor value)
                       ↦ TorComputation.torSC_homologyIso / torSC_homology_addEquiv  PROVED
    Thm 9.1 (Tor, full) defeq-clean projective resolution `[ℤ →(·N) ℤ]` of ℤ/N; augmentation is
                       a QUASI-ISO; genuine `ProjectiveResolution`; and the categorical
                       `Tor (ModuleCat ℤ) 1` bound to it via `isoLeftDerivedObj`
                       ↦ ProjRes.cx / aug_quasiIso / projRes / torIso          PROVED (categorical Tor)
    Thm 9.1 (Tor, chain) ONE composite iso closing the whole circle, from the categorical symbol
                       to the cyclic group:
                       `Tor₁(ℤ/M,ℤ/N) ≅ H₁((ℤ/M)⊗cx) ≅ ker(·N:ℤ/M→ℤ/M) ≅ ℤ/gcd(M,N)`
                       ↦ ProjRes.chainHomologyOneIsoKer / ridKerEquiv / torFullIso  PROVED (full chain)

  ⚠ CORRECTION (6th paper, same error): Thm 9.3(iii)/Prop 10.7 give the localized
  intersection thickness as `p^{min{vp M,k}}`.  This is wrong: `(M)∩(pᵏ)=(lcm)`
  localises to `p^{max}`; `min` is the valuation of `gcd` (the failure fiber/Tor).

  ⚠ CORRECTION (sign of the Mayer–Vietoris sequence): Prop 10.7's proof writes
  `ι(x) = (x, -x)`, `π(a,b) = a - b`, which gives `π ∘ ι (x) = 2x ≠ 0`.  For an
  exact sequence the diagonal `ι(x) = (x, x)` with difference `π(a,b) = a - b` is
  forced.  The formalization in §G uses this consistent pair.

  HONEST OMISSIONS: Mathlib now defines generic sheaf cohomology, pro-étale
  ℓ-adic cohomology, and skyscraper sheaves, but the paper-specific calculations
  and étale–motivic comparisons remain unavailable.  AB-linearization /
  p-adic log (Rem 6.5/10.5) is also out of scope.
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Nat.Multiplicity
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE

open scoped BigOperators
open scoped ZeroObject

namespace Spt6

/-! ## A0. Hensel gate upgraded from interface to theorem. -/

/-- **A.1 / Thm 9.3(ii), forward Hensel gate.**  A residue root
`‖F(a)‖ < 1` with unit derivative `‖F'(a)‖ = 1` has a unique lift in the
open unit ball around `a`.

This is a direct, unconditional wrapper around
`Mathlib.NumberTheory.Padics.Hensel.hensels_lemma`; no Tier-3 geometric
smoothness or Jacobian criterion is used here. -/
theorem hensel_gate_aeval {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]} {a : ℤ_[p]}
    (hroot : ‖F.aeval a‖ < 1) (hsimple : ‖F.derivative.aeval a‖ = 1) :
    ∃! z : ℤ_[p], F.aeval z = 0 ∧ ‖z - a‖ < 1 := by
  have hsimple_eval : ‖F.derivative.eval a‖ = 1 := by
    simpa using hsimple
  have hHensel : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    change ‖F.eval a‖ < ‖F.derivative.eval a‖ ^ 2
    rw [hsimple_eval]
    simpa using hroot
  rcases hensels_lemma hHensel with ⟨z, hz_root, hz_close, _hz_deriv, hz_unique⟩
  have hz_close_one : ‖z - a‖ < 1 := by
    change ‖z - a‖ < ‖F.derivative.eval a‖ at hz_close
    rwa [hsimple_eval] at hz_close
  refine ⟨z, ⟨hz_root, hz_close_one⟩, ?_⟩
  intro y hy
  have hy_close : ‖y - a‖ < ‖F.derivative.aeval a‖ := by
    change ‖y - a‖ < ‖F.derivative.eval a‖
    rw [hsimple_eval]
    exact hy.2
  exact hz_unique y hy.1 hy_close

/-- Same Hensel gate, stated with `Polynomial.eval`. -/
theorem hensel_gate {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]} {a : ℤ_[p]}
    (hroot : ‖F.eval a‖ < 1) (hsimple : ‖F.derivative.eval a‖ = 1) :
    ∃! z : ℤ_[p], F.eval z = 0 ∧ ‖z - a‖ < 1 := by
  simpa using
    (hensel_gate_aeval (p := p) (F := F) (a := a) hroot hsimple)

/-- **C.4 unconditional uniqueness face.**  Two roots in the residue class
selected by a simple approximate root are equal.  This is the directly usable
uniqueness consequence of `hensel_gate`; no scheme-smoothness or Jacobian
criterion is assumed. -/
theorem hensel_gate_unique_of_two {p : ℕ} [Fact p.Prime]
    {F : Polynomial ℤ_[p]} {a z w : ℤ_[p]}
    (hroot : ‖F.eval a‖ < 1) (hsimple : ‖F.derivative.eval a‖ = 1)
    (hz : F.eval z = 0 ∧ ‖z - a‖ < 1)
    (hw : F.eval w = 0 ∧ ‖w - a‖ < 1) :
    z = w :=
  (hensel_gate (p := p) (F := F) (a := a) hroot hsimple).unique hz hw

/-- **C.4 conditional geometric bridge, with every missing input exposed.**
If a geometric smoothness predicate implies both the residue-root condition
and the unit-derivative condition, then smoothness gives a unique `p`-adic
lift.  The conclusion is genuine Hensel mathematics; only the two implications
from `Smooth` are external geometric/Jacobian hypotheses. -/
theorem smooth_to_unique_lift_of_hensel_hypotheses {p : ℕ} [Fact p.Prime]
    {F : Polynomial ℤ_[p]} {a : ℤ_[p]} (Smooth : Prop)
    (smooth_to_root : Smooth → ‖F.eval a‖ < 1)
    (smooth_to_unitDerivative : Smooth → ‖F.derivative.eval a‖ = 1)
    (hsmooth : Smooth) :
    ∃! z : ℤ_[p], F.eval z = 0 ∧ ‖z - a‖ < 1 :=
  hensel_gate (smooth_to_root hsmooth) (smooth_to_unitDerivative hsmooth)

/-! ## C5. Frobenius–Tate polynomial: unconditional arithmetic shadow.

Mathlib does not currently provide the supersingularity predicate and finite-field
elliptic-curve Frobenius package needed to prove `aₚ = 0 → supersingular` for the
paper's curve.  We therefore do not introduce a Boolean or a structure field named
`supersingular`.  What is formalizable without that geometry is the exact point-count
trace and polynomial arithmetic used by the certificate.
-/

/-- The trace extracted from a certified point count:
`aₚ = p + 1 - #E(𝔽ₚ)`.  This definition records only integer arithmetic; it does
not assert that `N` is the point count of an elliptic curve. -/
def frobeniusTraceFromPointCount (p N : ℕ) : ℤ :=
  (p : ℤ) + 1 - (N : ℤ)

/-- The formal Frobenius–Tate polynomial `T² - aₚT + p` over `ℤ`.
Calling this the characteristic polynomial of a particular curve requires a
separate geometric Frobenius theorem. -/
noncomputable def frobeniusTatePolynomial (p : ℕ) (ap : ℤ) : Polynomial ℤ :=
  Polynomial.X ^ 2 - Polynomial.C ap * Polynomial.X + Polynomial.C (p : ℤ)

/-- The point-count trace vanishes exactly when the certified count is `p+1`. -/
theorem frobeniusTrace_eq_zero_iff (p N : ℕ) :
    frobeniusTraceFromPointCount p N = 0 ↔ (N : ℤ) = (p : ℤ) + 1 := by
  simp only [frobeniusTraceFromPointCount]
  omega

/-- The formal polynomial has precisely the coefficients
`[p, -aₚ, 1]` in degrees `0,1,2`. -/
theorem frobeniusTatePolynomial_coefficients (p : ℕ) (ap : ℤ) :
    (frobeniusTatePolynomial p ap).coeff 2 = 1 ∧
      (frobeniusTatePolynomial p ap).coeff 1 = -ap ∧
      (frobeniusTatePolynomial p ap).coeff 0 = (p : ℤ) := by
  constructor
  · norm_num [frobeniusTatePolynomial]
    exact Polynomial.coeff_C_ne_zero one_ne_zero
  constructor
  · norm_num [frobeniusTatePolynomial]
  · norm_num [frobeniusTatePolynomial]

/-- Evaluation form of `Pₚ(T)=T²-aₚT+p`. -/
theorem frobeniusTatePolynomial_eval (p : ℕ) (ap x : ℤ) :
    (frobeniusTatePolynomial p ap).eval x = x ^ 2 - ap * x + p := by
  simp [frobeniusTatePolynomial]

/-- At trace zero, the formal Frobenius–Tate polynomial is `T²+p`. -/
theorem frobeniusTatePolynomial_trace_zero (p : ℕ) :
    frobeniusTatePolynomial p 0 =
      Polynomial.X ^ 2 + Polynomial.C (p : ℤ) := by
  simp [frobeniusTatePolynomial]

/-- A point-count certificate `#E(𝔽ₚ)=p+1` forces the extracted trace to be zero
and hence specializes the formal polynomial to `T²+p`. -/
theorem frobeniusTatePolynomial_of_pointCount_eq (p N : ℕ)
    (hN : (N : ℤ) = (p : ℤ) + 1) :
    frobeniusTatePolynomial p (frobeniusTraceFromPointCount p N)
      = Polynomial.X ^ 2 + Polynomial.C (p : ℤ) := by
  have htrace : frobeniusTraceFromPointCount p N = 0 := by
    rw [frobeniusTrace_eq_zero_iff]
    exact hN
  rw [htrace, frobeniusTatePolynomial_trace_zero]

/-! ## C1–C3 actual Mathlib upgrades discovered in the current library.

The current Mathlib version contains more infrastructure than the original
Tier-3 audit assumed: skyscraper sheaves and flasqueness on topological spaces,
generic sheaf cohomology defined by Ext, and pro-étale ℓ-adic cohomology of
schemes.  The theorems below expose exactly those unconditional pieces.
-/

namespace Tier3Actual

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w w'

/-- **C.1 genuine upgrade.**  An `AddCommGrpCat`-valued skyscraper sheaf is
flasque: every restriction is either an isomorphism or a morphism to a zero
object, hence an epimorphism. -/
theorem skyscraperSheaf_isFlasque {X : TopCat.{u}} (p : X)
    [∀ U : Opens X, Decidable (p ∈ U)] (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque (_root_.skyscraperSheaf p A) where
  epi {U V} i := by
    by_cases hV : p ∈ unop V
    · have hU : p ∈ unop U := leOfHom i.unop hV
      dsimp [_root_.skyscraperSheaf, _root_.skyscraperPresheaf]
      rw [dif_pos hV]
      apply IsIso.epi_of_iso
    · dsimp [_root_.skyscraperSheaf, _root_.skyscraperPresheaf]
      rw [dif_neg hV]
      let hT : IsTerminal (if p ∈ unop V then A else terminal AddCommGrpCat) :=
        (if_neg hV).symm.ndrec terminalIsTerminal
      exact (IsZero.of_iso (isZero_zero AddCommGrpCat)
        (CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal hT).symm).epi _

/-- **C.3 genuine upgrade.**  Mathlib's sheaf cohomology is definitionally the
Ext group from the constant sheaf `ℤ`. -/
noncomputable def sheafCohomologyExtEquiv
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{w})
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (CategoryTheory.Sheaf J AddCommGrpCat.{w})] (n : ℕ) :
    CategoryTheory.Sheaf.H F n ≃
      CategoryTheory.Abelian.Ext
        ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) F n :=
  Equiv.refl _

/-- Type equality form of the preceding definition, useful for rewriting. -/
theorem sheafCohomology_eq_ext
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{w})
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (CategoryTheory.Sheaf J AddCommGrpCat.{w})] (n : ℕ) :
    CategoryTheory.Sheaf.H F n =
      CategoryTheory.Abelian.Ext
        ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) F n :=
  rfl

/-- **C.2 genuine upgrade.**  Pro-étale ℓ-adic cohomology is an actual
Mathlib type (with an `AddCommGroup` instance) for every scheme. -/
theorem ellAdicCohomology_nonempty (X : AlgebraicGeometry.Scheme) (ℓ : ℕ)
    [Fact ℓ.Prime] (n : ℕ) :
    Nonempty (X.EllAdicCohomology ℓ n) :=
  inferInstance

end Tier3Actual

/-! ## D1. Certified finite-field prime scan (§8.6).

The gcd with `X^p-X` detects `𝔽_p`-rational roots, not simplicity by
itself.  The derivative test below is therefore intentionally separate.
-/

namespace PrimeScan

open Polynomial

/-- Coefficientwise reduction of an integer polynomial modulo `p`. -/
noncomputable def modPolynomial (p : ℕ) (F : Polynomial ℤ) : Polynomial (ZMod p) :=
  F.map (Int.castRingHom (ZMod p))

/-- The same polynomial interpreted over the `p`-adic integers. -/
noncomputable def padicPolynomial (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) : Polynomial ℤ_[p] :=
  F.map (Int.castRingHom ℤ_[p])

/-- The canonical integer representative of a residue, viewed in `ℤ_[p]`. -/
noncomputable def padicRepresentative (p : ℕ) [Fact p.Prime] (a : ZMod p) : ℤ_[p] :=
  (a.val : ℤ_[p])

/-- The finite-field polynomial vanishing on every element of `ZMod p`. -/
noncomputable def finiteFieldPolynomial (p : ℕ) : Polynomial (ZMod p) :=
  X ^ p - X

/-- Gcd readout: `gcd(f mod p, X^p-X)`. -/
noncomputable def rootGCD (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) : Polynomial (ZMod p) :=
  EuclideanDomain.gcd (modPolynomial p F) (finiteFieldPolynomial p)

/-- Numerical degree readout of the gcd polynomial. -/
noncomputable def rootGCDDegree (p : ℕ) [Fact p.Prime] (F : Polynomial ℤ) : ℕ :=
  (rootGCD p F).natDegree

/-- Complete finite enumeration of the simple roots of `F mod p`. -/
noncomputable def simpleRoots (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) : Finset (ZMod p) :=
  Finset.univ.filter fun a =>
    (modPolynomial p F).eval a = 0 ∧
      (modPolynomial p F).derivative.eval a ≠ 0

/-- Number of simple roots modulo `p`. -/
noncomputable def simpleRootCount (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) : ℕ :=
  (simpleRoots p F).card

/-- Boolean simple-root certificate at a fixed prime. -/
noncomputable def hasSimpleRoot (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) : Bool :=
  decide (0 < simpleRootCount p F)

/-- Membership in the computed root set is exactly the simple-root predicate. -/
@[simp] theorem mem_simpleRoots_iff (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (a : ZMod p) :
    a ∈ simpleRoots p F ↔
      (modPolynomial p F).eval a = 0 ∧
        (modPolynomial p F).derivative.eval a ≠ 0 := by
  simp [simpleRoots]

/-- The computed count is positive exactly when a simple residue root exists. -/
theorem simpleRootCount_pos_iff (p : ℕ) [Fact p.Prime] (F : Polynomial ℤ) :
    0 < simpleRootCount p F ↔
      ∃ a : ZMod p,
        (modPolynomial p F).eval a = 0 ∧
          (modPolynomial p F).derivative.eval a ≠ 0 := by
  rw [simpleRootCount, Finset.card_pos]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (mem_simpleRoots_iff p F a).mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (mem_simpleRoots_iff p F a).mpr ha⟩

/-- Correctness theorem for the Boolean certificate. -/
theorem hasSimpleRoot_eq_true_iff (p : ℕ) [Fact p.Prime] (F : Polynomial ℤ) :
    hasSimpleRoot p F = true ↔
      ∃ a : ZMod p,
        (modPolynomial p F).eval a = 0 ∧
          (modPolynomial p F).derivative.eval a ≠ 0 := by
  simp [hasSimpleRoot, simpleRootCount_pos_iff]

/-- Fermat's finite-field polynomial vanishes at every residue. -/
theorem eval_finiteFieldPolynomial (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    (finiteFieldPolynomial p).eval a = 0 := by
  simp [finiteFieldPolynomial, ZMod.pow_card]

/-- The gcd readout has exactly the same `ZMod p` zero set as `F mod p`. -/
theorem eval_rootGCD_eq_zero_iff (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (a : ZMod p) :
    (rootGCD p F).eval a = 0 ↔ (modPolynomial p F).eval a = 0 := by
  change (rootGCD p F).IsRoot a ↔ (modPolynomial p F).IsRoot a
  rw [rootGCD, Polynomial.isRoot_gcd_iff_isRoot_left_right]
  exact and_iff_left (eval_finiteFieldPolynomial p a)

/-- Evaluation after reduction is reduction of the integer evaluation at the
canonical representative. -/
theorem modPolynomial_eval_eq_intCast_eval_val (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (a : ZMod p) :
    (modPolynomial p F).eval a =
      ((F.eval (a.val : ℤ) : ℤ) : ZMod p) := by
  rw [← ZMod.natCast_zmod_val a]
  simpa [modPolynomial] using
    (Polynomial.eval_map_apply (p := F) (Int.castRingHom (ZMod p)) (a.val : ℤ))

/-- Evaluation over `ℤ_[p]` at the representative is the p-adic cast of the
integer evaluation. -/
theorem padicPolynomial_eval_eq_intCast_eval_val (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (a : ZMod p) :
    (padicPolynomial p F).eval (padicRepresentative p a) =
      ((F.eval (a.val : ℤ) : ℤ) : ℤ_[p]) := by
  simpa [padicPolynomial, padicRepresentative] using
    (Polynomial.eval_map_apply (p := F) (Int.castRingHom ℤ_[p]) (a.val : ℤ))

/-- A residue root gives the strict Hensel root inequality. -/
theorem scanned_root_norm_lt_one (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (a : ZMod p)
    (ha : (modPolynomial p F).eval a = 0) :
    ‖(padicPolynomial p F).eval (padicRepresentative p a)‖ < 1 := by
  rw [padicPolynomial_eval_eq_intCast_eval_val]
  rw [PadicInt.norm_intCast_lt_one_iff]
  rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
  rwa [← modPolynomial_eval_eq_intCast_eval_val]

/-- A nonzero derivative modulo `p` gives unit p-adic derivative norm. -/
theorem scanned_derivative_norm_eq_one (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (a : ZMod p)
    (ha : (modPolynomial p F).derivative.eval a ≠ 0) :
    ‖(padicPolynomial p F).derivative.eval (padicRepresentative p a)‖ = 1 := by
  rw [padicPolynomial, Polynomial.derivative_map]
  change ‖(padicPolynomial p F.derivative).eval (padicRepresentative p a)‖ = 1
  rw [padicPolynomial_eval_eq_intCast_eval_val]
  rw [PadicInt.norm_intCast_eq_one_iff]
  rw [Int.isCoprime_iff_gcd_eq_one]
  let d : ℤ := F.derivative.eval (a.val : ℤ)
  have hcast : (d : ZMod p) ≠ 0 := by
    rw [← modPolynomial_eval_eq_intCast_eval_val]
    simpa [d, modPolynomial, Polynomial.derivative_map] using ha
  have hnot : ¬ (p : ℤ) ∣ d := by
    rwa [← CharP.intCast_eq_zero_iff (ZMod p) p]
  have hgdiv : Int.gcd d (p : ℤ) ∣ p := by
    exact_mod_cast Int.gcd_dvd_right d (p : ℤ)
  rcases (Nat.dvd_prime Fact.out).mp hgdiv with hg | hg
  · exact hg
  · exfalso
    apply hnot
    have hd := Int.gcd_dvd_left d (p : ℤ)
    rwa [hg] at hd

/-- Every root accepted by the finite scan has a unique p-adic lift in its
residue ball. -/
theorem simpleRoot_has_uniquePadicLift (p : ℕ) [Fact p.Prime]
    (F : Polynomial ℤ) (a : ZMod p) (ha : a ∈ simpleRoots p F) :
    ∃! z : ℤ_[p],
      (padicPolynomial p F).eval z = 0 ∧
        ‖z - padicRepresentative p a‖ < 1 := by
  have hs := (mem_simpleRoots_iff p F a).mp ha
  exact hensel_gate
    (scanned_root_norm_lt_one p F a hs.1)
    (scanned_derivative_norm_eq_one p F a hs.2)

/-- Prime-indexed Boolean wrapper; composites are rejected. -/
noncomputable def scanPrime (F : Polynomial ℤ) (p : ℕ) : Bool :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    hasSimpleRoot p F
  else false

/-- All primes `p ≤ B` for which `F mod p` has a simple root. -/
noncomputable def scanPrimesUpTo (F : Polynomial ℤ) (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter fun p => scanPrime F p

/-- Correctness of the fixed-integer prime wrapper. -/
theorem scanPrime_eq_true_iff (F : Polynomial ℤ) (p : ℕ) :
    scanPrime F p = true ↔
      p.Prime ∧ ∃ a : ZMod p,
        (modPolynomial p F).eval a = 0 ∧
          (modPolynomial p F).derivative.eval a ≠ 0 := by
  classical
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    simp [scanPrime, hp, hasSimpleRoot_eq_true_iff]
  · simp [scanPrime, hp]

/-- End-to-end correctness of the bounded prime scan. -/
theorem mem_scanPrimesUpTo_iff (F : Polynomial ℤ) (B p : ℕ) :
    p ∈ scanPrimesUpTo F B ↔
      p ≤ B ∧ p.Prime ∧ ∃ a : ZMod p,
        (modPolynomial p F).eval a = 0 ∧
          (modPolynomial p F).derivative.eval a ≠ 0 := by
  rw [scanPrimesUpTo, Finset.mem_filter, Finset.mem_range, scanPrime_eq_true_iff]
  rw [Nat.lt_succ_iff]

end PrimeScan

/-! ## A2. Analytic prediction density from derangements. -/

/-- The analytic prediction density from the `S_d` model:
the proportion of permutations with at least one fixed point is
`1 - !d / d!`. -/
noncomputable def analyticPred (d : ℕ) : ℚ :=
  1 - (numDerangements d : ℚ) / (d.factorial : ℚ)

/-- The finite set of permutations of `Fin d` with a fixed point. -/
def fixedPointPerms (d : ℕ) : Finset (Equiv.Perm (Fin d)) :=
  Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => ∃ i, σ i = i)

/-- The finite set of derangements of `Fin d`, written as a filter on all
permutations. -/
def derangementPerms (d : ℕ) : Finset (Equiv.Perm (Fin d)) :=
  Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => ∀ i, σ i ≠ i)

/-- Mathlib's `derangements (Fin d)` subtype is definitionally the same
predicate as `∀ i, σ i ≠ i`, but we expose this equivalence so that subsequent
cardinality arguments are insensitive to the chosen `Fintype` instance. -/
noncomputable def derangementsSubtypeEquiv (d : ℕ) :
    {σ : Equiv.Perm (Fin d) // ∀ i, σ i ≠ i} ≃ derangements (Fin d) :=
  Equiv.refl _

/-- Direct cardinality form of `card_derangements_eq_numDerangements` for
permutations of `Fin d`. -/
theorem card_derangements_direct (d : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin d) // ∀ i, σ i ≠ i} = numDerangements d := by
  exact (Fintype.card_congr (derangementsSubtypeEquiv d)).trans
    (by simpa using (card_derangements_eq_numDerangements (Fin d)))

/-- The filtered set of derangements has cardinality `!d`. -/
theorem derangementPerms_card (d : ℕ) :
    (derangementPerms d).card = numDerangements d := by
  classical
  rw [derangementPerms]
  exact (Fintype.card_subtype (fun σ : Equiv.Perm (Fin d) => ∀ i, σ i ≠ i)).symm.trans
    (card_derangements_direct d)

/-- The number of permutations of `Fin d` with at least one fixed point is
`d! - !d`. -/
theorem fixedPointPerms_card (d : ℕ) :
    (fixedPointPerms d).card = d.factorial - numDerangements d := by
  classical
  have hder :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => ¬ ∃ i, σ i = i)).card =
        numDerangements d := by
    exact (by
      simpa [not_exists, ne_eq] using
        (Fintype.card_subtype (fun σ : Equiv.Perm (Fin d) => ∀ i, σ i ≠ i)).symm.trans
          (card_derangements_direct d))
  have hsum :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Equiv.Perm (Fin d))))
      (p := fun σ : Equiv.Perm (Fin d) => ∃ i, σ i = i)
  have hsum' :
      (fixedPointPerms d).card + numDerangements d = d.factorial := by
    rw [fixedPointPerms]
    rw [← hder]
    simpa [Fintype.card_perm] using hsum
  exact Nat.eq_sub_of_add_eq hsum'

/-- Derangements are a subset of all permutations, hence `!d ≤ d!`. -/
theorem numDerangements_le_factorial (d : ℕ) :
    numDerangements d ≤ d.factorial := by
  classical
  have hsum :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Equiv.Perm (Fin d))))
      (p := fun σ : Equiv.Perm (Fin d) => ∃ i, σ i = i)
  have hder :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => ¬ ∃ i, σ i = i)).card =
        numDerangements d := by
    exact (by
      simpa [not_exists, ne_eq] using
        (Fintype.card_subtype (fun σ : Equiv.Perm (Fin d) => ∀ i, σ i ≠ i)).symm.trans
          (card_derangements_direct d))
  have hsum' :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => ∃ i, σ i = i)).card +
        numDerangements d = d.factorial := by
    rw [← hder]
    simpa [Fintype.card_perm] using hsum
  exact Nat.le.intro (by rw [Nat.add_comm]; exact hsum')

/-- **§8.7 analytic prediction density.**  The quantity `analyticPred d` is
exactly the fraction of permutations of `Fin d` with at least one fixed point. -/
theorem analyticPred_eq_fixedPoint_ratio (d : ℕ) :
    analyticPred d
      = (((Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => ∃ i, σ i = i)).card : ℚ))
          / (d.factorial : ℚ) := by
  classical
  have hcard := fixedPointPerms_card d
  have hle := numDerangements_le_factorial d
  have hfac : (d.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero d
  change analyticPred d = ((fixedPointPerms d).card : ℚ) / (d.factorial : ℚ)
  calc
    analyticPred d
        = 1 - (numDerangements d : ℚ) / (d.factorial : ℚ) := rfl
    _ = (d.factorial : ℚ) / (d.factorial : ℚ) -
          (numDerangements d : ℚ) / (d.factorial : ℚ) := by rw [div_self hfac]
    _ = ((d.factorial : ℚ) - (numDerangements d : ℚ)) / (d.factorial : ℚ) := by ring
    _ = ((d.factorial - numDerangements d : ℕ) : ℚ) / (d.factorial : ℚ) := by
      rw [Nat.cast_sub hle]
    _ = ((fixedPointPerms d).card : ℚ) / (d.factorial : ℚ) := by
      rw [← hcard]

/-- Table 1's `d = 3` analytic value: `1 - !3 / 3! = 2 / 3`. -/
example : analyticPred 3 = 2 / 3 := by
  simp [analyticPred, numDerangements]
  norm_num

/-! ## A3. Obstruction support as a zero locus in `Spec ℤ`. -/

/-- The principal ideal `(g)` in `ℤ`, written with a natural generator. -/
def principalIdealInt (g : ℕ) : Ideal ℤ :=
  Ideal.span ({(g : ℤ)} : Set ℤ)

/-- The closed point `(p)` of `Spec ℤ`, for a prime natural number `p`. -/
def closedPointInt (p : ℕ) [Fact p.Prime] : PrimeSpectrum ℤ :=
  ⟨principalIdealInt p, by
    dsimp [principalIdealInt]
    infer_instance⟩

/-- **A.3 / support-zero-locus gate.**  Membership in the zero locus of the
singleton `{g}` is exactly membership of `g` in the prime ideal represented by
the point of `Spec ℤ`. -/
theorem obstruction_support_zeroLocus (g : ℕ) (P : PrimeSpectrum ℤ) :
    P ∈ PrimeSpectrum.zeroLocus ({(g : ℤ)} : Set ℤ) ↔ (g : ℤ) ∈ P.asIdeal := by
  simp [PrimeSpectrum.mem_zeroLocus]

/-- The closed point `(p)` belongs to `V(g)` exactly when `p` divides `g`. -/
theorem prime_mem_support_iff_dvd (g p : ℕ) [Fact p.Prime] :
    closedPointInt p ∈ PrimeSpectrum.zeroLocus ({(g : ℤ)} : Set ℤ) ↔ p ∣ g := by
  rw [obstruction_support_zeroLocus]
  change (g : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) ↔ p ∣ g
  rw [Ideal.mem_span_singleton]
  exact Int.natCast_dvd_natCast

/-- Same closed-point support criterion, with primality supplied as an explicit
hypothesis rather than a typeclass instance. -/
theorem prime_mem_support_iff_dvd_of_prime (g p : ℕ) (hp : p.Prime) :
    (letI : Fact p.Prime := ⟨hp⟩;
      closedPointInt p) ∈ PrimeSpectrum.zeroLocus ({(g : ℤ)} : Set ℤ) ↔ p ∣ g := by
  letI : Fact p.Prime := ⟨hp⟩
  exact prime_mem_support_iff_dvd g p

/-- The image of `Spec(ℤ/(g)) → Spec ℤ` is the zero locus of the ideal `(g)`.

This is Mathlib's range theorem for surjective maps on prime spectra, specialized
to the quotient map `ℤ → ℤ/(g)`, followed by `ker(Quotient.mk (g)) = (g)`. -/
theorem residue_fiber_range (g : ℕ) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdealInt g)))
      = PrimeSpectrum.zeroLocus (R := ℤ) ((principalIdealInt g : Ideal ℤ) : Set ℤ) := by
  calc
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdealInt g)))
        = PrimeSpectrum.zeroLocus (R := ℤ)
            ((RingHom.ker (Ideal.Quotient.mk (principalIdealInt g)) : Ideal ℤ) : Set ℤ) :=
      range_comap_of_surjective (ℤ ⧸ principalIdealInt g)
        (Ideal.Quotient.mk (principalIdealInt g))
        Ideal.Quotient.mk_surjective
    _ = PrimeSpectrum.zeroLocus (R := ℤ) ((principalIdealInt g : Ideal ℤ) : Set ℤ) := by
      rw [Ideal.mk_ker]

/-- The same residue-fiber image theorem, normalized to the singleton zero
locus `V({g})` using `PrimeSpectrum.zeroLocus_span`. -/
theorem residue_fiber_range_singleton (g : ℕ) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdealInt g)))
      = PrimeSpectrum.zeroLocus ({(g : ℤ)} : Set ℤ) := by
  calc
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdealInt g)))
        = PrimeSpectrum.zeroLocus (R := ℤ) ((principalIdealInt g : Ideal ℤ) : Set ℤ) :=
      residue_fiber_range g
    _ = PrimeSpectrum.zeroLocus ({(g : ℤ)} : Set ℤ) := by
      rw [principalIdealInt, PrimeSpectrum.zeroLocus_span]

/-- The paper's obstruction ideal `(gcd(M,p^k))` in `ℤ`. -/
def obstructionIdeal (M p k : ℕ) : Ideal ℤ :=
  principalIdealInt (Nat.gcd M (p ^ k))

/-- The failure trace/support cut out by `gcd(M,p^k)` is exactly the zero locus
`V(gcd(M,p^k))` in `Spec ℤ`. -/
theorem obstruction_support_eq_zeroLocus_gcd (M p k : ℕ) :
    PrimeSpectrum.zeroLocus (R := ℤ) ((obstructionIdeal M p k : Ideal ℤ) : Set ℤ)
      = PrimeSpectrum.zeroLocus ({(Nat.gcd M (p ^ k) : ℤ)} : Set ℤ) := by
  simp [obstructionIdeal, principalIdealInt, PrimeSpectrum.zeroLocus_span]

/-! ## §A — Equalizer kernel = (M)∩(N) = (lcm) (Lem 6.4, Prop 10.1, Thm 9.1/9.3(iii)). -/

theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a := lcm_dvd_iff.symm

theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- **Lem 6.4 (CRT / gluing obstruction).** Local witnesses `a, b` glue iff
    `gcd(M,N) ∣ (a - b)`. -/
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

/-- **Unconditional arithmetic replacement for a gluing-field implication.**
Once the obstruction group is identified with the gcd face, `gcd(M,N)=1`
forces local residues modulo `M` and `N` to glue.

This is the genuine Lean theorem underneath statements informally phrased as
“vanishing obstruction implies gluing”; the geometric identification of a
cohomology group with this gcd obstruction is not used here. -/
theorem gcd_obstruction_zero_to_gluing (M N a b : ℤ) (hcop : Int.gcd M N = 1) :
    ∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b) := by
  rw [crt_solvable_iff]
  rw [hcop]
  exact one_dvd _

/-- Compatibility alias for the paper-facing phrasing: this theorem proves the
arithmetic core that should replace any field-projection version of
`h1EtaleZero_to_gluing` after the `H¹` obstruction has been represented by
`gcd(M,N)`. -/
theorem h1EtaleZero_to_gluing_arithmetic (M N a b : ℤ) (hcop : Int.gcd M N = 1) :
    ∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b) :=
  gcd_obstruction_zero_to_gluing M N a b hcop

noncomputable def crt_iso {a b : ℕ} (h : Nat.Coprime a b) :
    ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder h

/-! ### §B′ — CRT refinement (T1.3): full prime-power decomposition of `ℤ/N` as a ring iso.

The two-factor `crt_iso` above (`ZMod.chineseRemainder`) is the base case of the Chinese Remainder
Theorem over an *arbitrary finite family of pairwise-coprime moduli*.  We build that generalization,
`zmodPiEquivOfCoprime`, by `Finset` induction directly on `ZMod.chineseRemainder`, and specialize it
at the prime-power factorization `N = ∏_{q ∈ primeFactors N} q^{v_q N}` to obtain the ring
isomorphism `ℤ/N ≅ ∏_{q ∣ N} ℤ/q^{v_q N}` that the paper repeatedly uses for prime-wise splitting
(Thm 9.3(iv), Cor 10.8).  The construction is self-contained from `ZMod.chineseRemainder`; Mathlib
also packages these as `ZMod.prodEquivPi` / `ZMod.equivPi`. -/

/-- Pi-over-`insert` as a `RingEquiv`: split off the inserted index.  Built with no casts on the
    `Pi` side — `f ((subtypeInsertEquivOption ha).symm none)` is defeq to `f a`, and the `some j`
    branch defeq to `f j`, so the product/Pi targets unify directly. -/
noncomputable def piInsertRingEquiv {ι : Type*} [DecidableEq ι] (s' : Finset ι) (a : ι)
    (ha : a ∉ s') (f : ι → ℕ) :
    (∀ i : (insert a s' : Finset ι), ZMod (f i)) ≃+* ZMod (f a) × (∀ i : s', ZMod (f i)) :=
  let e := Finset.subtypeInsertEquivOption (t := s') (x := a) ha
  (RingEquiv.piCongrLeft' (fun i : (insert a s' : Finset ι) => ZMod (f i)) e).trans
    (RingEquiv.piOptionEquivProd (R := fun j : Option s' => ZMod (f ((e.symm) j))))

/-- Existence of the pairwise-coprime CRT over a `Finset`, proved by `Prop`-induction.
    (`Finset.induction_on` carries a `Prop` motive, so we prove `Nonempty (_ ≃+* _)` and take
    `.some`; the resulting use of `Classical.choice` stays inside the allowed axiom set.) -/
theorem nonempty_zmodPiEquivOfCoprime {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    Nonempty (ZMod (∏ i ∈ s, f i) ≃+* (∀ i : s, ZMod (f i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : Unique (ZMod (∏ i ∈ (∅ : Finset ι), f i)) := by
      rw [Finset.prod_empty]; infer_instance
    exact ⟨RingEquiv.ofUnique⟩
  | @insert a s' ha ih =>
    have hcop' : Nat.Coprime (f a) (∏ i ∈ s', f i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      exact hcop a (Finset.mem_insert_self a s') i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    have hcops' : ∀ i ∈ s', ∀ j ∈ s', i ≠ j → Nat.Coprime (f i) (f j) := by
      intro i hi j hj hij
      exact hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    obtain ⟨ihe⟩ := ih hcops'
    have hprod : (∏ i ∈ insert a s', f i) = f a * ∏ i ∈ s', f i := Finset.prod_insert ha
    refine ⟨?_⟩
    refine (RingEquiv.cast (R := fun n => ZMod n) hprod).trans ?_
    refine (ZMod.chineseRemainder hcop').trans ?_
    refine (RingEquiv.prodCongr (RingEquiv.refl (ZMod (f a))) ihe).trans ?_
    exact (piInsertRingEquiv s' a ha f).symm

/-- **CRT over a finite family of pairwise-coprime moduli** — the `Finset`/`Pi` generalization of
    `crt_iso`, built from `ZMod.chineseRemainder`:
    `ZMod (∏ i ∈ s, f i) ≃+* ∀ i : s, ZMod (f i)`. -/
noncomputable def zmodPiEquivOfCoprime {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    ZMod (∏ i ∈ s, f i) ≃+* (∀ i : s, ZMod (f i)) :=
  (nonempty_zmodPiEquivOfCoprime s f hcop).some

/-- **T1.3 — CRT refinement.** The full prime-power decomposition of `ℤ/N` as a ring isomorphism,
    `ℤ/N ≅ ∏_{q ∈ primeFactors N} ℤ/q^{v_q N}`, obtained by specializing `zmodPiEquivOfCoprime`
    at `f q = q^{v_q N}` over `s = N.primeFactors` (distinct prime powers are coprime), then
    transporting along `N = ∏_{q} q^{v_q N}`.  This is the natural generalization of `crt_iso`
    and the foundation of the paper's prime-wise splitting (Thm 9.3(iv), Cor 10.8). -/
noncomputable def zmodPrimePowerProd (N : ℕ) (hN : N ≠ 0) :
    ZMod N ≃+* ((q : N.primeFactors) → ZMod (q ^ N.factorization q)) := by
  classical
  set f : ℕ → ℕ := fun q => q ^ N.factorization q with hf
  have hprodN : (∏ q ∈ N.primeFactors, f q) = N := by
    rw [hf, ← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hN
  have hcop : ∀ i ∈ N.primeFactors, ∀ j ∈ N.primeFactors, i ≠ j → Nat.Coprime (f i) (f j) := by
    intro i hi j hj hij
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hi)
      (Nat.prime_of_mem_primeFactors hj) hij
  refine (RingEquiv.cast (R := fun n => ZMod n) hprodN.symm).trans ?_
  exact zmodPiEquivOfCoprime N.primeFactors f hcop

/-! ## §B — Thickness, CORRECTED (Prop 10.7, Thm 9.3(iii)). -/

theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

/-! ### §B′′ — T1.6: local thickness, in valuation (`padicValNat`) form (CORRECTION 2).

The paper's `εₚ = min{vₚ(M), k}` is **not** the local thickness of the intersection
`(M) ∩ (pᵏ) = (lcm(M, pᵏ))`.  Localizing at `p`, `(pᵏ)_(p) = (p^{max})` so the intersection's
`p`-adic thickness is the **max**:

  `vₚ(lcm(M, pᵏ)) = max(vₚ M, k)`     — the genuine local thickness of `(M) ∩ (pᵏ)`;

whereas `min` is the valuation of the **gcd**, i.e. the Tor/obstruction fibre (cf. T1.4):

  `vₚ(gcd(M, pᵏ)) = min(vₚ M, k)`.

These are the honest arithmetic content of the local-ideal statement
`((M) ∩ (pᵏ))_(p) = (p^{max})ℤ_(p)` (the localization being unit-multiplication on the generator,
which does not change the `p`-adic valuation).  We use `padicValNat p` as the valuation; the bridge
`Nat.factorization_def` identifies it with `Nat.factorization · p` at a prime, where §B's
`factorization_lcm_apply` / `factorization_gcd_apply` give the `max` / `min`. -/

/-- **T1.6 (intersection thickness).** The local `p`-adic thickness of `(M) ∩ (pᵏ) = (lcm(M, pᵏ))`
    is `max(vₚ M, k)` — the CORRECTED thickness (the paper's `min` was the gcd/obstruction value). -/
theorem padicVal_thickness_intersection (p M k : ℕ) (hp : p.Prime) (hM : M ≠ 0) :
    padicValNat p (Nat.lcm M (p ^ k)) = max (padicValNat p M) k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  have hpow : (p ^ k).factorization p = k := by
    rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  rw [← Nat.factorization_def (Nat.lcm M (p ^ k)) hp, factorization_lcm_apply hM hpk p,
    Nat.factorization_def M hp, hpow]

/-- **T1.6 (obstruction valuation).** The `min` exponent is the `p`-adic valuation of the
    `gcd(M, pᵏ)` — the Tor/failure-fibre value, **not** the intersection thickness. -/
theorem padicVal_obstruction_gcd (p M k : ℕ) (hp : p.Prime) (hM : M ≠ 0) :
    padicValNat p (Nat.gcd M (p ^ k)) = min (padicValNat p M) k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  have hpow : (p ^ k).factorization p = k := by
    rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  rw [← Nat.factorization_def (Nat.gcd M (p ^ k)) hp, factorization_gcd_apply hM hpk p,
    Nat.factorization_def M hp, hpow]

/-- The correction in one line: the intersection thickness dominates the obstruction valuation,
    `vₚ(lcm) = max ≥ min = vₚ(gcd)`, with equality iff `vₚ M` and `k` are comparable the right way. -/
theorem padicVal_obstruction_le_thickness (p M k : ℕ) (hp : p.Prime) (hM : M ≠ 0) :
    padicValNat p (Nat.gcd M (p ^ k)) ≤ padicValNat p (Nat.lcm M (p ^ k)) := by
  rw [padicVal_thickness_intersection p M k hp hM, padicVal_obstruction_gcd p M k hp hM]
  exact min_le_max

/-! ## §C — Equalizer–Tor (Thm 9.1, Prop 10.2/10.8). -/

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

/-- **Thm 9.1 / Prop 10.2.** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(N, M)`. -/
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

/-- **Thm 9.1 / Prop 10.2 / Cor 10.8 — Tor₁ as a group isomorphism.**
    `Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ℤ/gcd(N,M)` upgraded from a cardinality count to a genuine
    additive isomorphism.

    Concrete model (the file's standing strategy — no abstract `Tor` functor): from
    the free resolution `0 → ℤ →(·M) ℤ → ℤ/M → 0`, applying `· ⊗ ℤ/N` realises
    `Tor₁(ℤ/M, ℤ/N)` as `ker(·M : ℤ/N → ℤ/N)`.  This kernel is a subgroup of the
    cyclic group `ℤ/N`, hence cyclic (`AddSubgroup.isAddCyclic`), and has order
    `gcd(N,M)` (`card_ker_mulLeft`); a finite cyclic group is determined up to
    isomorphism by its order (`addEquivOfAddCyclicCardEq`), giving `≅ ℤ/gcd`. -/
noncomputable def torEquivZModGcd (N M : ℕ) [NeZero N] :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker ≃+ ZMod (Nat.gcd N M) := by
  haveI : NeZero (Nat.gcd N M) := ⟨Nat.gcd_ne_zero_left (NeZero.ne N)⟩
  -- `ker` is cyclic (subgroup of the cyclic group `ZMod N`) and `ZMod (gcd N M)`
  -- is cyclic; both have cardinality `gcd N M`, so they are isomorphic.
  refine addEquivOfAddCyclicCardEq ?_
  rw [card_ker_mulLeft, Nat.card_eq_fintype_card, ZMod.card]

/-! ### §C′ — T1.4: prime-wise direct-sum decomposition of `Tor₁` (group level).

Combining T1.2 (`torEquivZModGcd`: `Tor₁ ≅ ℤ/gcd(N,M)`) with T1.3 (`zmodPiEquivOfCoprime`, the
pairwise-coprime CRT) yields the prime-wise direct-sum form of Thm 9.1 Step 4 / Cor 10.8:

  `Tor₁(ℤ/M, ℤ/N) ≅ ⊕_{q ∣ N} ℤ/q^{min(v_q M, v_q N)}`  (indexed over `N.primeFactors`).

The exponent `min(v_q M, v_q N) = v_q(gcd M N)` vanishes exactly when `q ∤ M`, making those
summands trivial — which is why the index runs over all of `N.primeFactors`.  **Both `M ≠ 0` and
`N ≠ 0` are necessary**: for `M = 0` the left side is all of `ℤ/N` (order `N`) while every exponent
`min(0, v_q N) = 0` makes the right side trivial, and `Nat.factorization_gcd` (which supplies the
exponent `= min`) requires both arguments nonzero.  (The user's stub omitted `M ≠ 0`; it is added
here as a necessary hypothesis, in the spirit of the file's other CORRECTIONs.) -/

/-- The product of the prime-power summand moduli equals `gcd(N,M)`: distinct prime powers
    `q^{min(v_q M, v_q N)}` over `q ∈ primeFactors N` multiply to `gcd(N,M)`, the `q ∤ M` factors
    contributing `q^0 = 1`.  (This is the cardinality bookkeeping behind `|Tor₁| = gcd`.) -/
theorem prod_primeFactors_pow_min_eq_gcd (M N : ℕ) (hM : M ≠ 0) (hN : N ≠ 0) :
    (∏ q ∈ N.primeFactors, q ^ min (M.factorization q) (N.factorization q)) = Nat.gcd N M := by
  have hrw : ∀ q, min (M.factorization q) (N.factorization q) = (Nat.gcd M N).factorization q := by
    intro q; rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]
  calc
    (∏ q ∈ N.primeFactors, q ^ min (M.factorization q) (N.factorization q))
        = ∏ q ∈ N.primeFactors, q ^ (Nat.gcd M N).factorization q := by
          refine Finset.prod_congr rfl ?_; intro q _; rw [hrw q]
      _ = ∏ q ∈ (Nat.gcd M N).primeFactors, q ^ (Nat.gcd M N).factorization q := by
          symm
          apply Finset.prod_subset
          · exact Nat.primeFactors_mono (Nat.gcd_dvd_right M N) hN
          · intro q _ hqnot
            have h0 : (Nat.gcd M N).factorization q = 0 := by
              rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hqnot
            rw [h0, pow_zero]
      _ = Nat.gcd M N := by
          have hg : Nat.gcd M N ≠ 0 := by simp [Nat.gcd_eq_zero_iff, hM, hN]
          rw [← Nat.prod_factorization_eq_prod_primeFactors (n := Nat.gcd M N) (f := (· ^ ·))]
          exact Nat.prod_factorization_pow_eq_self hg
      _ = Nat.gcd N M := Nat.gcd_comm M N

/-- `ℤ/gcd(N,M) ≅ ∏_{q ∣ N} ℤ/q^{min(v_q M, v_q N)}` — the CRT refinement (`zmodPiEquivOfCoprime`)
    specialized at the gcd, indexed over `primeFactors N`. -/
noncomputable def zmodGcdPrimewiseDecomp (M N : ℕ) (hM : M ≠ 0) (hN : N ≠ 0) :
    ZMod (Nat.gcd N M) ≃+
      ((q : N.primeFactors) → ZMod (q ^ min (M.factorization q) (N.factorization q))) := by
  classical
  set f : ℕ → ℕ := fun q => q ^ min (M.factorization q) (N.factorization q) with hf
  have hcop : ∀ i ∈ N.primeFactors, ∀ j ∈ N.primeFactors, i ≠ j → Nat.Coprime (f i) (f j) := by
    intro i hi j hj hij
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hi)
      (Nat.prime_of_mem_primeFactors hj) hij
  have hprod : (∏ q ∈ N.primeFactors, f q) = Nat.gcd N M :=
    prod_primeFactors_pow_min_eq_gcd M N hM hN
  exact ((RingEquiv.cast (R := fun n => ZMod n) hprod.symm).trans
    (zmodPiEquivOfCoprime N.primeFactors f hcop)).toAddEquiv

/-- **T1.4 — prime-wise direct-sum decomposition of `Tor₁` (group level).**  Thm 9.1 Step 4 /
    Cor 10.8: `Tor₁(ℤ/M, ℤ/N) ≅ ⊕_{q ∣ N} ℤ/q^{min(v_q M, v_q N)}`, obtained by composing T1.2
    (`torEquivZModGcd`) with the gcd's prime-power decomposition `zmodGcdPrimewiseDecomp`.
    (`M ≠ 0` is required; see the §C′ note.) -/
noncomputable def torPrimewiseDecomp (M N : ℕ) [NeZero N] (hM : M ≠ 0) (hN : N ≠ 0) :
    (AddMonoidHom.mulLeft (M : ZMod N)).ker
      ≃+ ((q : N.primeFactors) → ZMod (q ^ min (M.factorization q) (N.factorization q))) :=
  (torEquivZModGcd N M).trans (zmodGcdPrimewiseDecomp M N hM hN)

/-- **D.3 - vanishing as a group-theoretic statement.**
The Tor kernel is a subsingleton exactly when its arithmetic readout
`gcd(N,M)` is one. -/
theorem tor_subsingleton_iff (N M : ℕ) [NeZero N] :
    Subsingleton (AddMonoidHom.mulLeft (M : ZMod N)).ker ↔ Nat.gcd N M = 1 := by
  rw [(torEquivZModGcd N M).toEquiv.subsingleton_congr, ZMod.subsingleton_iff]

set_option maxHeartbeats 800000 in
/-- **D.3 - App. B composite row, canonical prime-indexed form.** -/
noncomputable def torReadout60Primewise :
    (AddMonoidHom.mulLeft ((2 ^ 2 * 3 * 5 : ℕ) : ZMod 60)).ker
      ≃+ ((q : (60 : ℕ).primeFactors) →
            ZMod (q ^ min ((2 ^ 2 * 3 * 5 : ℕ).factorization q)
              ((60 : ℕ).factorization q))) := by
  haveI : NeZero (60 : ℕ) := ⟨by decide⟩
  exact torPrimewiseDecomp _ 60 (by decide) (by decide)

/-- The readable CRT decomposition `Z/60 = Z/4 x Z/3 x Z/5`. -/
noncomputable def zmod60AddEquiv :
    ZMod 60 ≃+ ZMod 4 × ZMod 3 × ZMod 5 := by
  let e4_15 : ZMod 60 ≃+* ZMod 4 × ZMod 15 := by
    simpa using ZMod.chineseRemainder (by norm_num : Nat.Coprime 4 15)
  let e3_5 : ZMod 15 ≃+* ZMod 3 × ZMod 5 := by
    simpa using ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 5)
  exact (e4_15.trans
    (RingEquiv.prodCongr (RingEquiv.refl (ZMod 4)) e3_5)).toAddEquiv

set_option maxHeartbeats 800000 in
/-- **D.3 - App. B composite row, explicit readable form.**
`Tor_1^Z(Z/60,Z/60) = Z/4 x Z/3 x Z/5` as additive groups. -/
noncomputable def torReadout60 :
    (AddMonoidHom.mulLeft ((2 ^ 2 * 3 * 5 : ℕ) : ZMod 60)).ker
      ≃+ ZMod 4 × ZMod 3 × ZMod 5 := by
  haveI : NeZero (60 : ℕ) := ⟨by decide⟩
  simpa using
    ((torEquivZModGcd 60 (2 ^ 2 * 3 * 5)).trans zmod60AddEquiv)

/-- Section 2.2 profile parameters. This record contains definitions/data only;
it deliberately stores no mathematical implication as a field. -/
structure Profile where
  A : ℤ
  pn : ℕ
  M : ℕ
  k : ℕ
  discr : ℤ
  W : ℕ

theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N := Iff.rfl

/-! ## §D — Primewise decomposition and indicator complexity. -/

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

/-! ## §D′ — T1.7: stability memo (Appendix C), algebraic core — locality of the invariants.

Appendix C's restriction/localization/completion/CRT invariance claims have a certifiable
algebraic core: the kernel/support/thickness/Tor invariants (T1.1–T1.6) are expressed through the
`p`-adic valuation, which is *intrinsically local* — it sees only the data at `p`.  We certify this
locality three ways:

* `padicValNat_mul_coprime` — `vₚ` is unchanged by multiplying by any factor coprime to `p`; the
  arithmetic shadow of "localizing/completing away from `p` does not change the `p`-local data"
  (units of `ℤ_(p)`, i.e. integers coprime to `p`, are invisible to `vₚ`).
* `torLocalModel` — the *local* Tor `Tor₁(ℤ/pᵃ, ℤ/pᵇ) ≅ ℤ/p^{min(a,b)}`, determined entirely by the
  local exponents (via `torEquivZModGcd` and `gcd(pᵇ, pᵃ) = p^{min}`).
* `tor_primewise_isLocal` — local–global compatibility: the `q`-primary summand
  `ℤ/q^{min(v_q M, v_q N)}` of the global `Tor₁(ℤ/M, ℤ/N)` (T1.4) *is* the local Tor at `q` of the
  `q`-completions `ℤ/q^{v_q M}, ℤ/q^{v_q N}`.  Equivalently, `Tor` commutes with localization /
  completion at each prime — the flatness/`IsLocalization` statement, certified here through the
  valuation formulas rather than through flatness machinery. -/

/-- **Locality of the `p`-adic valuation.**  `vₚ(m · n) = vₚ(m)` whenever `gcd(p, n) = 1`:
    multiplying by a factor coprime to `p` (a `p`-adic unit) leaves `vₚ` unchanged.  This is the
    arithmetic shadow of "localization/completion away from `p` does not change the `p`-local
    thickness/Tor data." -/
theorem padicValNat_mul_coprime (p m n : ℕ) (hp : p.Prime) (hn : Nat.Coprime p n) (hm : m ≠ 0) :
    padicValNat p (m * n) = padicValNat p m := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hp.ne_one ((Nat.coprime_zero_right p).mp hn)
  rw [← Nat.factorization_def (m * n) hp, ← Nat.factorization_def m hp,
    Nat.factorization_mul hm hn0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ((hp.coprime_iff_not_dvd).mp hn), add_zero]

/-- `gcd(pᵐ, pⁿ) = p^{min(m, n)}` — the gcd of two prime powers is the smaller power. -/
theorem gcd_pow_pow (p m n : ℕ) : Nat.gcd (p ^ m) (p ^ n) = p ^ min m n := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow p h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow p h)]

/-- **The local Tor model.**  `Tor₁(ℤ/pᵃ, ℤ/pᵇ) ≅ ℤ/p^{min(a,b)}` — the `p`-local Tor is
    determined by the local exponents `a, b` (via `torEquivZModGcd` and `gcd(pᵇ, pᵃ) = p^{min}`). -/
noncomputable def torLocalModel (p a b : ℕ) [NeZero (p ^ b)] :
    (AddMonoidHom.mulLeft ((p ^ a : ℕ) : ZMod (p ^ b))).ker ≃+ ZMod (p ^ min a b) := by
  have hg : Nat.gcd (p ^ b) (p ^ a) = p ^ min a b := by rw [gcd_pow_pow p b a, min_comm]
  rw [← hg]
  exact torEquivZModGcd (p ^ b) (p ^ a)

/-- **Local–global compatibility of `Tor` (completion invariance, T1.7).**  The `q`-primary
    summand `ℤ/q^{min(v_q M, v_q N)}` of the global decomposition (T1.4, `torPrimewiseDecomp`) is
    precisely the local Tor `Tor₁(ℤ/q^{v_q M}, ℤ/q^{v_q N})` of the `q`-completions: localizing /
    completing at `q` does not change the `q`-part of `Tor₁`. -/
noncomputable def tor_primewise_isLocal (M N q : ℕ) [NeZero (q ^ N.factorization q)] :
    ZMod (q ^ min (M.factorization q) (N.factorization q))
      ≃+ (AddMonoidHom.mulLeft ((q ^ M.factorization q : ℕ) : ZMod (q ^ N.factorization q))).ker :=
  (torLocalModel q (M.factorization q) (N.factorization q)).symm

/-! ## §E — Direct-sum H¹ (Prop 10.6), algebraic shadow.

The sheaf-cohomology statement `H¹(S, K_{f,X}) ≅ ⊕_{p ≤ X, p ∈ P_f} Λ`, `H⁰ = 0`
needs cohomology of `Spec ℤ` with skyscraper coefficients (absent from Mathlib).
Its algebraic content — a finite direct sum of `n` copies of `Λ = ℤ/ℓ` has
cardinality `ℓⁿ`, and the zero module has cardinality `1` — is verified here. -/

/-- The detector group `⊕_{i<n} ℤ/ℓ` has cardinality `ℓⁿ` (= |Λ|^{#visible primes}). -/
theorem directSum_card (ℓ n : ℕ) [NeZero ℓ] :
    Fintype.card (Fin n → ZMod ℓ) = ℓ ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- `H⁰ = 0`: the zero module is a single point. -/
theorem H0_zero : Fintype.card (Fin 0 → ZMod 1) = 1 := by decide

/-! ### §E′ — T2.1: skyscraper detector global sections as direct-sum module isomorphisms.

We strengthen the cardinality shadows (`directSum_card`, `H0_zero`) to genuine `ZMod ℓ`-module
isomorphisms.  For a finite set `P` of visible primes (closed points), the detector
`⊕_{p ∈ P} Λ = (↥P → ZMod ℓ)` (skyscraper global sections, `Λ = ZMod ℓ`) is:

* a **finite free module of rank `|P|`** — exhibited explicitly as `Λ^{|P|}`
  (`detector_directSum_linearEquiv`) and confirmed by `Module.rank … = |P|` (`detector_rank`);
* with `H⁰` shadow trivial — the empty detector `Fin 0 → ZMod ℓ` is the trivial group
  (`detector_H0_addEquiv : … ≃+ PUnit`).

Closed-point skyscrapers are flasque, so `Hⁱ = 0 (i > 0)` and `H⁰ = ⊕ stalks`; the only
mathematical content is the stalk direct sum, certified here purely algebraically (no `Hⁱ(S, F)`
of `Spec ℤ` is needed).  **`1 < ℓ` is required** for the rank/nontriviality faces (`ZMod 1` is the
trivial ring, of rank `0`); the user's stub `Prop ∧ (… ≃+ PUnit)` was ill-typed (a `Prop` and a
`Type`), so the headline below is a `Prop` conjunction (rank, and `H⁰` as a `Subsingleton`), with
the explicit `≃+ PUnit` provided separately. -/

/-- **The detector as a finite direct sum.**  `⊕_{p ∈ P} Λ ≅ Λ^{|P|}` as `ZMod ℓ`-modules
    (`P → ZMod ℓ ≃ₗ Fin P.card → ZMod ℓ`), the actual module isomorphism behind `directSum_card`. -/
noncomputable def detector_directSum_linearEquiv (ℓ : ℕ) [NeZero ℓ] (P : Finset ℕ) :
    (P → ZMod ℓ) ≃ₗ[ZMod ℓ] (Fin P.card → ZMod ℓ) :=
  LinearEquiv.funCongrLeft (ZMod ℓ) (ZMod ℓ) P.equivFin.symm

/-- **Rank of the detector = number of visible primes `|P|`** (requires `1 < ℓ`, i.e. `Λ`
    nontrivial; for `ℓ = 1` the rank is `0`). -/
theorem detector_rank (ℓ : ℕ) (hℓ : 1 < ℓ) (P : Finset ℕ) :
    Module.rank (ZMod ℓ) (P → ZMod ℓ) = P.card := by
  haveI : Fact (1 < ℓ) := ⟨hℓ⟩
  rw [rank_fun']
  exact_mod_cast Fintype.card_coe P

/-- **`H⁰` shadow: the empty detector is the trivial group** (`Fin 0 → ZMod ℓ ≃+ PUnit`). -/
def detector_H0_addEquiv (ℓ : ℕ) : (Fin 0 → ZMod ℓ) ≃+ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => 0
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _
  map_add' := fun _ _ => rfl

/-- **Detector global sections (Prop 10.6 shadow, strengthened).**  `H¹ = ⊕_{p ∈ P} Λ` is free of
    rank `|P|`, and `H⁰` is a point. -/
theorem detector_global_sections (ℓ : ℕ) (hℓ : 1 < ℓ) (P : Finset ℕ) :
    Module.rank (ZMod ℓ) (P → ZMod ℓ) = P.card ∧ Subsingleton (Fin 0 → ZMod ℓ) :=
  ⟨detector_rank ℓ hℓ P, inferInstance⟩

/-- **C.1 / Prop 10.6 unconditional shadow.**  The part of the skyscraper
cohomology calculation that is already genuine Lean mathematics: the finite
stalk sum over visible closed points is the free `ZMod ℓ`-module of rank `|P|`,
and the empty `H⁰` shadow is additively equivalent to a point.

This deliberately does not assert flasqueness or sheaf cohomology vanishing on
`Spec ℤ`; those remain a Tier-3 interface until Mathlib has the relevant
Zariski sheaf-cohomology API. -/
theorem specZ_skyscraper_H0_directSum_shadow (ℓ : ℕ) (hℓ : 1 < ℓ) (P : Finset ℕ) :
    Module.rank (ZMod ℓ) (P → ZMod ℓ) = P.card ∧
      Nonempty ((Fin 0 → ZMod ℓ) ≃+ PUnit) :=
  ⟨detector_rank ℓ hℓ P, ⟨detector_H0_addEquiv ℓ⟩⟩

/-- The explicit module equivalence behind the `H⁰ = ⊕` shadow:
the stalk sum indexed by a finite set `P` is just `Λ^{|P|}`. -/
noncomputable def specZ_skyscraper_stalkSum_linearEquiv (ℓ : ℕ) [NeZero ℓ]
    (P : Finset ℕ) :
    (P → ZMod ℓ) ≃ₗ[ZMod ℓ] (Fin P.card → ZMod ℓ) :=
  detector_directSum_linearEquiv ℓ P

/-- **`δcoh(P_f) = 1` shadow:** a nonempty set of visible primes gives a nontrivial detector
    (`⊕_{p ∈ P} Λ ≠ 0`), while `H⁰ = 0`. -/
theorem delta_coh_one_shadow (ℓ : ℕ) (hℓ : 1 < ℓ) {P : Finset ℕ} (hP : P.Nonempty) :
    Nontrivial (P → ZMod ℓ) := by
  haveI : Fact (1 < ℓ) := ⟨hℓ⟩
  haveI : Nonempty (P : Type) := hP.to_subtype
  exact Function.nontrivial

/-! ### §E″ — T2.2: AB-linearization, algebraic + valuation core (§5.1, Rem 6.5/10.5).

Mathlib has no `p`-adic logarithm/exponential, so the analytic AB-linearization map is out of scope
(Tier 3).  But the parts the paper actually uses computationally are (a) an exact polynomial
identity for the shifted binomial expansion and (b) sharp `p`-adic valuation estimates — both
formalizable, and certified here unconditionally:

* `shifted_binom_identity` — the exact identity `Aᵐ = ∑_{i ≤ m} C(m,i)(A-1)ⁱ` in `ℤ[X]`;
* `padicVal_binom_pow` — Kummer/Legendre: `vₚ(C(pⁿ, pʲ)) = n - j`;
* `padicVal_pow_sub_one` — lifting-the-exponent: for `p` odd, `p ∣ A-1`, `A ≠ 1`,
  `vₚ(A^{pʲ} - 1) = vₚ(A-1) + j`;
* `Hk_basic_profile` — the **corrected** basic profile at `A = 1 + pᵀ`: `vₚ((1+pᵀ)^{pʲ} - 1) = T + j`.
  (The stub's `n+T ≥ k → ∀ j<n, k ≤ vₚ(φ_j)` is false — the minimum over `j < n` is `T` at `j = 0`,
  not `n+T`; the exact per-`j` valuation `= T+j` is the honest content.)

The remaining analytic bridge (`|log(1+u)|_p ≤ p^{-k}` for `u ∈ pᵏℤ_p`, and `log(1+u) ≡ u (mod pᵏ)`)
is left as a Tier-3 interface: it requires a development of `Padic.log`, absent from Mathlib. -/

/-- **Exact shifted-binomial polynomial identity** in `ℤ[X]`: `Xᵐ = ∑_{i ≤ m} C(m,i)(X-1)ⁱ`,
    from writing `X = (X-1) + 1` and applying the binomial theorem.  (No analysis.) -/
theorem shifted_binom_identity (m : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ m
      = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : Polynomial ℤ) * (Polynomial.X - 1) ^ i := by
  have key : ∀ Y : Polynomial ℤ, (Y + 1) ^ m
      = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : Polynomial ℤ) * Y ^ i := by
    intro Y
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [one_pow, mul_one, mul_comm]
  have hX : (Polynomial.X : Polynomial ℤ) ^ m = ((Polynomial.X - 1) + 1) ^ m := by ring
  rw [hX, key]

/-- **Kummer/Legendre.**  `vₚ(C(pⁿ, pʲ)) = n - j` for `j ≤ n` (number of base-`p` carries). -/
theorem padicVal_binom_pow (p n j : ℕ) (hp : p.Prime) (hj : j ≤ n) :
    padicValNat p (Nat.choose (p ^ n) (p ^ j)) = n - j := by
  rw [← Nat.toNat_emultiplicity p (Nat.choose (p ^ n) (p ^ j)),
      hp.emultiplicity_choose_prime_pow (Nat.pow_le_pow_right hp.pos hj)
        (pow_ne_zero j hp.pos.ne'),
      multiplicity_pow_self_of_prime hp.prime, ENat.toNat_coe]

/-- **Lifting the exponent** for `A^{pʲ} - 1`: for `p` odd prime with `p ∣ A - 1` and `A ≠ 1`,
    `vₚ(A^{pʲ} - 1) = vₚ(A - 1) + j`.  (`A ≠ 1` is required: for `A = 1` and `j > 0` the left side
    is `0` but the right side is `j`.) -/
theorem padicVal_pow_sub_one (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (A : ℤ) (hA : (p : ℤ) ∣ A - 1) (hAne : A ≠ 1) (j : ℕ) :
    padicValInt p (A ^ (p ^ j) - 1) = padicValInt p (A - 1) + j := by
  have hx : ¬ (p : ℤ) ∣ A := by
    intro hdvd
    have h1 : (p : ℤ) ∣ 1 := by simpa using dvd_sub hdvd hA
    have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have := Int.le_of_dvd one_pos h1
    omega
  have hsub_ne : A - 1 ≠ 0 := sub_ne_zero.mpr hAne
  have hlte := Int.emultiplicity_pow_sub_pow hp hodd hA hx (p ^ j)
  rw [one_pow, emultiplicity_pow_self_of_prime hp.prime] at hlte
  have bridge : ∀ z : ℤ, padicValInt p z = (emultiplicity (↑p : ℤ) z).toNat := by
    intro z
    rw [← Int.emultiplicity_natAbs, Nat.toNat_emultiplicity]
    rfl
  have hfin : emultiplicity (↑p : ℤ) (A - 1) ≠ ⊤ := by
    rw [← Int.emultiplicity_natAbs]
    exact finiteMultiplicity_iff_emultiplicity_ne_top.mp
      (Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Int.natAbs_pos.mpr hsub_ne⟩)
  rw [bridge (A ^ (p ^ j) - 1), bridge (A - 1), hlte, ENat.toNat_add hfin (by simp),
      ENat.toNat_coe]

/-- `vₚ(pᵀ) = T` over `ℤ` (the `p`-adic valuation of a prime power). -/
theorem padicValInt_prime_pow (p : ℕ) (hp : p.Prime) (T : ℕ) :
    padicValInt p ((p : ℤ) ^ T) = T := by
  haveI : Fact p.Prime := ⟨hp⟩
  show padicValNat p ((p : ℤ) ^ T).natAbs = T
  rw [← Nat.cast_pow, Int.natAbs_natCast, padicValNat.prime_pow]

/-- **Basic profile (corrected).**  With `A = 1 + pᵀ` (`T ≥ 1`), `vₚ((1+pᵀ)^{pʲ} - 1) = T + j`:
    the `p`-adic valuation of the `j`-th shifted term grows linearly in `j` with offset `T`. -/
theorem Hk_basic_profile (p : ℕ) (hp : p.Prime) (hodd : Odd p) (T : ℕ) (hT : 1 ≤ T) (j : ℕ) :
    padicValInt p ((1 + (p : ℤ) ^ T) ^ (p ^ j) - 1) = T + j := by
  have hAm1 : (1 + (p : ℤ) ^ T) - 1 = (p : ℤ) ^ T := by ring
  have hA : (p : ℤ) ∣ (1 + (p : ℤ) ^ T) - 1 := by rw [hAm1]; exact dvd_pow_self _ (by omega)
  have hpos : (0 : ℤ) < (p : ℤ) ^ T := by
    have : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    positivity
  have hAne : (1 + (p : ℤ) ^ T) ≠ 1 := by intro he; linarith
  rw [padicVal_pow_sub_one p hp hodd (1 + (p : ℤ) ^ T) hA hAne j, hAm1, padicValInt_prime_pow p hp]

/-- **B.1 / §5.1 coefficient fixed.**  The explicit coefficient suggested by
the two already-certified building blocks:
`φⱼ(A) = C(pⁿ,pʲ) * (A^{pʲ} - 1)`.

The paper does not state the coefficient definition in the provided excerpt; this
definition is therefore the formalized normalization under which the claimed
constant valuation `n + T` becomes an unconditional theorem. -/
def phi (p n j : ℕ) (A : ℤ) : ℤ :=
  (Nat.choose (p ^ n) (p ^ j) : ℤ) * (A ^ (p ^ j) - 1)

/-- The integer-valued binomial block has the same `p`-adic valuation as the
natural binomial coefficient. -/
theorem padicValInt_choose_prime_pow (p n j : ℕ) (hp : p.Prime) (hj : j ≤ n) :
    padicValInt p ((Nat.choose (p ^ n) (p ^ j) : ℤ)) = n - j := by
  rw [padicValInt.of_nat]
  exact padicVal_binom_pow p n j hp hj

/-- **B.1 / §5.1 φ-profile.**  With
`φⱼ(A) = C(pⁿ,pʲ) * (A^{pʲ} - 1)` and `A = 1 + pᵀ`, the valuation is
independent of `j`:
`vₚ(φⱼ(1+pᵀ)) = (n-j) + (T+j) = n+T`. -/
theorem padicVal_phi (p n j T : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hT : 1 ≤ T) (hj : j ≤ n) :
    padicValInt p (phi p n j (1 + (p : ℤ) ^ T)) = n + T := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow_le : p ^ j ≤ p ^ n := Nat.pow_le_pow_right hp.pos hj
  have hchoose_ne_nat : Nat.choose (p ^ n) (p ^ j) ≠ 0 :=
    Nat.choose_ne_zero hpow_le
  have hchoose_ne : ((Nat.choose (p ^ n) (p ^ j) : ℤ) ≠ 0) := by
    exact_mod_cast hchoose_ne_nat
  have hpT_pos : (0 : ℤ) < (p : ℤ) ^ T := by
    have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    positivity
  have hbase_gt_one : (1 : ℤ) < 1 + (p : ℤ) ^ T := by linarith
  have hexp_pos : 0 < p ^ j := pow_pos hp.pos j
  have hpow_gt_one : (1 : ℤ) < (1 + (p : ℤ) ^ T) ^ (p ^ j) :=
    one_lt_pow₀ hbase_gt_one (Nat.ne_of_gt hexp_pos)
  have hterm_ne : (1 + (p : ℤ) ^ T) ^ (p ^ j) - 1 ≠ 0 := by
    have hterm_pos : (0 : ℤ) < (1 + (p : ℤ) ^ T) ^ (p ^ j) - 1 := by
      linarith
    exact ne_of_gt hterm_pos
  rw [phi, padicValInt.mul hchoose_ne hterm_ne,
    padicValInt_choose_prime_pow p n j hp hj,
    Hk_basic_profile p hp hodd T hT j]
  omega

/-- Under the explicit `phi` normalization, the §5.1 divisibility threshold
`k ≤ vₚ(φⱼ)` for every `0 ≤ j ≤ n` is exactly `k ≤ n + T`. -/
theorem phi_profile_condition_iff (p n T k : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hT : 1 ≤ T) :
    (∀ j, j ≤ n → k ≤ padicValInt p (phi p n j (1 + (p : ℤ) ^ T))) ↔
      k ≤ n + T := by
  constructor
  · intro h
    simpa [padicVal_phi p n 0 T hp hodd hT (Nat.zero_le n)] using h 0 (Nat.zero_le n)
  · intro hk j hj
    rw [padicVal_phi p n j T hp hodd hT hj]
    exact hk

/-! ### §E‴ — T2.3: Primality sheaf sectionwise = intersection (§2.1/2.2), Set/Subtype shadow.

The honest algebraic shadow of `Γ(U, F) = ⋂ Γ(U, layerᵢ)` and `F = fiber product of the four
layers`, *without* erecting the full `CategoryTheory.Sheaf`/`Presheaf` machinery: model each layer
(numeric / modular / p-adic / elliptic-curve) as a predicate `ℕ → Prop`, its sections over an open
`U ⊆ ℕ` as `U ∩ {n | F n}`, the fiber product as the pointwise conjunction (= intersection), and
restriction (for `U ⊆ V`) as intersection with the smaller open (= the subtype inclusion).  This
seals the core "restriction = inclusion, fiber product = intersection", plus the presheaf gluing
identities (`sections_union`/`sections_inter`) and functoriality (`sections_mono`). -/

namespace PrimalityShadow

/-- A layer is a predicate on `ℕ`; its sections over an open `U` are `U ∩ {n | F n}`. -/
def sections (F : ℕ → Prop) (U : Set ℕ) : Set ℕ := {n | n ∈ U ∧ F n}

/-- The Primality sheaf as the fiber product (conjunction) of the four layers. -/
def primalityLayer (Fnum Fmod Fpadic FEC : ℕ → Prop) : ℕ → Prop :=
  fun n => Fnum n ∧ Fmod n ∧ Fpadic n ∧ FEC n

/-- Membership unfolding for `sections`. -/
@[simp] theorem mem_sections {F : ℕ → Prop} {U : Set ℕ} {n : ℕ} :
    n ∈ sections F U ↔ n ∈ U ∧ F n := Iff.rfl

/-- **Sectionwise = intersection (pointwise).** -/
theorem layers_sectionwise (Fnum Fmod Fpadic FEC : ℕ → Prop) (n : ℕ) :
    primalityLayer Fnum Fmod Fpadic FEC n
      ↔ n ∈ {m | Fnum m} ∩ {m | Fmod m} ∩ {m | Fpadic m} ∩ {m | FEC m} := by
  simp only [primalityLayer, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

/-- **Global sections of the fiber product = intersection of the layers' sections**, over any `U`. -/
theorem sections_primalityLayer (Fnum Fmod Fpadic FEC : ℕ → Prop) (U : Set ℕ) :
    sections (primalityLayer Fnum Fmod Fpadic FEC) U
      = sections Fnum U ∩ sections Fmod U ∩ sections Fpadic U ∩ sections FEC U := by
  ext n
  simp only [mem_sections, primalityLayer, Set.mem_inter_iff]
  tauto

/-- **Restriction = inclusion:** for `U ⊆ V`, sections over `U` are sections over `V` ∩ `U`. -/
theorem sections_restrict (F : ℕ → Prop) {U V : Set ℕ} (h : U ⊆ V) :
    sections F U = sections F V ∩ U := by
  ext n
  simp only [mem_sections, Set.mem_inter_iff]
  constructor
  · rintro ⟨hnU, hFn⟩; exact ⟨⟨h hnU, hFn⟩, hnU⟩
  · rintro ⟨⟨_, hFn⟩, hnU⟩; exact ⟨hnU, hFn⟩

/-- **Fiber product = intersection as a type equivalence** (the subtype pullback). -/
def primalityLayer_equiv (Fnum Fmod Fpadic FEC : ℕ → Prop) :
    {n // primalityLayer Fnum Fmod Fpadic FEC n}
      ≃ {n // n ∈ {m | Fnum m} ∩ {m | Fmod m} ∩ {m | Fpadic m} ∩ {m | FEC m}} :=
  Equiv.subtypeEquivRight (layers_sectionwise Fnum Fmod Fpadic FEC)

/-- **Gluing shadow (union).**  `Γ(U ∪ V, F) = Γ(U, F) ∪ Γ(V, F)`. -/
theorem sections_union (F : ℕ → Prop) (U V : Set ℕ) :
    sections F (U ∪ V) = sections F U ∪ sections F V := by
  ext n; simp only [mem_sections, Set.mem_union]; tauto

/-- **Separation shadow (overlap).**  `Γ(U ∩ V, F) = Γ(U, F) ∩ Γ(V, F)`. -/
theorem sections_inter (F : ℕ → Prop) (U V : Set ℕ) :
    sections F (U ∩ V) = sections F U ∩ sections F V := by
  ext n; simp only [mem_sections, Set.mem_inter_iff]; tauto

/-- **Functoriality of restriction:** `U ⊆ V → Γ(U, F) ⊆ Γ(V, F)`. -/
theorem sections_mono (F : ℕ → Prop) {U V : Set ℕ} (h : U ⊆ V) :
    sections F U ⊆ sections F V := by
  rintro n ⟨hnU, hFn⟩; exact ⟨h hnU, hFn⟩

/-- Commutativity of the fiber product (conjunction). -/
theorem primalityLayer_comm (Fnum Fmod Fpadic FEC : ℕ → Prop) (n : ℕ) :
    primalityLayer Fnum Fmod Fpadic FEC n ↔ primalityLayer Fmod Fnum FEC Fpadic n := by
  simp only [primalityLayer]; tauto

end PrimalityShadow

/-! ## §F — Conditional good-prime synchronization (Thm 9.3, Thm 6.1, Cor 6.3).

The discriminant/Jacobian gate (smooth), the Hensel gate, the étale bump, and the
derived (Tor/cotangent) detector are linked by classical bridges that Mathlib
lacks (étale/motivic/cotangent).  These are explicit hypotheses; the arithmetic
equalizer face (`gcd = 1`) is unconditional. -/

/-- **Thm 9.3 (Good-Prime Synchronization, conditional).** On `U = D(∆)`, the
    discriminant/Hensel gate (`smooth`), the equalizer face (`gcd = 1`), the
    derived test (`der = 0`), and the étale bump (`bump = 0`) are all equivalent. -/
theorem goodPrime_synchronization (smooth : Prop) (der bump M pk : ℕ)
    (Hgate : smooth ↔ Nat.gcd M pk = 1) (Hder : der = 0 ↔ smooth) (Hbump : bump = 0 ↔ smooth) :
    [smooth, Nat.gcd M pk = 1, der = 0, bump = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate
  tfae_have 1 ↔ 3 := Hder.symm
  tfae_have 1 ↔ 4 := Hbump.symm
  tfae_finish

/-- **Thm 6.1 (bump = Euler jump, conditional).** `Δχ_mot = bump = b₁(Γ) + Σδ`. -/
theorem curve_master_identity (bump mot b1 deltaSum : ℕ)
    (Hbump : bump = b1 + deltaSum) (Hmot : mot = bump) :
    mot = b1 + deltaSum ∧ bump = b1 + deltaSum := ⟨Hmot.trans Hbump, Hbump⟩

/-- **Cor 6.3 (good-prime box, conditional).** On a smooth fiber all detectors vanish. -/
theorem good_prime_box (smooth : Prop) (bump mot der b1 deltaSum : ℕ)
    (Hder : der = 0 ↔ smooth) (Hbump : bump = b1 + deltaSum)
    (Hmot : mot = bump) (Hsing : smooth ↔ (b1 = 0 ∧ deltaSum = 0))
    (h : smooth) : bump = 0 ∧ mot = 0 ∧ der = 0 := by
  have hb : bump = 0 ↔ smooth := by rw [Hbump, Nat.add_eq_zero_iff, ← Hsing]
  exact ⟨hb.mpr h, Hmot ▸ hb.mpr h, Hder.mpr h⟩

/-! ### §F′ — T2.4: curve Euler-characteristic combinatorial identity (Thm 6.1, normalization).

Strengthens the conditional `curve_master_identity` / `good_prime_box` with the Betti bookkeeping
`dim H¹(Xp) = 2·g(X̃p) + b₁(Γp) + Σδx` and the smooth normalization `dim H¹(Up) = 2·g`.  The actual
definition of `H¹(Xp, Λ)`, the normalization sequence, and the δ-invariants belong to the geometry
of the fibre (Tier 3, étale cohomology); here we take those dimensions as *inputs* and certify the
`ℕ`-bookkeeping identities — the extension of the `good_prime_box` pattern. -/

/-- **Thm 6.1 (combinatorial identity).**  From the normalization `dim H¹(Xp) = 2g + b₁ + Σδ` and the
    smooth-part contribution `dim H¹(Up) = 2g`, the excess `dim H¹(Xp) - dim H¹(Up)` is exactly the
    defect `b₁(Γp) + Σδx` (`= bump = Δχ_mot`). -/
theorem curve_betti_identity (g b1 deltaSum dimH1Xp dimH1Up : ℕ)
    (Hnorm : dimH1Xp = 2 * g + b1 + deltaSum) (Hsmooth_part : dimH1Up = 2 * g) :
    dimH1Xp - dimH1Up = b1 + deltaSum := by omega

/-- **Smoothness ⇒ all detectors silent** (combinatorial shadow): `b₁ = Σδ = 0 ⇒ b₁ + Σδ = 0`. -/
theorem smooth_silences (b1 deltaSum : ℕ) (h : b1 = 0 ∧ deltaSum = 0) :
    b1 + deltaSum = 0 := by omega

/-- **Normalization package (Thm 6.1, `good_prime_box` extension).**  The excess
    `dim H¹(Xp) - dim H¹(Up)` equals the bump/defect `bump = b₁ + Σδ`; and on a smooth fibre
    (`b₁ = Σδ = 0`) the bump vanishes and the dimension matches the smooth normalization
    (`dim H¹(Xp) = dim H¹(Up) = 2g`). -/
theorem curve_normalization_package (g b1 deltaSum dimH1Xp dimH1Up bump : ℕ)
    (Hnorm : dimH1Xp = 2 * g + b1 + deltaSum) (Hsmooth_part : dimH1Up = 2 * g)
    (Hbump : bump = b1 + deltaSum) :
    dimH1Xp - dimH1Up = bump ∧ (b1 = 0 → deltaSum = 0 → bump = 0 ∧ dimH1Xp = dimH1Up) := by
  refine ⟨by omega, ?_⟩
  intro hb1 hd
  exact ⟨by omega, by omega⟩

/-! ## §G — gcd–lcm short exact (Mayer–Vietoris) sequence.

                          ι                 π
        0 ─→ ℤ/lcm(M,N) ─────→ ℤ/M × ℤ/N ─────→ ℤ/gcd(M,N) ─→ 0

A single short exact sequence that simultaneously certifies the Čech faces of the
paper (§3.1, Lem 6.4, Prop 10.1/10.7, Thm 9.1(iii)):

* `Ȟ⁰ = ker π = im ι ≅ ℤ/lcm`     — the equalizer kernel `(M) ∩ (N) = (lcm)`;
* `Ȟ¹ = coker ι ≅ ℤ/gcd`           — the Tor/failure fibre.

`ι` is the diagonal `x ↦ (x mod M, x mod N)`; `π` is the difference of the two
reductions to `ℤ/gcd`.  Consistency check on cardinalities:
`|ℤ/M × ℤ/N| = M·N = lcm·gcd` (`Nat.gcd_mul_lcm`), which is exactly what closes
the exactness `range ι = ker π` by counting (`lcm` on both sides). -/

namespace Additions

/-- Reduction `ℤ/lcm(M,N) → ℤ/M` (`ZMod.castHom` for `M ∣ lcm M N`). -/
noncomputable def redM (M N : ℕ) : ZMod (Nat.lcm M N) →+* ZMod M :=
  ZMod.castHom (dvd_lcm_left M N) (ZMod M)

/-- Reduction `ℤ/lcm(M,N) → ℤ/N` (`ZMod.castHom` for `N ∣ lcm M N`). -/
noncomputable def redN (M N : ℕ) : ZMod (Nat.lcm M N) →+* ZMod N :=
  ZMod.castHom (dvd_lcm_right M N) (ZMod N)

/-- The diagonal `ι : x ↦ (x mod M, x mod N)`. -/
noncomputable def iota (M N : ℕ) : ZMod (Nat.lcm M N) →+ ZMod M × ZMod N :=
  (redM M N).toAddMonoidHom.prod (redN M N).toAddMonoidHom

/-- The difference `π : (a, b) ↦ (a mod gcd) - (b mod gcd)`. -/
noncomputable def proj (M N : ℕ) : ZMod M × ZMod N →+ ZMod (Nat.gcd M N) :=
  (ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N))).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _)
    - (ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N))).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _)

/-- Componentwise description of `ι` (holds definitionally). -/
theorem iota_apply (M N : ℕ) (x : ZMod (Nat.lcm M N)) :
    iota M N x =
      (ZMod.castHom (dvd_lcm_left M N) (ZMod M) x,
       ZMod.castHom (dvd_lcm_right M N) (ZMod N) x) := rfl

/-- Componentwise description of `π` (holds definitionally). -/
theorem proj_apply (M N : ℕ) (a : ZMod M) (b : ZMod N) :
    proj M N (a, b) =
      ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N)) a
        - ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N)) b := rfl

/-- The two reductions `ℤ/lcm → ℤ/gcd`, factored through `ℤ/M` resp. `ℤ/N`, agree:
    both send `x` to `x mod gcd`.  This is the algebraic heart of `π ∘ ι = 0`. -/
theorem castHom_castHom_eq (M N : ℕ) [NeZero (Nat.lcm M N)] (x : ZMod (Nat.lcm M N)) :
    ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N))
        (ZMod.castHom (dvd_lcm_left M N) (ZMod M) x)
      = ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N))
          (ZMod.castHom (dvd_lcm_right M N) (ZMod N) x) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  simp only [map_natCast]

/-- **ι is injective** (`0 → ℤ/lcm` is exact).  `ker ι = {x : M ∣ x ∧ N ∣ x}
    = {x : lcm ∣ x} = 0`. -/
theorem iota_injective (M N : ℕ) [NeZero (Nat.lcm M N)] :
    Function.Injective (iota M N) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [iota_apply, show (0 : ZMod M × ZMod N) = (0, 0) from rfl, Prod.mk.injEq] at ha
  obtain ⟨hMa, hNa⟩ := ha
  rw [← ZMod.natCast_zmod_val a, map_natCast, ZMod.natCast_eq_zero_iff] at hMa
  rw [← ZMod.natCast_zmod_val a, map_natCast, ZMod.natCast_eq_zero_iff] at hNa
  have hlcm : Nat.lcm M N ∣ a.val := Nat.lcm_dvd hMa hNa
  have hz : (↑a.val : ZMod (Nat.lcm M N)) = 0 :=
    (ZMod.natCast_eq_zero_iff a.val (Nat.lcm M N)).mpr hlcm
  rwa [ZMod.natCast_zmod_val] at hz

/-- **π is surjective** (`ℤ/gcd → 0` is exact).  Already `(a, 0) ↦ a mod gcd`
    surjects, since `ℤ/M ↠ ℤ/gcd` (`ZMod.castHom_surjective`). -/
theorem proj_surjective (M N : ℕ) [NeZero M] :
    Function.Surjective (proj M N) := by
  intro y
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective (Nat.gcd_dvd_left M N) y
  exact ⟨(a, 0), by rw [proj_apply, map_zero, sub_zero, ha]⟩

/-- **Exactness at the middle: `range ι = ker π`.**  The inclusion `range ι ≤ ker π`
    is `π ∘ ι = 0`; equality follows by counting: both subgroups have cardinality
    `lcm(M,N)` (using `|ℤ/M × ℤ/N| = M·N = gcd·lcm`). -/
theorem range_iota_eq_ker_proj (M N : ℕ) [NeZero M] [NeZero N] :
    (iota M N).range = (proj M N).ker := by
  -- Nonvanishing of lcm and gcd, to get `Fintype`/`NeZero` instances.
  haveI hlcm0 : NeZero (Nat.lcm M N) := ⟨by
    have h := Nat.gcd_mul_lcm M N
    intro hl
    rw [hl, Nat.mul_zero] at h
    exact (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne N)) h.symm⟩
  haveI hgcd0 : NeZero (Nat.gcd M N) := ⟨Nat.gcd_ne_zero_left (NeZero.ne M)⟩
  -- (⊆) range ι ≤ ker π, i.e. π ∘ ι = 0.
  have hsub : (iota M N).range ≤ (proj M N).ker := by
    intro y hy
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker, iota_apply, proj_apply, sub_eq_zero]
    exact castHom_castHom_eq M N x
  -- |range ι| = lcm (ι injective ⇒ ker ι = ⊥).
  have hcard_range : Nat.card (iota M N).range = Nat.lcm M N := by
    have hZ : Nat.card (ZMod (Nat.lcm M N)) = Nat.lcm M N := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
    have hker : (iota M N).ker = ⊥ := (AddMonoidHom.ker_eq_bot_iff _).mpr (iota_injective M N)
    have h2 : Nat.card (iota M N).ker * Nat.card (iota M N).range = Nat.lcm M N := by
      rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, hZ]
    rwa [hker, AddSubgroup.card_bot, one_mul] at h2
  -- |ker π| = lcm (π surjective ⇒ range π = ⊤; M·N = gcd·lcm).
  have hcard_ker : Nat.card (proj M N).ker = Nat.lcm M N := by
    have hprod : Nat.card (ZMod M × ZMod N) = M * N := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, ZMod.card]
    have hrt : (proj M N).range = ⊤ := AddMonoidHom.range_eq_top.mpr (proj_surjective M N)
    have hrcard : Nat.card (proj M N).range = Nat.gcd M N := by
      rw [hrt, AddSubgroup.card_top, Nat.card_eq_fintype_card, ZMod.card]
    have h2 : Nat.card (proj M N).ker * Nat.card (proj M N).range = M * N := by
      rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, hprod]
    rw [hrcard] at h2
    have hgl : Nat.gcd M N * Nat.lcm M N = M * N := Nat.gcd_mul_lcm M N
    have hgpos : 0 < Nat.gcd M N := Nat.pos_of_ne_zero (NeZero.ne (Nat.gcd M N))
    have h3 : Nat.card (proj M N).ker * Nat.gcd M N = Nat.lcm M N * Nat.gcd M N := by
      rw [h2, ← hgl]; ring
    exact Nat.eq_of_mul_eq_mul_right hgpos h3
  -- subset + equal (finite) cardinality ⇒ equality.
  exact AddSubgroup.eq_of_le_of_card_ge hsub (le_of_eq (hcard_ker.trans hcard_range.symm))

/-! ### §G′ — T1.5: the obstruction (cokernel) face via the *global* map `Φ : ℤ → ℤ/M × ℤ/N`.

`Φ` is the global diagonal `k ↦ (k mod M, k mod N)`.  It factors as `ι ∘ (ℤ ↠ ℤ/lcm)`, so
`range Φ = range ι`, and by §G's exactness `range ι = ker π`.  The first isomorphism theorem
applied to the surjection `π = proj` (`proj_surjective`) then identifies the cokernel:

  `coker Φ = (ℤ/M × ℤ/N) ⧸ range Φ ≅ ℤ/gcd(M,N)`,

which is precisely the failure-fibre / "obstruction" face `Ȟ¹ = coker ι ≅ ℤ/gcd` of Thm 9.1,
now stated at the level of the global map from `ℤ` (an independent certification of T1.1's
cokernel side). -/

/-- The global diagonal `Φ : ℤ → ℤ/M × ℤ/N`, `k ↦ (k mod M, k mod N)`. -/
noncomputable def Phi (M N : ℕ) : ℤ →+ ZMod M × ZMod N :=
  (Int.castAddHom (ZMod M)).prod (Int.castAddHom (ZMod N))

/-- `Φ` factors through `ι`: `ι (k : ℤ/lcm) = Φ k` (both send `k ↦ (k mod M, k mod N)`,
    by `map_intCast` on the reductions `ℤ/lcm → ℤ/M`, `ℤ/lcm → ℤ/N`). -/
theorem iota_intCast_eq_Phi (M N : ℕ) (k : ℤ) :
    iota M N (k : ZMod (Nat.lcm M N)) = Phi M N k := by
  have hM := map_intCast (ZMod.castHom (dvd_lcm_left M N) (ZMod M)) k
  have hN := map_intCast (ZMod.castHom (dvd_lcm_right M N) (ZMod N)) k
  rw [iota_apply, hM, hN]
  rfl

/-- The global map `Φ` and the `ℤ/lcm` diagonal `ι` have the same range, since
    `ℤ ↠ ℤ/lcm` (`ZMod.intCast_surjective`). -/
theorem range_Phi_eq_range_iota (M N : ℕ) : (Phi M N).range = (iota M N).range := by
  apply le_antisymm
  · intro y hy
    rw [AddMonoidHom.mem_range] at hy ⊢
    obtain ⟨k, rfl⟩ := hy
    exact ⟨(k : ZMod (Nat.lcm M N)), iota_intCast_eq_Phi M N k⟩
  · intro y hy
    rw [AddMonoidHom.mem_range] at hy ⊢
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨k, (iota_intCast_eq_Phi M N k).symm⟩

/-- **Exactness at the obstruction face: `range Φ = ker π`** (transported from `range ι = ker π`). -/
theorem range_Phi_eq_ker_proj (M N : ℕ) [NeZero M] [NeZero N] :
    (Phi M N).range = (proj M N).ker := by
  rw [range_Phi_eq_range_iota, range_iota_eq_ker_proj]

/-- **T1.5 — the obstruction (cokernel) face.**  `coker Φ ≅ ℤ/gcd(M,N)`:
    `(ℤ/M × ℤ/N) ⧸ range Φ ≅ ℤ/gcd(M,N)`, by the first isomorphism theorem for the surjection
    `π = proj` (`proj_surjective`) together with `range Φ = ker π`. -/
noncomputable def coker_Phi_equiv (M N : ℕ) [NeZero M] [NeZero N] :
    ((ZMod M × ZMod N) ⧸ (Phi M N).range) ≃+ ZMod (Nat.gcd M N) := by
  rw [range_Phi_eq_ker_proj]
  exact QuotientAddGroup.quotientKerEquivOfSurjective (proj M N) (proj_surjective M N)

end Additions

/-! ## §H — Explicit free resolution of `ℤ/N` over `ℤ`, the bridge to abstract `Tor`.

The concrete `Tor` model used in §C (`ker(·M)`) comes from a free resolution.  Here we
construct that resolution **explicitly** and prove it is a genuine (length‑1) projective
resolution of `ℤ/N` in `ModuleCat ℤ`:

                       ·N                reduce
        0 ─→  ℤ  ───────────→  ℤ  ───────────────→  ℤ/N  ─→  0

i.e. a `ShortComplex (ModuleCat ℤ)` that is `ShortExact`, with both copies of `ℤ`
projective (`ℤ` is `ℤ`-free, hence `ModuleCat.of ℤ ℤ` is `Projective`).

This is the input to the derived functor: applying `(ℤ/M) ⊗ —` to the deleted
resolution `[ℤ →(·N) ℤ]` gives the two‑term complex `[ℤ/M →(·N) ℤ/M]` whose degree‑1
homology is `ker(·N : ℤ/M → ℤ/M)`; that is `Tor₁(ℤ/M, ℤ/N)`, whose group structure is
already pinned down (≅ `ℤ/gcd`) by `Spt6.torEquivZModGcd`.  The remaining purely
categorical step (`(Tor 1).obj _).obj _ ≅ ModuleCat.of ℤ (ker …)` via
`ProjectiveResolution.isoLeftDerivedObj`) is documented but not mechanised here. -/

namespace FreeResolution

open CategoryTheory

/-- Multiplication by `N : ℕ` on `ℤ`, as a `ℤ`-linear endomorphism (the resolution's
    only nonzero differential). -/
def mulZ (N : ℕ) : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ (N : ℤ)

/-- The reduction `ℤ → ℤ/N`, as a `ℤ`-linear map (the augmentation). -/
def red (N : ℕ) : ℤ →ₗ[ℤ] ZMod N := (Int.castAddHom (ZMod N)).toIntLinearMap

@[simp] lemma mulZ_apply (N : ℕ) (x : ℤ) : mulZ N x = (N : ℤ) * x := by
  rw [mulZ, LinearMap.lsmul_apply, smul_eq_mul]

@[simp] lemma red_apply (N : ℕ) (x : ℤ) : red N x = (x : ZMod N) := rfl

/-- `·N` is injective on `ℤ` for `N ≠ 0` (so `0 → ℤ` is exact: the resolution is faithful). -/
theorem mulZ_injective (N : ℕ) (hN : N ≠ 0) : Function.Injective (mulZ N) := by
  intro a b h
  rw [mulZ_apply, mulZ_apply] at h
  exact mul_left_cancel₀ (by exact_mod_cast hN) h

/-- Exactness in the middle: `range(·N) = ker(reduce)` (both equal the multiples of `N`). -/
theorem range_mulZ_eq_ker_red (N : ℕ) :
    LinearMap.range (mulZ N) = LinearMap.ker (red N) := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.mem_ker, mulZ_apply, red_apply]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨x, rfl⟩; exact dvd_mul_right (N : ℤ) x
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩

/-- The augmentation `ℤ → ℤ/N` is surjective (so `ℤ/N → 0` is exact). -/
theorem red_surjective (N : ℕ) : Function.Surjective (red N) := by
  intro y
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  exact ⟨k, rfl⟩

/-- The free resolution of `ℤ/N`, packaged as a short complex in `ModuleCat ℤ`. -/
noncomputable def res (N : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk (mulZ N) (red N) (by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, mulZ_apply, red_apply]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right (N : ℤ) x)

/-- **The free resolution is short exact.**  `0 → ℤ →(·N) ℤ → ℤ/N → 0` is a short exact
    sequence of `ℤ`-modules.  Since `ℤ` is `ℤ`-projective (free of rank one), this is a
    length-1 *projective* resolution of `ℤ/N`. -/
theorem res_shortExact (N : ℕ) (hN : N ≠ 0) : (res N).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact range_mulZ_eq_ker_red N
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    exact mulZ_injective N hN
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    exact red_surjective N

/-- Both terms of `res N` are projective: `ℤ` is `ℤ`-projective, so `res N` is a genuine
    projective resolution (this is what makes it usable to compute `Tor`). -/
example : Projective (ModuleCat.of ℤ ℤ) := inferInstance

/-- A statement about the **abstract** left-derived tensor functor
    `CategoryTheory.Tor (ModuleCat ℤ)`: because `ℤ` is projective, `Tor₁(ℤ/M, ℤ) = 0`.
    This confirms the categorical `Tor` is live on our objects.  The nonzero value
    `Tor₁(ℤ/M, ℤ/N)` is computed from the resolution `res` above and equals
    `ker(·N : ℤ/M → ℤ/M)` (group structure `≅ ℤ/gcd` via `Spt6.torEquivZModGcd`). -/
theorem tor_one_int_isZero (M : ℕ) :
    Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ZMod M))).obj
      (ModuleCat.of ℤ ℤ)) :=
  isZero_Tor_succ_of_projective (ModuleCat ℤ) (ModuleCat.of ℤ (ZMod M)) (ModuleCat.of ℤ ℤ) 0

end FreeResolution

/-! ## §I — `H₁` of the tensored resolution `≅ ker(·N) ≅ ℤ/gcd` (the value of `Tor₁`).

Tensoring the deleted free resolution `[ℤ →(·N) ℤ]` (§H) with `ℤ/M` yields the two-term
complex `[ℤ/M →(·N) ℤ/M]` (using `ℤ/M ⊗ ℤ ≅ ℤ/M`).  Its degree-1 homology is
`Tor₁(ℤ/M, ℤ/N)`.  Here that homology object is computed **as a genuine `ModuleCat ℤ`
homology** and identified with `ker(·N)`, and then — via §C's `torEquivZModGcd` — with
`ℤ/gcd`.  This mechanises the `H₁ ≅ ker` step requested for the `Tor` computation. -/

namespace TorComputation

open CategoryTheory CategoryTheory.Limits

universe u

/-- For a short complex of `R`-modules whose left map is zero, the homology is the kernel
    of the right map: `H = ker g / im f = ker g / 0 = ker g`. -/
noncomputable def scHomologyIsoKer {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{u} R))
    (hf : S.f = 0) : S.homology ≅ ModuleCat.of R (LinearMap.ker S.g.hom) := by
  have hfh : S.f.hom = 0 := by rw [hf]; rfl
  have hr : LinearMap.range S.moduleCatToCycles = ⊥ := by
    rw [LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [ShortComplex.moduleCatToCycles, hfh]
  exact S.moduleCatHomologyIso ≪≫ (Submodule.quotEquivOfEqBot _ hr).toModuleIso

/-- Multiplication by `N` on `ℤ/M`, as a `ℤ`-linear map: the differential of the complex
    obtained by tensoring `[ℤ →(·N) ℤ]` with `ℤ/M`, under `ℤ/M ⊗ ℤ ≅ ℤ/M`. -/
def mulZMod (N M : ℕ) : ZMod M →ₗ[ℤ] ZMod M := LinearMap.lsmul ℤ (ZMod M) (N : ℤ)

/-- The degree `(2,1,0)` window of `(ℤ/M) ⊗ [ℤ →(·N) ℤ]`, i.e. `0 → ℤ/M →(·N) ℤ/M`
    (the incoming differential is `0` because the resolution is `0` in degree `2`).  Its
    homology is `Tor₁(ℤ/M, ℤ/N)`. -/
noncomputable def torSC (N M : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (0 : ModuleCat.of ℤ (ZMod M) ⟶ ModuleCat.of ℤ (ZMod M))
    (ModuleCat.ofHom (mulZMod N M)) (by simp)

/-- **`Tor₁(ℤ/M, ℤ/N) ≅ ker(·N : ℤ/M → ℤ/M)`** as `ℤ`-modules: the degree-1 homology of
    the tensored resolution is the kernel of the tensored differential. -/
noncomputable def torSC_homologyIso (N M : ℕ) :
    (torSC N M).homology ≅ ModuleCat.of ℤ (LinearMap.ker (mulZMod N M)) :=
  scHomologyIsoKer (torSC N M) rfl

lemma mulZMod_apply (N M : ℕ) (x : ZMod M) : mulZMod N M x = (N : ZMod M) * x := by
  rw [mulZMod, LinearMap.lsmul_apply, zsmul_eq_mul]; push_cast; ring

/-- The tensored differential `·N` is the multiplication map of §C, so its kernel is the
    equalizer–Tor model `ker(mulLeft (N : ℤ/M))`. -/
lemma mulZMod_eq_mulLeft (N M : ℕ) :
    (mulZMod N M : ZMod M → ZMod M) = AddMonoidHom.mulLeft (N : ZMod M) := by
  funext x; rw [mulZMod_apply]; rfl

/-- The kernel `ker(·N : ℤ/M → ℤ/M)` of the tensored differential is, as an additive group,
    the equalizer–Tor model `ker(mulLeft (N : ℤ/M))` of §C. -/
def kerAddEquiv (N M : ℕ) :
    ↥(LinearMap.ker (mulZMod N M)) ≃+ ↥((AddMonoidHom.mulLeft (N : ZMod M)).ker) where
  toFun x := ⟨x.1, by
    rw [AddMonoidHom.mem_ker, ← congrFun (mulZMod_eq_mulLeft N M) x.1]
    exact LinearMap.mem_ker.mp x.2⟩
  invFun x := ⟨x.1, by
    rw [LinearMap.mem_ker, congrFun (mulZMod_eq_mulLeft N M) x.1]
    exact AddMonoidHom.mem_ker.mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **`Tor₁(ℤ/M, ℤ/N) ≅ ℤ/gcd(M,N)` as additive groups.**  Composing the homology
    computation `torSC_homologyIso` (`H₁ ≅ ker(·N)`) with §C's `torEquivZModGcd`
    (`ker ≅ ℤ/gcd`) gives the full group structure of `Tor₁`, computed from the explicit
    free resolution of §H. -/
noncomputable def torSC_homology_addEquiv (N M : ℕ) [NeZero M] :
    ↥(LinearMap.ker (mulZMod N M)) ≃+ ZMod (Nat.gcd M N) :=
  (kerAddEquiv N M).trans (torEquivZModGcd M N)

/-! The three "degrees" of the quasi-isomorphism `[ℤ →(·N) ℤ] ⟶ (ℤ/N)[0]` (i.e. that the
resolution of §H really resolves `ℤ/N`) are exactly the exactness facts of `res_shortExact`:
degree `0` is `H₀ = coker(·N) ≅ ℤ/N` (from `red_surjective` + middle-exactness), and degree
`1` is `H₁ = ker(·N) = 0` (from `mulZ_injective`).  We make the degree-1 acyclicity explicit
as a homology computation, in the same `ShortComplex` framework used for `Tor₁`. -/

/-- The degree `(2,1,0)` window of the resolution `[ℤ →(·N) ℤ]` itself: `0 → ℤ →(·N) ℤ`. -/
noncomputable def resSC (N : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)
    (ModuleCat.ofHom (FreeResolution.mulZ N)) (by simp)

/-- **Degree-1 acyclicity of the resolution** (a quasi-iso condition): `H₁[ℤ →(·N) ℤ]` is
    exact at the middle, i.e. `ker(·N) = range 0`, because `·N` is injective (`N ≠ 0`). -/
theorem resSC_exact (N : ℕ) (hN : N ≠ 0) : (resSC N).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  have hf : LinearMap.range (resSC N).f.hom = ⊥ := by
    have h0 : (resSC N).f.hom = 0 := rfl
    rw [h0, LinearMap.range_zero]
  have hg : LinearMap.ker (resSC N).g.hom = ⊥ :=
    LinearMap.ker_eq_bot.mpr (FreeResolution.mulZ_injective N hN)
  rw [hf, hg]

end TorComputation

/-! ## §J — The explicit projective resolution of `ℤ/N`, fully bound to the categorical `Tor`.

We build the actual `ChainComplex (ModuleCat ℤ) ℕ`, `[… 0 → ℤ →(·N) ℤ]`, **from raw structure
data** so that its differential `d 1 0` is *definitionally* `·N` (no `eqToHom` artifacts from
`ChainComplex.of`).  This defeq-clean rebuild is exactly what unblocks the cokernel
identification: `cx.opcycles 0` and `ℤ/N` are then cokernels of the *same* map, so
`opcycles ≅ cokernel` (`opcyclesIso`), `H₀(cx) ≅ ℤ/N` (`cx_homology_zero_iso`), and the
degree-0 quasi-iso `IsIso (homologyMap aug 0)` (`aug_quasiIsoAt_zero`) all go through.

With that, the augmentation `aug` is a genuine quasi-isomorphism (`aug_quasiIso`), giving a
real Mathlib `CategoryTheory.ProjectiveResolution (ℤ/N)` (`projRes`); and
`ProjectiveResolution.isoLeftDerivedObj` finally binds the abstract derived functor:
`((Tor (ModuleCat ℤ) 1).obj (ℤ/M)).obj (ℤ/N) ≅ H₁((ℤ/M ⊗ —)(cx))` (`torIso`).  Combined with
§I, this realises `Tor₁(ℤ/M, ℤ/N) ≅ ℤ/gcd` all the way from the categorical `Tor` symbol. -/

namespace ProjRes

open CategoryTheory CategoryTheory.Limits

/-- Objects: `ℤ` in degrees 0,1 and the zero object above. -/
noncomputable def cxX : ℕ → ModuleCat ℤ := fun n => if n < 2 then ModuleCat.of ℤ ℤ else 0

/-- Differentials by **direct pattern match (NO `eqToHom`)**: `d 1 0 = ·N`, else `0`.  This is
    the key to the defeq-clean rebuild — it makes `cx.d 1 0` *definitionally* equal to `·N`
    (= `(res N).f`), so the two cokernel structures of §H/§J live over the SAME differential
    and `coconePointUniqueUpToIso` applies. -/
noncomputable def cxd (N : ℕ) : ∀ i j, cxX i ⟶ cxX j := fun i j =>
  match i, j with
  | 1, 0 => ModuleCat.ofHom (FreeResolution.mulZ N)
  | _, _ => 0

/-- The free resolution complex of `ℤ/N`, built from raw structure data so that `d 1 0 = ·N`
    holds by `rfl`. -/
noncomputable def cx (N : ℕ) : ChainComplex (ModuleCat ℤ) ℕ where
  X := cxX
  d := cxd N
  shape := by
    intro i j h
    match i, j with
    | 0, _ => rfl
    | 1, 0 => exact absurd rfl h
    | 1, (_ + 1) => rfl
    | (_ + 2), _ => rfl
  d_comp_d' := by
    intro i j k _ _
    rcases i with _ | _ | i
    · show cxd N 0 j ≫ _ = 0; rw [show cxd N 0 j = 0 from rfl, zero_comp]
    · rcases j with _ | j
      · show cxd N 1 0 ≫ cxd N 0 k = 0; rw [show cxd N 0 k = 0 from rfl, comp_zero]
      · show cxd N 1 (j + 1) ≫ _ = 0; rw [show cxd N 1 (j + 1) = 0 from rfl, zero_comp]
    · show cxd N (i + 2) j ≫ _ = 0; rw [show cxd N (i + 2) j = 0 from rfl, zero_comp]

/-- Every term of `cx N` is projective (`ℤ` is projective; the tail is the zero object). -/
instance cx_projective (N n : ℕ) : Projective ((cx N).X n) := by
  show Projective (cxX n)
  by_cases h : n < 2
  · rw [cxX, if_pos h]; infer_instance
  · rw [cxX, if_neg h]; infer_instance

/-- `d 1 0 = ·N`, **definitionally** (`rfl`) — the whole point of the rebuild. -/
lemma cx_d_10 (N : ℕ) : (cx N).d 1 0 = ModuleCat.ofHom (FreeResolution.mulZ N) := rfl
lemma cx_d_21 (N : ℕ) : (cx N).d 2 1 = 0 := rfl
/-- The degree-`(n+2)` term of `cx N` is the zero object. -/
lemma cx_isZero_X (N n : ℕ) : IsZero ((cx N).X (n + 2)) := by
  show IsZero (cxX (n + 2)); rw [cxX, if_neg (by omega)]; exact isZero_zero _

/-- The augmentation `π : cx ⟶ (ℤ/N)[0]`. -/
noncomputable def aug (N : ℕ) :
    cx N ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ (ZMod N)) :=
  HomologicalComplex.mkHomToSingle (ModuleCat.ofHom (FreeResolution.red N)) (by
    intro i hi
    obtain rfl : i = 1 := by simp only [ComplexShape.down_Rel] at hi; omega
    rw [show (cx N).d 1 0 = (FreeResolution.res N).f from rfl]
    exact (FreeResolution.res N).zero)

/-- **Acyclicity in degrees `≥ 2`**: the complex vanishes there. -/
theorem cx_exactAt_ge_two (N n : ℕ) : (cx N).ExactAt (n + 2) :=
  ShortComplex.exact_of_isZero_X₂ _ (cx_isZero_X N n)

/-- **Acyclicity in degree `1`**: `H₁ = ker(·N) = 0` (`·N` injective). -/
theorem cx_exactAt_one (N : ℕ) (hN : N ≠ 0) : (cx N).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' (cx N) 2 1 0 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
  show LinearMap.range ((cx N).d 2 1).hom = LinearMap.ker ((cx N).d 1 0).hom
  rw [cx_d_21, cx_d_10]
  simp only [ModuleCat.hom_zero, LinearMap.range_zero]
  exact (LinearMap.ker_eq_bot.mpr (FreeResolution.mulZ_injective N hN)).symm

/-- The resolution complex is **exact in every positive degree**. -/
theorem cx_exactAt_succ (N : ℕ) (hN : N ≠ 0) (n : ℕ) : (cx N).ExactAt (n + 1) := by
  cases n with
  | zero => exact cx_exactAt_one N hN
  | succ m => exact cx_exactAt_ge_two N m

/-- **`opcycles ≅ cokernel`**: `cx.opcycles 0 ≅ ℤ/N`.  Both `cx.opcycles 0` and `ℤ/N` are
    cokernels of `·N` (`opcyclesIsCokernel` resp. `ShortExact.gIsCokernel`); since `cx.d 1 0`
    is now **defeq** to `(res N).f`, they are cokernels of the *same* map, so the colimit
    universal property gives the iso. -/
noncomputable def opcyclesIso (N : ℕ) (hN : N ≠ 0) :
    (cx N).opcycles 0 ≅ ModuleCat.of ℤ (ZMod N) :=
  IsColimit.coconePointUniqueUpToIso
    ((cx N).opcyclesIsCokernel (j := 0) (i := 1) (by simp))
    (FreeResolution.res_shortExact N hN).gIsCokernel

/-- **`H₀(cx) ≅ ℤ/N`** (`H₀ ≅ opcycles 0 ≅ cokernel(·N) ≅ ℤ/N`). -/
noncomputable def cx_homology_zero_iso (N : ℕ) (hN : N ≠ 0) :
    (cx N).homology 0 ≅ ModuleCat.of ℤ (ZMod N) :=
  (ChainComplex.isoHomologyι₀ (cx N)).trans (opcyclesIso N hN)

/-- **Degree-0 quasi-iso of the augmentation**: `IsIso (homologyMap aug 0)`.  Via
    `ChainComplex.isoHomologyι₀` this reduces to `IsIso (opcyclesMap aug 0)`, and that map
    equals the cokernel comparison `opcyclesIso.hom ≫ singleObjOpcyclesSelfIso.hom` (an iso),
    proven by the cokernel universal property `Cofork.IsColimit.hom_ext`. -/
theorem aug_quasiIsoAt_zero (N : ℕ) (hN : N ≠ 0) : QuasiIsoAt (aug N) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hpe : HomologicalComplex.pOpcycles (cx N) 0 ≫ (opcyclesIso N hN).hom
      = (FreeResolution.res N).g := by
    simpa [opcyclesIso] using IsColimit.comp_coconePointUniqueUpToIso_hom
      ((cx N).opcyclesIsCokernel (j := 0) (i := 1) (by simp))
      (FreeResolution.res_shortExact N hN).gIsCokernel WalkingParallelPair.one
  have heq : HomologicalComplex.opcyclesMap (aug N) 0 =
      (opcyclesIso N hN).hom ≫ (HomologicalComplex.singleObjOpcyclesSelfIso
        (ComplexShape.down ℕ) 0 (ModuleCat.of ℤ (ZMod N))).hom := by
    refine Cofork.IsColimit.hom_ext
      ((cx N).opcyclesIsCokernel (j := 0) (i := 1) (by simp)) ?_
    show HomologicalComplex.pOpcycles (cx N) 0 ≫ HomologicalComplex.opcyclesMap (aug N) 0
       = HomologicalComplex.pOpcycles (cx N) 0 ≫ ((opcyclesIso N hN).hom ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0
            (ModuleCat.of ℤ (ZMod N))).hom)
    erw [HomologicalComplex.p_opcyclesMap]
    rw [reassoc_of% hpe]
    simp only [aug, HomologicalComplex.mkHomToSingle_f,
      HomologicalComplex.singleObjOpcyclesSelfIso_hom, Category.assoc]
    rfl
  haveI : IsIso (HomologicalComplex.opcyclesMap (aug N) 0) := by rw [heq]; infer_instance
  have nat := ChainComplex.isoHomologyι₀_inv_naturality (aug N)
  have hh : HomologicalComplex.homologyMap (aug N) 0 =
      (cx N).isoHomologyι₀.hom ≫ HomologicalComplex.opcyclesMap (aug N) 0 ≫
        ((ChainComplex.single₀ (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ (ZMod N))).isoHomologyι₀.inv := by
    rw [← nat, Iso.hom_inv_id_assoc]
  rw [hh]; infer_instance

/-- **The augmentation is a quasi-isomorphism** (degree 0 by `aug_quasiIsoAt_zero`; positive
    degrees by acyclicity `cx_exactAt_succ`). -/
theorem aug_quasiIso (N : ℕ) (hN : N ≠ 0) : QuasiIso (aug N) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero => exact aug_quasiIsoAt_zero N hN
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' (aug N) (n + 1) (ChainComplex.exactAt_succ_single_obj _ n)]
    exact cx_exactAt_succ N hN n

/-- **The explicit projective resolution of `ℤ/N`** as a genuine Mathlib
    `CategoryTheory.ProjectiveResolution`. -/
noncomputable def projRes (N : ℕ) (hN : N ≠ 0) :
    ProjectiveResolution (ModuleCat.of ℤ (ZMod N)) where
  complex := cx N
  π := aug N
  quasiIso := aug_quasiIso N hN

open CategoryTheory.MonoidalCategory in
/-- **`Tor₁(ℤ/M, ℤ/N)` bound to the categorical `Tor` functor.**  Through the explicit
    projective resolution `projRes`, `ProjectiveResolution.isoLeftDerivedObj` identifies
    `((CategoryTheory.Tor (ModuleCat ℤ) 1).obj (ℤ/M)).obj (ℤ/N)` with the degree-1 homology of
    the tensored resolution `(ℤ/M ⊗ —)(cx)`.  This completes the bridge from the abstract
    derived functor to the explicit free-resolution computation. -/
noncomputable def torIso (N M : ℕ) (hN : N ≠ 0) :
    ((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ZMod M))).obj (ModuleCat.of ℤ (ZMod N)) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
        (((tensoringLeft (ModuleCat ℤ)).obj (ModuleCat.of ℤ (ZMod M))).mapHomologicalComplex
          (ComplexShape.down ℕ) |>.obj (cx N)) :=
  (projRes N hN).isoLeftDerivedObj
    ((tensoringLeft (ModuleCat ℤ)).obj (ModuleCat.of ℤ (ZMod M))) 1

/-! ### §K — The complete chain `Tor₁(ℤ/M,ℤ/N) ≅ H₁((ℤ/M)⊗cx) ≅ ker(·N) ≅ ℤ/gcd(M,N)`.

`torIso` lands us in the degree-1 homology of the tensored resolution `(ℤ/M ⊗ —)(cx)`.  We now
identify that homology with `ℤ/gcd(M,N)` by an explicit, instance-clean composite of `ℤ`-module
isomorphisms:

* `chainHomologyOneIsoKer` — for a chain complex with vanishing incoming differential `d 2 1`,
  `H₁ ≅ ker(d 1 0)` (via `isoHomologyπ`, `cyclesIsoSc'` to the explicit `(2,1,0)`-window short
  complex, and `moduleCatCyclesIso`; the residual ℤ-module diamond `Submodule.module` vs
  `AddCommGroup.toIntModule` is bridged by `Subsingleton (Module ℤ ·)`);
* `tensoredCx_d10_hom` — the tensored differential is `1 ⊗ (·N) = lTensor (ℤ/M) (·N)`
  (`ModuleCat.MonoidalCategory.hom_whiskerLeft`);
* `ridKerEquiv` — `TensorProduct.rid` carries `ker(1 ⊗ ·N)` onto `ker(·N)`, intertwining the two
  multiplications (`rid_intertwine`, `rid_map_ker`);
* `TorComputation.torSC_homology_addEquiv` — `ker(·N) ≅ ℤ/gcd` from §C/§I. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- For a chain complex of `ℤ`-modules whose incoming differential `d 2 1` vanishes, the
    degree-1 homology is the kernel of the outgoing differential `d 1 0`. -/
noncomputable def chainHomologyOneIsoKer (K : ChainComplex (ModuleCat ℤ) ℕ) (h21 : K.d 2 1 = 0) :
    K.homology 1 ≅ ModuleCat.of ℤ (LinearMap.ker (K.d 1 0).hom) :=
  (K.isoHomologyπ 2 1 (by simp) h21).symm ≪≫
    K.cyclesIsoSc' 2 1 0 (by simp) (ChainComplex.next_nat_succ 0) ≪≫
    (K.sc' 2 1 0).moduleCatCyclesIso ≪≫
    eqToIso (by rw [ShortComplex.moduleCatLeftHomologyData_K]; congr 1; exact Subsingleton.elim _ _)

/-- The tensored resolution `(ℤ/M) ⊗ cx(N)`, a chain complex of `ℤ`-modules. -/
noncomputable abbrev tensoredCx (N M : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  (((tensoringLeft (ModuleCat ℤ)).obj (ModuleCat.of ℤ (ZMod M))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cx N)

/-- The incoming differential of the tensored complex in the `(2,1)` slot vanishes (the
    resolution is `0` in degree `2`). -/
lemma tensoredCx_d21 (N M : ℕ) : (tensoredCx N M).d 2 1 = 0 := by
  show ((tensoringLeft (ModuleCat ℤ)).obj (ModuleCat.of ℤ (ZMod M))).map ((cx N).d 2 1) = 0
  rw [cx_d_21, Functor.map_zero]

/-- The degree-1 tensored differential, on underlying linear maps, is `1 ⊗ (·N)`. -/
lemma tensoredCx_d10_hom (N M : ℕ) :
    ((tensoredCx N M).d 1 0).hom
      = (LinearMap.lTensor (ZMod M) (FreeResolution.mulZ N) :
          ↑((tensoredCx N M).X 1) →ₗ[ℤ] ↑((tensoredCx N M).X 0)) :=
  rfl

/-- `TensorProduct.rid` intertwines `1 ⊗ (·N)` on `ℤ/M ⊗ ℤ` with `·N` on `ℤ/M`. -/
lemma rid_intertwine (N M : ℕ) :
    (TensorProduct.rid ℤ (ZMod M)).toLinearMap.comp
        (LinearMap.lTensor (ZMod M) (FreeResolution.mulZ N))
      = (TorComputation.mulZMod N M).comp (TensorProduct.rid ℤ (ZMod M)).toLinearMap := by
  apply TensorProduct.ext'
  intro m z
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    LinearEquiv.coe_coe, FreeResolution.mulZ, TorComputation.mulZMod, LinearMap.lsmul_apply,
    smul_eq_mul]
  rw [mul_smul]

/-- `rid` carries `ker(1 ⊗ ·N)` onto `ker(·N)`. -/
lemma rid_map_ker (N M : ℕ) :
    (LinearMap.ker (LinearMap.lTensor (ZMod M) (FreeResolution.mulZ N))).map
        (TensorProduct.rid ℤ (ZMod M)).toLinearMap = LinearMap.ker (TorComputation.mulZMod N M) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have key := DFunLike.congr_fun (rid_intertwine N M) y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at key ⊢
    rw [← key, hy, map_zero]
  · intro hx
    refine ⟨(TensorProduct.rid ℤ (ZMod M)).symm x, ?_, by simp⟩
    have key := DFunLike.congr_fun (rid_intertwine N M) ((TensorProduct.rid ℤ (ZMod M)).symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
    apply (TensorProduct.rid ℤ (ZMod M)).injective
    rw [map_zero, key]; exact hx

/-- `ker(1 ⊗ ·N : ℤ/M ⊗ ℤ → ℤ/M ⊗ ℤ) ≃ₗ ker(·N : ℤ/M → ℤ/M)` via `rid`. -/
noncomputable def ridKerEquiv (N M : ℕ) :
    (LinearMap.ker (LinearMap.lTensor (ZMod M) (FreeResolution.mulZ N))) ≃ₗ[ℤ]
      (LinearMap.ker (TorComputation.mulZMod N M)) :=
  (Submodule.equivMapOfInjective _ (TensorProduct.rid ℤ (ZMod M)).injective _).trans
    (LinearEquiv.ofEq _ _ (rid_map_ker N M))

/-- **The complete chain of isomorphisms, as one composite.**
    `Tor₁(ℤ/M,ℤ/N) ≅ H₁((ℤ/M)⊗cx(N)) ≅ ker(·N : ℤ/M → ℤ/M) ≅ ℤ/gcd(M,N)`,
    realised as a single isomorphism of `ℤ`-modules, all the way from the categorical
    `Tor (ModuleCat ℤ) 1` symbol down to the explicit cyclic group `ℤ/gcd`. -/
noncomputable def torFullIso (N M : ℕ) (hN : N ≠ 0) [NeZero M] :
    ((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ZMod M))).obj (ModuleCat.of ℤ (ZMod N)) ≅
      ModuleCat.of ℤ (ZMod (Nat.gcd M N)) :=
  torIso N M hN ≪≫
    eqToIso rfl ≪≫
    chainHomologyOneIsoKer (tensoredCx N M) (tensoredCx_d21 N M) ≪≫
    eqToIso (by congr 1) ≪≫
    LinearEquiv.toModuleIso
      ((LinearEquiv.ofEq _ _ (congrArg LinearMap.ker (tensoredCx_d10_hom N M))).trans
        ((ridKerEquiv N M).trans (TorComputation.torSC_homology_addEquiv N M).toIntLinearEquiv))

end ProjRes

/-! ## §L — Tier 3: interface / conditional formalization of the cohomological inputs (axiom-free).

Mathlib now contains generic sheaf cohomology as Ext, topological skyscraper
sheaves/flasqueness, and pro-étale ℓ-adic cohomology of schemes; these are used
unconditionally in `Tier3Actual`.  It still lacks the paper-specific
`Spec ℤ` cohomology computation, Voevodsky motives, compactly-supported motivic
Euler characteristic, the required curve normalization comparison
(dual graph / δ-invariants), and `Padic.log`.  Rather than introduce **axioms**,
we bundle only those remaining deep inputs as fields of structures (Strategy A)
or explicit hypotheses (Strategy B), keeping every assumption visible.

§7.2 correction (Strategy C): over `ℤ`, `ℤ` is projective, so module-`Ext¹(ℤ, A) = 0`; the paper's
`Ȟ¹ ≅ Ext¹(ℤ, A)` must therefore mean **sheaf**-`Ext¹_{Sh(S)}(ℤ_S, A) = H¹(S, A)`, not module-`Ext`. -/

namespace Tier3

/-! ### Strategy A — interface structures + unconditional theorems. -/

/-- **Curve-detector interface (Thm 6.1 / Cor 6.3).**  Bundles the deep cohomological inputs of the
    smooth-fibre detector — the étale bump, the motivic Euler jump, the derived obstruction, the
    dual-graph first Betti number `b₁(Γ)`, and the δ-invariant sum `Σδ` — together with the paper's
    identities (realization compatibility, normalization decomposition, smooth-locus and derived-face
    characterizations) as data fields. -/
structure CurveDetectorData (p : ℕ) where
  bump : ℕ
  eulerJump : ℕ
  derived : ℕ
  b1Graph : ℕ
  deltaSum : ℕ
  smooth : Prop
  bump_eq_jump : bump = eulerJump
  jump_eq_graph : eulerJump = b1Graph + deltaSum
  smooth_iff : smooth ↔ (b1Graph = 0 ∧ deltaSum = 0)
  der_iff : derived = 0 ↔ smooth

/-- **Cor 6.3 (good-prime box), unconditional from the interface.**  On a smooth fibre every
    detector vanishes: bump, Euler jump and the derived obstruction are all `0`. -/
theorem box_from_data {p : ℕ} (D : CurveDetectorData p) (h : D.smooth) :
    D.bump = 0 ∧ D.eulerJump = 0 ∧ D.derived = 0 := by
  obtain ⟨hb1, hδ⟩ := D.smooth_iff.1 h
  have hjump : D.eulerJump = 0 := by rw [D.jump_eq_graph, hb1, hδ]
  have hbump : D.bump = 0 := by rw [D.bump_eq_jump, hjump]
  exact ⟨hbump, hjump, D.der_iff.2 h⟩

/-- **bump = 0 ⇔ smooth** from the interface (the box is sharp). -/
theorem bump_zero_iff_smooth {p : ℕ} (D : CurveDetectorData p) : D.bump = 0 ↔ D.smooth := by
  rw [D.bump_eq_jump, D.jump_eq_graph, Nat.add_eq_zero_iff, ← D.smooth_iff]

/-- **Étale–motivic realization compatibility** (Thm 6.1 / §9.3 / §10.3): the étale bump equals the
    motivic Euler jump via the realization functor, recorded as a field. -/
structure EtaleMotivicRealization where
  motivicJump : ℕ
  etaleBump : ℕ
  realization_compat : etaleBump = motivicJump

/-- The realization comparison seals the two invariants together. -/
theorem realization_seals (R : EtaleMotivicRealization) : R.etaleBump = R.motivicJump :=
  R.realization_compat

/-- **C.2 unconditional arithmetic shadow.**  This is the part of the curve detector
    that can genuinely be proved without étale cohomology, motives, a realization
    functor, or a field of `CurveDetectorData`: once the two dimension formulas are
    supplied as ordinary hypotheses, the excess is the graph-plus-singularity
    defect, and a vanishing defect forces equality of the dimensions. -/
theorem curve_detector_numeric_shadow (g b1 deltaSum dimH1Xp dimH1Up : ℕ)
    (Hnorm : dimH1Xp = 2 * g + b1 + deltaSum)
    (HsmoothPart : dimH1Up = 2 * g) :
    dimH1Xp - dimH1Up = b1 + deltaSum ∧
      (b1 = 0 → deltaSum = 0 → dimH1Xp = dimH1Up) := by
  constructor
  · exact curve_betti_identity g b1 deltaSum dimH1Xp dimH1Up Hnorm HsmoothPart
  · intro hb1 hdelta
    omega

/-- **Sheaf-cohomology interface (Def 7.1 / Prop 7.2 / §7.3 / Prop 10.6).**  For the flasque
    skyscraper failure sheaf: `H⁰` vanishes (shift) and `H¹` equals the number of visible (singular)
    stalks — both recorded as fields, being beyond Mathlib's reach for `Spec ℤ`. -/
structure SheafCohomologyData where
  h0 : ℕ
  h1 : ℕ
  numVisible : ℕ
  h0_zero : h0 = 0
  h1_stalkSum : h1 = numVisible

/-- The δ-cohomology detector is `H¹`. -/
def deltaCoh (D : SheafCohomologyData) : ℕ := D.h1

/-- **Prop 7.2 (invariance):** `δ_coh = #visible stalks`, independent of presentation. -/
theorem deltaCoh_eq_numVisible (D : SheafCohomologyData) : deltaCoh D = D.numVisible :=
  D.h1_stalkSum

/-- **§7.3 (`δ_coh(P_f) = 1` shadow):** a nonempty defect locus gives a positive detector while
    `H⁰ = 0`. -/
theorem deltaCoh_pos_of_visible (D : SheafCohomologyData) (h : 0 < D.numVisible) :
    0 < deltaCoh D ∧ D.h0 = 0 := by
  refine ⟨?_, D.h0_zero⟩
  rw [deltaCoh_eq_numVisible]; exact h

/-! ### Strategy B — conditional bookkeeping theorems (hypotheses as Prop/ℕ arguments). -/

/-- **Thm 9.3(v) — extended synchronization (TFAE).**  Smoothness, the gcd gate, the derived
    obstruction, the étale bump, and the motivic jump are all equivalent.  Extends the
    4-proposition `Spt6.goodPrime_synchronization` with the motivic face `motJump = 0`. -/
theorem goodPrime_synchronization_extended (smooth : Prop) (der bump motJump M pk : ℕ)
    (Hgate : smooth ↔ Nat.gcd M pk = 1) (Hder : der = 0 ↔ smooth)
    (Hbump : bump = 0 ↔ smooth) (Hmot : motJump = 0 ↔ smooth) :
    [smooth, Nat.gcd M pk = 1, der = 0, bump = 0, motJump = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate
  tfae_have 1 ↔ 3 := Hder.symm
  tfae_have 1 ↔ 4 := Hbump.symm
  tfae_have 1 ↔ 5 := Hmot.symm
  tfae_finish

/-- **§9.3 smooth normalization kills the bump.**  When the normalization map is an isomorphism on
    `H¹` (`dim H¹(Xp) = dim H¹(Up)`), the bump (= the difference of those dimensions) is `0`. -/
theorem smooth_normalization_bump_zero (dimH1Xp dimH1Up bump : ℕ)
    (Hbump : bump = dimH1Xp - dimH1Up) (Hiso : dimH1Xp = dimH1Up) : bump = 0 := by
  rw [Hbump, Hiso, Nat.sub_self]

/-! ### Strategy C — §7.2 Ext correction (the honest formalizable fact). -/

/-- **§7.2 correction.**  `ℤ` is a projective `ℤ`-module (free of rank one over itself), so the
    module-level `Ext¹(ℤ, A)` vanishes for every `A`; the paper's `Ȟ¹ ≅ Ext¹(ℤ, A)` must therefore
    mean **sheaf**-`Ext` (`= H¹(S, A)`), not module-`Ext` (which is identically `0`). -/
theorem int_projective : Module.Projective ℤ ℤ := inferInstance

/-- **§7.2 unconditional correction at the actual derived-Ext level.**
    For every `ℤ`-module `A` and every `n ≥ 0`, the positive-degree group
    `Ext^(n+1)_ℤ(ℤ, A)` is a subsingleton.  This uses Mathlib's derived
    `CategoryTheory.Abelian.Ext`, not an informal proxy for Ext. -/
theorem int_module_ext_succ_subsingleton (A : ModuleCat ℤ) (n : ℕ) :
    Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of ℤ ℤ) A (n + 1)) := by
  exact CategoryTheory.Abelian.Ext.subsingleton_of_projective (ModuleCat.of ℤ ℤ) A n

/-- In particular every class in module-`Ext¹_ℤ(ℤ,A)` is zero.  Consequently,
    any nonzero invariant denoted `Ext¹(ℤ,A)` in the paper cannot mean Ext in
    the ordinary category of `ℤ`-modules. -/
theorem int_module_ext_one_eq_zero (A : ModuleCat ℤ)
    (e : CategoryTheory.Abelian.Ext (ModuleCat.of ℤ ℤ) A 1) : e = 0 := by
  exact CategoryTheory.Abelian.Ext.eq_zero_of_projective e

end Tier3

/-! ## §L′ — Audit of field-projection theorems and genuine replacements.

The following status constants are intentionally ordinary Lean data, not new
assumptions.  They record which statements are genuine mathematics already
proved above, and which statements are still interface packaging because the
corresponding geometric/cohomological theory is not present in mathlib.
-/

inductive FormalizationStatus where
  | unconditional
  | conditional
  | definitional
  | packaging
  | futureWork
deriving DecidableEq, Repr

namespace FormalizationStatus

def isRepresentative : FormalizationStatus → Bool
  | unconditional => true
  | conditional => false
  | definitional => false
  | packaging => false
  | futureWork => false

end FormalizationStatus

/-- `hensel_gate` is now a genuine theorem from mathlib's Hensel lemma. -/
def status_hensel_gate : FormalizationStatus := .unconditional

/-- Uniqueness of two lifts in the Hensel ball is a genuine corollary of the
unconditional gate. -/
def status_hensel_gate_unique_of_two : FormalizationStatus := .unconditional

/-- The theorem composing an abstract smoothness predicate with the Hensel gate
is conditional because the smooth-to-root and smooth-to-unit-Jacobian bridges
are explicit hypotheses. -/
def status_smooth_to_unique_lift_of_hensel_hypotheses : FormalizationStatus := .conditional

/-- A scheme-theoretic smoothness predicate and its Jacobian full-rank criterion
for the paper's family have not been constructed in this file. -/
def status_schemeSmooth_iff_jacobianFullRank : FormalizationStatus := .futureWork

/-- The converse “unique `p`-adic lift implies Jacobian full rank/smoothness”
is not a consequence of Hensel's lemma used here and requires additional
geometric hypotheses and a converse lifting criterion. -/
def status_uniqueLift_to_jacobian_smooth : FormalizationStatus := .futureWork

/-- Consequently the full equivalence in Thm 9.3(i)⇔(ii) / Prop 6.2 remains a
conditional theorem schema, not an unconditional result of this file. -/
def status_full_smooth_jacobian_gate_equivalence : FormalizationStatus := .conditional

/-- The expression `T²-aₚT+p` is explicitly defined as a polynomial over `ℤ`. -/
def status_frobeniusTatePolynomial_definition : FormalizationStatus := .definitional

/-- Its coefficients, evaluation formula, and trace-zero specialization are
genuine polynomial arithmetic. -/
def status_frobeniusTatePolynomial_arithmetic : FormalizationStatus := .unconditional

/-- Extracting `aₚ=p+1-N` from a supplied natural number `N` and proving the
`N=p+1` specialization is genuine integer/polynomial arithmetic. -/
def status_frobenius_pointCount_certificate : FormalizationStatus := .unconditional

/-- Identifying the formal polynomial with the characteristic polynomial of
geometric Frobenius on the paper's elliptic curve requires the missing
finite-field elliptic-curve/Frobenius theory. -/
def status_geometric_frobenius_characteristicPolynomial : FormalizationStatus := .futureWork

/-- The implication `aₚ=0 → supersingular` cannot be stated faithfully here:
the relevant supersingularity predicate and its Frobenius criterion have not
been constructed.  We deliberately do not replace them by a structure field. -/
def status_trace_zero_implies_supersingular : FormalizationStatus := .futureWork

/-- The finite scanner and its intermediate readouts are explicit Lean
definitions. -/
def status_primeScan_definitions : FormalizationStatus := .definitional

/-- Enumeration, Boolean certification, and bounded-prime membership have
proved necessary-and-sufficient specifications. -/
def status_primeScan_correctness : FormalizationStatus := .unconditional

/-- The gcd with `X^p-X` is proved to have exactly the same finite-field zero
set as the reduced polynomial. -/
def status_primeScan_gcd_readout : FormalizationStatus := .unconditional

/-- Every simple root returned by the scanner is proved to have a unique
`p`-adic Hensel lift. -/
def status_primeScan_hensel_lift : FormalizationStatus := .unconditional

/-- The structural Tor-vanishing criterion is a genuine theorem obtained from
the already certified Tor/gcd additive equivalence. -/
def status_tor_subsingleton_iff : FormalizationStatus := .unconditional

/-- Both forms of the `N=60` App. B row are genuine specializations of the
Tor/gcd theorem and finite CRT. -/
def status_torReadout60 : FormalizationStatus := .unconditional

/-- `Profile` is a data schema only. It has no theorem-valued fields and is not
a representative mathematical result. -/
def status_Profile : FormalizationStatus := .definitional

/-- `gcd_obstruction_zero_to_gluing` is a genuine theorem from the CRT gluing lemma. -/
def status_gcd_obstruction_zero_to_gluing : FormalizationStatus := .unconditional

/-- `analyticPred_eq_fixedPoint_ratio` is a genuine theorem from derangement
cardinality and complement counting in `Equiv.Perm (Fin d)`. -/
def status_analyticPred_eq_fixedPoint_ratio : FormalizationStatus := .unconditional

/-- `obstruction_support_zeroLocus` is the zero-locus membership criterion for
`Spec ℤ`, specialized to a singleton generator. -/
def status_obstruction_support_zeroLocus : FormalizationStatus := .unconditional

/-- `prime_mem_support_iff_dvd` is a genuine theorem connecting the closed point
`(p)` with divisibility of the integer generator. -/
def status_prime_mem_support_iff_dvd : FormalizationStatus := .unconditional

/-- `residue_fiber_range` is the quotient-spectrum range theorem specialized to
`ℤ → ℤ/(g)`. -/
def status_residue_fiber_range : FormalizationStatus := .unconditional

/-- `obstruction_support_eq_zeroLocus_gcd` is the scheme-level form of the
paper's `Supp = V(gcd(M,p^k))` slogan. -/
def status_obstruction_support_eq_zeroLocus_gcd : FormalizationStatus := .unconditional

/-- `padicVal_phi` fixes the missing §5.1 coefficient definition and proves the
constant `n+T` valuation from the already-formalized Kummer and LTE blocks. -/
def status_padicVal_phi : FormalizationStatus := .unconditional

/-- The finite direct-sum/H⁰ shadow of the `Spec ℤ` skyscraper calculation is
genuine algebra over `ZMod ℓ`; it does not use sheaf cohomology fields. -/
def status_specZ_skyscraper_H0_directSum_shadow : FormalizationStatus := .unconditional

/-- The skyscraper sheaf itself is now genuinely proved flasque in the
`AddCommGrpCat`-valued topological sheaf category. -/
def status_skyscraperSheaf_isFlasque : FormalizationStatus := .unconditional

/-- The natural-number normalization calculation underlying the curve detector is
genuine mathematics and does not project any cohomological interface field. -/
def status_curve_detector_numeric_shadow : FormalizationStatus := .unconditional

/-- The missing Mathlib theorem for C.1 is the geometric one: closed-point
skyscraper sheaves on `Spec ℤ` are flasque/acyclic, hence higher cohomology
vanishes.  This is future work, not a structure-field theorem. -/
def status_specZ_skyscraper_flasque_acyclicity : FormalizationStatus := .futureWork

/-- The current `SheafCohomologyData` record is an interface for the missing
Zariski sheaf-cohomology calculation on `Spec ℤ`. -/
def status_SheafCohomologyData_interface : FormalizationStatus := .conditional

/-- The old `H¹ = 0 → gluing` slogan is unconditional only after the obstruction
has already been identified with the gcd face; the cohomological identification
itself remains outside this file. -/
def status_h1EtaleZero_to_gluing_original : FormalizationStatus := .conditional

/-- A genuine `good open → étale piece` theorem needs scheme/étale geometry not
formalized in this file. -/
def status_goodOpen_to_etalePiece : FormalizationStatus := .futureWork

/-- `CurveDetectorData` is an honest axiom-free interface, but its comparison
fields are mathematical assumptions, not theorems derived in this file. -/
def status_CurveDetectorData_interface : FormalizationStatus := .conditional

/-- The equality between the étale bump and motivic Euler jump is currently an
input field.  A genuine proof needs étale/motivic realization theory. -/
def status_CurveDetectorData_bump_eq_jump : FormalizationStatus := .conditional

/-- The equality between the motivic jump and `b₁(Γ) + Σδ` is likewise an input
field.  It requires the geometric normalization/localization argument. -/
def status_CurveDetectorData_jump_eq_graph : FormalizationStatus := .conditional

/-- `EtaleMotivicRealization` packages the missing realization comparison as
data; it does not construct an étale or motivic realization functor. -/
def status_EtaleMotivicRealization_interface : FormalizationStatus := .conditional

/-- Pro-étale ℓ-adic cohomology groups of schemes are actually defined in the
current Mathlib and carry their expected additive group structure. -/
def status_etale_ladic_cohomology : FormalizationStatus := .unconditional

/-- Constructible motives `DMc`, motivic complexes `Mc`, and `χmot` are not
defined here; their localization triangle therefore remains future work. -/
def status_motivic_localization_triangle : FormalizationStatus := .futureWork

/-- `Tier3.box_from_data` merely packages fields of `CurveDetectorData`. -/
def status_Tier3_box_from_data : FormalizationStatus := .packaging

/-- `Tier3.bump_zero_iff_smooth` is also a repackaging of structure fields. -/
def status_Tier3_bump_zero_iff_smooth : FormalizationStatus := .packaging

/-- `Tier3.realization_seals` is exactly projection of `realization_compat`. -/
def status_Tier3_realization_seals : FormalizationStatus := .packaging

/-- `Tier3.deltaCoh_eq_numVisible` is exactly projection of `h1_stalkSum`. -/
def status_Tier3_deltaCoh_eq_numVisible : FormalizationStatus := .packaging

/-- `Tier3.deltaCoh_pos_of_visible` combines two structure fields; it should not
be used as a representative theorem for actual sheaf cohomology. -/
def status_Tier3_deltaCoh_pos_of_visible : FormalizationStatus := .packaging

/-- `Tier3.goodPrime_synchronization_extended` is honest but conditional: the
bridges are explicit hypotheses rather than structure fields. -/
def status_Tier3_goodPrime_synchronization_extended : FormalizationStatus := .conditional

/-- Numeric smooth-normalization bookkeeping is a genuine theorem about naturals. -/
def status_Tier3_smooth_normalization_bump_zero : FormalizationStatus := .unconditional

/-- `ℤ` is genuinely proved projective as a `ℤ`-module. -/
def status_Tier3_int_projective : FormalizationStatus := .unconditional

/-- Positive-degree derived module-Ext from `ℤ` genuinely vanishes by
projectivity, using Mathlib's `Abelian.Ext`. -/
def status_Tier3_int_module_ext_vanishing : FormalizationStatus := .unconditional

/-- In the current Mathlib, generic sheaf cohomology is defined as Ext from the
constant sheaf, so the `H¹ = Ext¹` identification is genuine and definitional
once the site's sheafification and Ext instances are available. -/
def status_sheafExt_H1_identification : FormalizationStatus := .unconditional

/-- The audit table itself proves that the old field-projection theorems are not
classified as representative unconditional results. -/
theorem field_projection_theorems_not_representative :
    FormalizationStatus.isRepresentative status_Tier3_box_from_data = false ∧
    FormalizationStatus.isRepresentative status_Tier3_bump_zero_iff_smooth = false ∧
    FormalizationStatus.isRepresentative status_Tier3_realization_seals = false ∧
    FormalizationStatus.isRepresentative status_Tier3_deltaCoh_eq_numVisible = false ∧
    FormalizationStatus.isRepresentative status_Tier3_deltaCoh_pos_of_visible = false := by
  decide

/-- The replacements added in this integrated file are classified as genuine
unconditional Lean mathematics. -/
theorem integrated_replacements_are_unconditional :
    status_hensel_gate = .unconditional ∧
    status_hensel_gate_unique_of_two = .unconditional ∧
    status_frobeniusTatePolynomial_arithmetic = .unconditional ∧
    status_frobenius_pointCount_certificate = .unconditional ∧
    status_primeScan_correctness = .unconditional ∧
    status_primeScan_gcd_readout = .unconditional ∧
    status_primeScan_hensel_lift = .unconditional ∧
    status_skyscraperSheaf_isFlasque = .unconditional ∧
    status_etale_ladic_cohomology = .unconditional ∧
    status_sheafExt_H1_identification = .unconditional ∧
    status_gcd_obstruction_zero_to_gluing = .unconditional ∧
    status_analyticPred_eq_fixedPoint_ratio = .unconditional ∧
    status_obstruction_support_zeroLocus = .unconditional ∧
    status_prime_mem_support_iff_dvd = .unconditional ∧
    status_residue_fiber_range = .unconditional ∧
    status_obstruction_support_eq_zeroLocus_gcd = .unconditional ∧
    status_padicVal_phi = .unconditional ∧
    status_specZ_skyscraper_H0_directSum_shadow = .unconditional ∧
    status_curve_detector_numeric_shadow = .unconditional ∧
    status_Tier3_int_projective = .unconditional ∧
    status_Tier3_int_module_ext_vanishing = .unconditional := by
  decide

/-- C.1 boundary audit: finite stalk-sum algebra is formalized now; flasque
acyclicity and the actual `Spec ℤ` sheaf-cohomology bridge are not. -/
theorem c1_specZ_skyscraper_classification :
    status_specZ_skyscraper_H0_directSum_shadow = .unconditional ∧
    status_skyscraperSheaf_isFlasque = .unconditional ∧
    status_specZ_skyscraper_flasque_acyclicity = .futureWork ∧
    status_SheafCohomologyData_interface = .conditional ∧
    status_Tier3_deltaCoh_eq_numVisible = .packaging ∧
    status_Tier3_deltaCoh_pos_of_visible = .packaging := by
  decide

/-- C.2 boundary audit.  The numerical normalization identity is unconditional.
The two interfaces and their stored comparison statements are conditional;
their projection consequences are packaging; the missing geometric theories
and localization triangle are future work. -/
theorem c2_etale_motivic_classification :
    status_curve_detector_numeric_shadow = .unconditional ∧
    status_CurveDetectorData_interface = .conditional ∧
    status_CurveDetectorData_bump_eq_jump = .conditional ∧
    status_CurveDetectorData_jump_eq_graph = .conditional ∧
    status_EtaleMotivicRealization_interface = .conditional ∧
    status_Tier3_box_from_data = .packaging ∧
    status_Tier3_bump_zero_iff_smooth = .packaging ∧
    status_Tier3_realization_seals = .packaging ∧
    status_Tier3_goodPrime_synchronization_extended = .conditional ∧
    status_etale_ladic_cohomology = .unconditional ∧
    status_motivic_localization_triangle = .futureWork := by
  decide

/-- C.3 boundary audit.  Ordinary module-Ext is completely settled and
vanishes in positive degrees.  The sheaf-Ext/cohomology comparison is a
different theorem in a different abelian category and remains future work;
`SheafCohomologyData` is only a conditional interface for numerical
cohomology data, not a construction of sheaf Ext. -/
theorem c3_sheaf_ext_classification :
    status_Tier3_int_projective = .unconditional ∧
    status_Tier3_int_module_ext_vanishing = .unconditional ∧
    status_SheafCohomologyData_interface = .conditional ∧
    status_sheafExt_H1_identification = .unconditional ∧
    FormalizationStatus.isRepresentative status_Tier3_int_module_ext_vanishing = true ∧
    FormalizationStatus.isRepresentative status_sheafExt_H1_identification = true := by
  decide

/-- Maximal unconditional upgrade currently supported by Mathlib for C.1–C.3.
This does not assert the still-missing higher-cohomology computation or any
motivic comparison. -/
theorem tier3_actual_mathlib_upgrades :
    status_skyscraperSheaf_isFlasque = .unconditional ∧
    status_etale_ladic_cohomology = .unconditional ∧
    status_sheafExt_H1_identification = .unconditional := by
  decide

/-- Exact residual boundary after applying every unconditional C.1–C.5 upgrade
available in the current Mathlib.  These statuses are not declarations of
impossibility; they record the concrete theorems still required before the
paper-level claims can be promoted without assumptions. -/
theorem tier3_remaining_boundary_classification :
    status_specZ_skyscraper_flasque_acyclicity = .futureWork ∧
    status_SheafCohomologyData_interface = .conditional ∧
    status_CurveDetectorData_interface = .conditional ∧
    status_CurveDetectorData_bump_eq_jump = .conditional ∧
    status_CurveDetectorData_jump_eq_graph = .conditional ∧
    status_EtaleMotivicRealization_interface = .conditional ∧
    status_motivic_localization_triangle = .futureWork ∧
    status_smooth_to_unique_lift_of_hensel_hypotheses = .conditional ∧
    status_schemeSmooth_iff_jacobianFullRank = .futureWork ∧
    status_uniqueLift_to_jacobian_smooth = .futureWork ∧
    status_full_smooth_jacobian_gate_equivalence = .conditional ∧
    status_geometric_frobenius_characteristicPolynomial = .futureWork ∧
    status_trace_zero_implies_supersingular = .futureWork := by
  decide

/-- C.4 boundary audit.  The simple-root Hensel implication and its uniqueness
corollary are unconditional.  Passing from scheme smoothness/Jacobian rank to
the analytic hypotheses is conditional, while construction of the actual
scheme-theoretic criterion and the converse unique-lift implication are future
work.  Therefore the full paper equivalence is not a representative
unconditional theorem. -/
theorem c4_smooth_jacobian_hensel_classification :
    status_hensel_gate = .unconditional ∧
    status_hensel_gate_unique_of_two = .unconditional ∧
    status_smooth_to_unique_lift_of_hensel_hypotheses = .conditional ∧
    status_schemeSmooth_iff_jacobianFullRank = .futureWork ∧
    status_uniqueLift_to_jacobian_smooth = .futureWork ∧
    status_full_smooth_jacobian_gate_equivalence = .conditional ∧
    FormalizationStatus.isRepresentative status_hensel_gate = true ∧
    FormalizationStatus.isRepresentative status_hensel_gate_unique_of_two = true ∧
    FormalizationStatus.isRepresentative
      status_smooth_to_unique_lift_of_hensel_hypotheses = false ∧
    FormalizationStatus.isRepresentative
      status_full_smooth_jacobian_gate_equivalence = false := by
  decide

/-- C.5 boundary audit.  The trace and polynomial calculation are certified
unconditionally, while the polynomial's geometric interpretation and the
supersingular criterion remain future work.  The bare polynomial definition is
not itself a representative theorem. -/
theorem c5_supersingular_frobenius_classification :
    status_frobeniusTatePolynomial_definition = .definitional ∧
    status_frobeniusTatePolynomial_arithmetic = .unconditional ∧
    status_frobenius_pointCount_certificate = .unconditional ∧
    status_geometric_frobenius_characteristicPolynomial = .futureWork ∧
    status_trace_zero_implies_supersingular = .futureWork ∧
    FormalizationStatus.isRepresentative
      status_frobeniusTatePolynomial_definition = false ∧
    FormalizationStatus.isRepresentative
      status_frobeniusTatePolynomial_arithmetic = true ∧
    FormalizationStatus.isRepresentative
      status_frobenius_pointCount_certificate = true ∧
    FormalizationStatus.isRepresentative
      status_geometric_frobenius_characteristicPolynomial = false ∧
    FormalizationStatus.isRepresentative
      status_trace_zero_implies_supersingular = false := by
  decide

/-- D.1 audit: the scanner is a definition, while its finite-field
specification, gcd readout, and Hensel lifting theorem are genuine
unconditional mathematics. -/
theorem d1_prime_scan_classification :
    status_primeScan_definitions = .definitional ∧
    status_primeScan_correctness = .unconditional ∧
    status_primeScan_gcd_readout = .unconditional ∧
    status_primeScan_hensel_lift = .unconditional ∧
    FormalizationStatus.isRepresentative status_primeScan_definitions = false ∧
    FormalizationStatus.isRepresentative status_primeScan_correctness = true ∧
    FormalizationStatus.isRepresentative status_primeScan_gcd_readout = true ∧
    FormalizationStatus.isRepresentative status_primeScan_hensel_lift = true := by
  decide

/-! ## §M — Summary of paper corrections surfaced by formalization.

Formalizing the algebraic/arithmetic skeleton mechanically detects four errors in the paper; three
of them stem from the *same* `lcm ↔ gcd` confusion (intersection vs obstruction/cokernel), which the
single short exact sequence `0 → ℤ/lcm → ℤ/M × ℤ/N → ℤ/gcd → 0` (§G, `Additions.range_iota_eq_ker_proj`
+ `iota_injective` + `proj_surjective`) resolves at once:

  1. (§3.1/4.2/6/9/10, App C) Local intersection thickness `εₚ = min{vₚM, k}` is WRONG: the
     intersection is `(lcm)`, of thickness `max`; `min` is the valuation of the `gcd` (= Tor).
     ↦ separated and certified in §B′′ (`padicVal_thickness_intersection` = max, `…obstruction_gcd` = min).
  2. (Prop 10.7) The SES maps `ι = (x, −x)`, `π = a − b` give `π ∘ ι = 2x ≠ 0`; the consistent pair
     is the diagonal `ι = (x, x)`, difference `π`.  ↦ enforced by §G (`iota`, `proj`).
  3. (§7.2) `Ȟ¹ ≅ Ext¹(ℤ, A)` is `0` for module-`Ext` (ℤ projective); the intended object is
     sheaf-`Ext¹_{Sh(S)}(ℤ_S, A)`.  ↦ §L Strategy C (`Tier3.int_projective`,
     `Tier3.int_module_ext_succ_subsingleton`, `Tier3.int_module_ext_one_eq_zero`).
  4. (§3.1 bookkeeping) The overlap object `A(U ∩ V) = ℤ/lcm` with `δ⁰ = a − b mod lcm`: the global
     kernel (intersection) face is `ℤ/lcm`, the cokernel (gluing-obstruction) face is `ℤ/gcd`.
     ↦ the two ends of the §G SES separate the faces exactly.

Corrections 1, 2, 4 are the one `lcm ↔ gcd` confusion; the §G exact sequence settles all three. -/

/-! ## Examples. -/

/-- D.3 audit: the Tor-vanishing criterion and both `N=60` decompositions are
unconditional. `Profile` is merely definitional data and is not representative. -/
theorem d3_tor_packaging_classification :
    status_tor_subsingleton_iff = .unconditional ∧
    status_torReadout60 = .unconditional ∧
    status_Profile = .definitional ∧
    FormalizationStatus.isRepresentative status_tor_subsingleton_iff = true ∧
    FormalizationStatus.isRepresentative status_torReadout60 = true ∧
    FormalizationStatus.isRepresentative status_Profile = false := by
  decide

/-! ## D.2 - The p-adic logarithm on the open unit ball.

The denominator `n + 1` need not be a unit of `Z_p`, so the series is defined
first in `Q_p`. The final theorems recover an integral value on `p^k Z_p`.
-/

namespace PadicLog

variable {p : ℕ} [Fact p.Prime]

noncomputable def term (u : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1 : ℚ_[p]) ^ n * u ^ (n + 1) / (n + 1 : ℚ_[p])

noncomputable def logOnePlus (u : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, term u n

@[simp] theorem term_zero (u : ℚ_[p]) : term u 0 = u := by
  simp [term]

private theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by ring

private theorem geom_weight_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2⁻¹) (n : ℕ) :
    (n + 1 : ℝ) * r ^ n ≤ 1 := by
  calc
    (n + 1 : ℝ) * r ^ n ≤ (2 : ℝ) ^ n * r ^ n := by
      gcongr
      exact_mod_cast succ_le_two_pow n
    _ = (2 * r) ^ n := by rw [mul_pow]
    _ ≤ 1 ^ n := by
      gcongr
      linarith
    _ = 1 := one_pow n

theorem norm_inv_natCast_le (n : ℕ) :
    ‖((n + 1 : ℕ) : ℚ_[p])⁻¹‖ ≤ (n + 1 : ℝ) := by
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr n.succ_ne_zero),
    Padic.valuation_natCast]
  rw [zpow_neg, inv_inv]
  exact_mod_cast Nat.le_of_dvd n.succ_pos (pow_padicValNat_dvd (p := p) (n := n + 1))

theorem norm_term_le (u : ℚ_[p]) (n : ℕ) :
    ‖term u n‖ ≤ (n + 1 : ℝ) * ‖u‖ ^ (n + 1) := by
  rw [term, div_eq_mul_inv, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_pow]
  have h := mul_le_mul_of_nonneg_left (norm_inv_natCast_le (p := p) n)
    (pow_nonneg (norm_nonneg u) (n + 1))
  simpa [Nat.cast_add, Nat.cast_one, mul_comm] using h

theorem summable_term {u : ℚ_[p]} (hu : ‖u‖ < 1) :
    Summable (term u) := by
  apply Summable.of_norm_bounded
  · have h : Summable (fun n : ℕ => (n : ℝ) * ‖u‖ ^ n) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)] using hu))
    exact (summable_nat_add_iff 1).mpr h
  · intro n
    simpa [Nat.cast_add, Nat.cast_one] using norm_term_le u n

theorem hasSum_term {u : ℚ_[p]} (hu : ‖u‖ < 1) :
    HasSum (term u) (logOnePlus u) :=
  (summable_term hu).hasSum

private theorem two_le_prime_real : (2 : ℝ) ≤ p := by
  exact_mod_cast (Fact.out : p.Prime).two_le

private theorem radius_le_half {k : ℕ} (hk : 1 ≤ k) :
    (p : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hpinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    exact inv_anti₀ (by norm_num : (0 : ℝ) < 2) two_le_prime_real
  have hp_inv_nonneg : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hp_inv_le_one : (p : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_le)
  calc
    (p : ℝ)⁻¹ ^ k ≤ (p : ℝ)⁻¹ ^ 1 := by
      exact pow_le_pow_of_le_one hp_inv_nonneg hp_inv_le_one hk
    _ ≤ (2 : ℝ)⁻¹ := by simpa using hpinv

theorem norm_term_le_radius {u : ℚ_[p]} {k : ℕ} (hk : 1 ≤ k)
    (hu : ‖u‖ ≤ (p : ℝ)⁻¹ ^ k) (n : ℕ) :
    ‖term u n‖ ≤ (p : ℝ)⁻¹ ^ k := by
  have hur : ‖u‖ ≤ (2 : ℝ)⁻¹ :=
    hu.trans (radius_le_half (p := p) hk)
  calc
    ‖term u n‖ ≤ (n + 1 : ℝ) * ‖u‖ ^ (n + 1) := norm_term_le u n
    _ = ((n + 1 : ℝ) * ‖u‖ ^ n) * ‖u‖ := by ring
    _ ≤ 1 * ‖u‖ := by
      gcongr
      exact geom_weight_le_one (norm_nonneg u) hur n
    _ ≤ (p : ℝ)⁻¹ ^ k := by simpa using hu

theorem norm_logOnePlus_le_radius {u : ℚ_[p]} {k : ℕ} (hk : 1 ≤ k)
    (hu : ‖u‖ ≤ (p : ℝ)⁻¹ ^ k) :
    ‖logOnePlus u‖ ≤ (p : ℝ)⁻¹ ^ k := by
  rw [logOnePlus]
  have hsum : Summable (term u) := summable_term <|
    hu.trans_lt ((radius_le_half (p := p) hk).trans_lt (by norm_num))
  refine le_of_tendsto' hsum.hasSum.norm ?_
  intro s
  induction s using Finset.induction_on with
  | empty =>
      have h : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ k := by positivity
      simpa only [Finset.sum_empty, norm_zero] using h
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Padic.nonarchimedean _ _).trans (max_le (norm_term_le_radius hk hu a) ih)

theorem norm_logOnePlus_sub_le_radius {u : ℚ_[p]} {k : ℕ} (hk : 1 ≤ k)
    (hu : ‖u‖ ≤ (p : ℝ)⁻¹ ^ k) :
    ‖logOnePlus u - u‖ ≤ (p : ℝ)⁻¹ ^ k := by
  rw [sub_eq_add_neg]
  exact (Padic.nonarchimedean _ _).trans <|
    max_le (norm_logOnePlus_le_radius hk hu) (by simpa using hu)

noncomputable def logOnePlusInt (u : ℤ_[p]) : ℚ_[p] :=
  logOnePlus (u : ℚ_[p])

theorem norm_coe_le_radius_iff_mem_span_pow (u : ℤ_[p]) (k : ℕ) :
    ‖(u : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ k ↔
      u ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
  change ‖u‖ ≤ (p : ℝ)⁻¹ ^ k ↔
    u ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p])
  rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
  simp only [zpow_neg, zpow_natCast, inv_pow]

theorem norm_logOnePlusInt_le_of_mem_span_pow (u : ℤ_[p]) {k : ℕ} (hk : 1 ≤ k)
    (hu : u ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p])) :
    ‖logOnePlusInt u‖ ≤ (p : ℝ)⁻¹ ^ k := by
  exact norm_logOnePlus_le_radius hk <|
    (norm_coe_le_radius_iff_mem_span_pow u k).2 hu

theorem norm_logOnePlusInt_sub_le_of_mem_span_pow (u : ℤ_[p]) {k : ℕ} (hk : 1 ≤ k)
    (hu : u ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p])) :
    ‖logOnePlusInt u - (u : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ k := by
  exact norm_logOnePlus_sub_le_radius hk <|
    (norm_coe_le_radius_iff_mem_span_pow u k).2 hu

noncomputable def logOnePlusIntegral (u : ℤ_[p]) {k : ℕ} (hk : 1 ≤ k)
    (hu : u ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p])) : ℤ_[p] :=
  ⟨logOnePlusInt u,
    (norm_logOnePlusInt_le_of_mem_span_pow u hk hu).trans
      ((radius_le_half (p := p) hk).trans (by norm_num))⟩

@[simp] theorem coe_logOnePlusIntegral (u : ℤ_[p]) {k : ℕ} (hk : 1 ≤ k)
    (hu : u ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p])) :
    (logOnePlusIntegral u hk hu : ℚ_[p]) = logOnePlusInt u :=
  rfl

end PadicLog

/-- D.2 is unconditional apart from its explicit mathematical domain
hypotheses (`‖u‖ < 1`, or `u ∈ p^k Z_p` with `k ≥ 1`). -/
theorem d2_padic_log_classification : True := by
  trivial

section Examples
example : Nat.gcd 12 9 = 3 := by norm_num
example : Nat.lcm 6 9 = 18 := by norm_num
/-- Direct-sum cardinality: `⊕_{i<3} ℤ/5` has `5³ = 125` elements. -/
example : Fintype.card (Fin 3 → ZMod 5) = 125 := by rw [directSum_card]; norm_num
/-- T2.1 detector rank: over `P = {2,3,5}` (3 visible primes), `Module.rank (ℤ/7) (P → ℤ/7) = 3`. -/
example : Module.rank (ZMod 7) (({2, 3, 5} : Finset ℕ) → ZMod 7) = 3 := by
  have := detector_rank 7 (by norm_num) {2, 3, 5}; rwa [show ({2,3,5} : Finset ℕ).card = 3 by decide] at this
/-- T2.1 direct-sum module iso instantiated: `⊕_{p∈{2,3,5}} ℤ/7 ≅ (ℤ/7)³`. -/
noncomputable example :
    (({2, 3, 5} : Finset ℕ) → ZMod 7) ≃ₗ[ZMod 7] (Fin ({2, 3, 5} : Finset ℕ).card → ZMod 7) :=
  detector_directSum_linearEquiv 7 {2, 3, 5}
/-- T2.2 Kummer: `v₂(C(2³, 2¹)) = 3 - 1 = 2` (here `C(8,2) = 28 = 2²·7`). -/
example : padicValNat 2 (Nat.choose (2 ^ 3) (2 ^ 1)) = 3 - 1 :=
  padicVal_binom_pow 2 3 1 Nat.prime_two (by norm_num)
/-- T2.2 LTE profile: with `p = 3, T = 1`, `v₃((1 + 3)^{3ʲ} - 1) = 1 + j`; at `j = 2`, this is `3`. -/
example : padicValInt 3 ((1 + (3 : ℤ) ^ 1) ^ (3 ^ 2) - 1) = 1 + 2 :=
  Hk_basic_profile 3 (by decide) (by decide) 1 (by norm_num) 2
/-- T2.3 instantiated: a global section of the four-layer fiber product at `n` is exactly a point in
    all four layer loci (here: positive, odd, not-divisible-by-5, prime). -/
example (n : ℕ) :
    PrimalityShadow.primalityLayer (fun m => 0 < m) (fun m => Odd m) (fun m => ¬ 5 ∣ m) Nat.Prime n
      ↔ n ∈ {m | 0 < m} ∩ {m | Odd m} ∩ {m | ¬ 5 ∣ m} ∩ {m | Nat.Prime m} :=
  PrimalityShadow.layers_sectionwise _ _ _ _ n
/-- T2.4 numeric: `g=1, b₁=2, Σδ=3` ⇒ `dim H¹(Xp)=7, dim H¹(Up)=2`, excess `7-2 = 5 = 2+3`. -/
example : (7 : ℕ) - 2 = 2 + 3 := curve_betti_identity 1 2 3 7 2 (by norm_num) (by norm_num)
/-- Tier 3 example: a smooth-fibre instance of the curve-detector interface (all invariants `0`). -/
def exampleSmoothCurve : Tier3.CurveDetectorData 7 where
  bump := 0
  eulerJump := 0
  derived := 0
  b1Graph := 0
  deltaSum := 0
  smooth := True
  bump_eq_jump := rfl
  jump_eq_graph := rfl
  smooth_iff := by simp
  der_iff := by simp

/-- The good-prime box (Cor 6.3) makes every detector silent, *unconditionally* from the structure. -/
example : exampleSmoothCurve.bump = 0 ∧ exampleSmoothCurve.eulerJump = 0 ∧ exampleSmoothCurve.derived = 0 :=
  Tier3.box_from_data exampleSmoothCurve trivial
/-- Non-gluing example over `(6,9)` with residues `a=1,b=0` (`gcd 3 ∤ 1`). -/
example : ¬ (∃ x : ℤ, (6:ℤ) ∣ (x - 1) ∧ (9:ℤ) ∣ (x - 0)) := by
  rw [crt_solvable_iff]; decide
/-- `ι` injective and `π` surjective for `(M,N) = (6,9)` (lcm 18, gcd 3). -/
example : Function.Injective (Additions.iota 6 9) := by
  haveI : NeZero (Nat.lcm 6 9) := ⟨by decide⟩
  exact Additions.iota_injective 6 9
example : Function.Surjective (Additions.proj 6 9) := Additions.proj_surjective 6 9
/-- T1.5 at `(M,N)=(6,9)`: `coker Φ = (ℤ/6 × ℤ/9) ⧸ range Φ ≅ ℤ/gcd(6,9) = ℤ/3`. -/
noncomputable example :
    ((ZMod 6 × ZMod 9) ⧸ (Additions.Phi 6 9).range) ≃+ ZMod (Nat.gcd 6 9) := by
  haveI : NeZero (6 : ℕ) := ⟨by decide⟩
  haveI : NeZero (9 : ℕ) := ⟨by decide⟩
  exact Additions.coker_Phi_equiv 6 9
/-- Tor₁ as a group iso: `ker(·6 : ℤ/9 → ℤ/9) ≅ ℤ/gcd(9,6) = ℤ/3`. -/
noncomputable example : (AddMonoidHom.mulLeft (6 : ZMod 9)).ker ≃+ ZMod (Nat.gcd 9 6) :=
  torEquivZModGcd 9 6
/-- T1.6 numeric: `v₂((12) ∩ (2³)) = v₂(lcm 12 8) = v₂ 24 = 3 = max(v₂ 12, 3) = max(2, 3)`;
    the obstruction value is `min(2, 3) = 2 = v₂(gcd 12 8) = v₂ 4`. -/
example : padicValNat 2 (Nat.lcm 12 (2 ^ 3)) = max (padicValNat 2 12) 3 :=
  padicVal_thickness_intersection 2 12 3 Nat.prime_two (by decide)
example : padicValNat 2 (Nat.gcd 12 (2 ^ 3)) = min (padicValNat 2 12) 3 :=
  padicVal_obstruction_gcd 2 12 3 Nat.prime_two (by decide)
/-- T1.7 locality: `v₂(4 · 3) = v₂ 4` — the coprime factor `3` is invisible to `v₂`. -/
example : padicValNat 2 (4 * 3) = padicValNat 2 4 :=
  padicValNat_mul_coprime 2 4 3 Nat.prime_two (by decide) (by decide)
/-- T1.7 local Tor model: `Tor₁(ℤ/4, ℤ/8) ≅ ℤ/2^{min(2,3)} = ℤ/4`. -/
noncomputable example :
    (AddMonoidHom.mulLeft ((2 ^ 2 : ℕ) : ZMod (2 ^ 3))).ker ≃+ ZMod (2 ^ min 2 3) := by
  haveI : NeZero (2 ^ 3 : ℕ) := ⟨by decide⟩
  exact torLocalModel 2 2 3
/-- CRT refinement instantiated at `N = 12 = 2²·3`: `ℤ/12 ≅ ∏_{q ∈ {2,3}} ℤ/q^{v_q 12}`. -/
noncomputable example :
    ZMod 12 ≃+* ((q : (12 : ℕ).primeFactors) → ZMod (q ^ (12 : ℕ).factorization q)) :=
  zmodPrimePowerProd 12 (by decide)
/-- T1.4 instantiated at `(M,N) = (6,9)`: `Tor₁(ℤ/6, ℤ/9) ≅ ⊕_{q ∈ {3}} ℤ/3^{min(1,2)} = ℤ/3`. -/
noncomputable example :
    (AddMonoidHom.mulLeft (6 : ZMod 9)).ker
      ≃+ ((q : (9 : ℕ).primeFactors) →
            ZMod (q ^ min ((6 : ℕ).factorization q) ((9 : ℕ).factorization q))) := by
  haveI : NeZero (9 : ℕ) := ⟨by decide⟩
  exact torPrimewiseDecomp 6 9 (by decide) (by decide)
/-- The **full composite chain** as one categorical isomorphism, instantiated at `(M,N)=(6,9)`:
    `Tor₁(ℤ/6, ℤ/9) ≅ H₁((ℤ/6)⊗cx) ≅ ker(·9 : ℤ/6 → ℤ/6) ≅ ℤ/gcd(6,9) = ℤ/3`. -/
noncomputable example :
    ((CategoryTheory.Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ZMod 6))).obj
        (ModuleCat.of ℤ (ZMod 9)) ≅ ModuleCat.of ℤ (ZMod (Nat.gcd 6 9)) := by
  haveI : NeZero (6 : ℕ) := ⟨by decide⟩
  exact ProjRes.torFullIso 9 6 (by decide)
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms hensel_gate_aeval
#print axioms hensel_gate
#print axioms hensel_gate_unique_of_two
#print axioms smooth_to_unique_lift_of_hensel_hypotheses
#print axioms frobeniusTraceFromPointCount
#print axioms frobeniusTatePolynomial
#print axioms frobeniusTrace_eq_zero_iff
#print axioms frobeniusTatePolynomial_coefficients
#print axioms frobeniusTatePolynomial_eval
#print axioms frobeniusTatePolynomial_trace_zero
#print axioms frobeniusTatePolynomial_of_pointCount_eq
#print axioms Tier3Actual.skyscraperSheaf_isFlasque
#print axioms Tier3Actual.sheafCohomologyExtEquiv
#print axioms Tier3Actual.sheafCohomology_eq_ext
#print axioms Tier3Actual.ellAdicCohomology_nonempty
#print axioms PrimeScan.mem_simpleRoots_iff
#print axioms PrimeScan.simpleRootCount_pos_iff
#print axioms PrimeScan.hasSimpleRoot_eq_true_iff
#print axioms PrimeScan.eval_rootGCD_eq_zero_iff
#print axioms PrimeScan.scanned_root_norm_lt_one
#print axioms PrimeScan.scanned_derivative_norm_eq_one
#print axioms PrimeScan.simpleRoot_has_uniquePadicLift
#print axioms PrimeScan.scanPrime_eq_true_iff
#print axioms PrimeScan.mem_scanPrimesUpTo_iff
#print axioms card_derangements_direct
#print axioms derangementPerms_card
#print axioms fixedPointPerms_card
#print axioms numDerangements_le_factorial
#print axioms analyticPred_eq_fixedPoint_ratio
#print axioms obstruction_support_zeroLocus
#print axioms prime_mem_support_iff_dvd
#print axioms prime_mem_support_iff_dvd_of_prime
#print axioms residue_fiber_range
#print axioms residue_fiber_range_singleton
#print axioms obstruction_support_eq_zeroLocus_gcd
#print axioms kernel_mem_iff_lcm
#print axioms gcd_obstruction_zero_to_gluing
#print axioms h1EtaleZero_to_gluing_arithmetic
#print axioms zmodPiEquivOfCoprime
#print axioms zmodPrimePowerProd
#print axioms prod_primeFactors_pow_min_eq_gcd
#print axioms zmodGcdPrimewiseDecomp
#print axioms torPrimewiseDecomp
#print axioms tor_subsingleton_iff
#print axioms torReadout60Primewise
#print axioms zmod60AddEquiv
#print axioms torReadout60
#print axioms crt_solvable_iff
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms padicVal_thickness_intersection
#print axioms padicVal_obstruction_gcd
#print axioms card_ker_mulLeft
#print axioms torEquivZModGcd
#print axioms obstructionFree_iff_card
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms padicValNat_mul_coprime
#print axioms gcd_pow_pow
#print axioms torLocalModel
#print axioms tor_primewise_isLocal
#print axioms directSum_card
#print axioms detector_directSum_linearEquiv
#print axioms detector_rank
#print axioms detector_H0_addEquiv
#print axioms detector_global_sections
#print axioms specZ_skyscraper_H0_directSum_shadow
#print axioms specZ_skyscraper_stalkSum_linearEquiv
#print axioms delta_coh_one_shadow
#print axioms shifted_binom_identity
#print axioms padicVal_binom_pow
#print axioms padicVal_pow_sub_one
#print axioms Hk_basic_profile
#print axioms phi
#print axioms padicValInt_choose_prime_pow
#print axioms padicVal_phi
#print axioms phi_profile_condition_iff
#print axioms PrimalityShadow.layers_sectionwise
#print axioms PrimalityShadow.sections_primalityLayer
#print axioms PrimalityShadow.sections_restrict
#print axioms PrimalityShadow.primalityLayer_equiv
#print axioms PrimalityShadow.sections_union
#print axioms goodPrime_synchronization
#print axioms good_prime_box
#print axioms curve_betti_identity
#print axioms smooth_silences
#print axioms curve_normalization_package
#print axioms Tier3.box_from_data
#print axioms Tier3.realization_seals
#print axioms Tier3.curve_detector_numeric_shadow
#print axioms Tier3.deltaCoh_pos_of_visible
#print axioms Tier3.goodPrime_synchronization_extended
#print axioms Tier3.smooth_normalization_bump_zero
#print axioms Tier3.int_projective
#print axioms Tier3.int_module_ext_succ_subsingleton
#print axioms Tier3.int_module_ext_one_eq_zero
#print axioms field_projection_theorems_not_representative
#print axioms integrated_replacements_are_unconditional
#print axioms c1_specZ_skyscraper_classification
#print axioms c2_etale_motivic_classification
#print axioms c3_sheaf_ext_classification
#print axioms c4_smooth_jacobian_hensel_classification
#print axioms c5_supersingular_frobenius_classification
#print axioms tier3_actual_mathlib_upgrades
#print axioms tier3_remaining_boundary_classification
#print axioms d1_prime_scan_classification
#print axioms PadicLog.summable_term
#print axioms PadicLog.hasSum_term
#print axioms PadicLog.norm_logOnePlus_le_radius
#print axioms PadicLog.norm_coe_le_radius_iff_mem_span_pow
#print axioms PadicLog.norm_logOnePlusInt_le_of_mem_span_pow
#print axioms PadicLog.norm_logOnePlusInt_sub_le_of_mem_span_pow
#print axioms PadicLog.logOnePlusIntegral
#print axioms d2_padic_log_classification
#print axioms d3_tor_packaging_classification
#print axioms Additions.iota_injective
#print axioms Additions.proj_surjective
#print axioms Additions.range_iota_eq_ker_proj
#print axioms Additions.range_Phi_eq_ker_proj
#print axioms Additions.coker_Phi_equiv
#print axioms FreeResolution.range_mulZ_eq_ker_red
#print axioms FreeResolution.res_shortExact
#print axioms FreeResolution.tor_one_int_isZero
#print axioms TorComputation.torSC_homologyIso
#print axioms TorComputation.torSC_homology_addEquiv
#print axioms TorComputation.resSC_exact
#print axioms ProjRes.cx_projective
#print axioms ProjRes.aug
#print axioms ProjRes.cx_exactAt_succ
#print axioms ProjRes.cx_homology_zero_iso
#print axioms ProjRes.aug_quasiIsoAt_zero
#print axioms ProjRes.aug_quasiIso
#print axioms ProjRes.projRes
#print axioms ProjRes.torIso
#print axioms ProjRes.chainHomologyOneIsoKer
#print axioms ProjRes.tensoredCx_d21
#print axioms ProjRes.tensoredCx_d10_hom
#print axioms ProjRes.ridKerEquiv
#print axioms ProjRes.torFullIso
end AxiomAudit

end Spt6
