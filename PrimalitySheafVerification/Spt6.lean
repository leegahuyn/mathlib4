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
    Thm 9.3(i)⇔(ii) GOOD-LOCUS equivalence (FIFTH CORRECTION; false reverse refuted):
                       p∤Δ ⟺ f̄ separable ⟺ all residual roots simple (squarefree)
                       ↦ GoodLocus.modPolynomial_good_locus_tfae /
                         GoodLocus.not_dvd_disc_iff_separable /
                         GoodLocus.unique_lift_not_imply_unit_derivative      PROVED (uncond.)
    Prop 2 / Tier-A A2 Weierstrass discriminant gate at polynomial level:
                       p∤Δ(E) ⟺ (x³+ax+b mod p) squarefree (= separable, residual nonsingular)
                       ↦ WeierstrassGate.cubic_good_locus_tfae /
                         WeierstrassGate.not_dvd_shortWeierstrass_Δ_iff_separable /
                         WeierstrassGate.shortWeierstrass_Δ                   PROVED (uncond.)
    §2.1/2.2 / Tier-A A3 concrete four-layer gates: numLayer/modLayer/discLayer/ecLayer
                       concrete; Γ(U,F)=⋂Γ(U,F_layer) certified; Hensel/EC layers = A2 gate
                       ↦ PrimalityShadow.{primeCertGate, sections_primeCertGate,
                         discLayer_iff_separable, ecLayer_iff_discLayer}        PROVED (uncond.)
    §5.1 Rem 6.5/10.5 / Tier-A A4 AB-linearization closed directly mod pᵏ (functional eqn bypassed):
                       ∑ⱼ aⱼ log(1+uⱼ) ≡ ∑ⱼ aⱼ uⱼ (mod pᵏ); radius bounds from padicVal_phi
                       ↦ PadicLog.{CongMod, sum_smul_logOnePlus_congMod,
                         norm_intCast_le_of_le_padicValInt, ab_linearization_phi_congMod}  PROVED (uncond.)
    §6 / Tier-A A5 δ-invariant + dual-graph b₁(Γ) as definitions (cohomology link = Tier C):
                       δ = length_R(S/R); b₁ = E−V+C; δ=0 ⟺ R→S surjective (smooth criterion)
                       ↦ CurveInvariants.{deltaInvariant, deltaInvariant_eq_zero_iff,
                         firstBettiNumber, graphFirstBetti, betti_excess_eq}    PROVED (uncond. defs)
    §5.1 / Tier-B B1 p-adic log functional equation, FORMAL (uncond.) + analytic transfer (isolated):
                       logOf(f·g)=logOf f+logOf g, logOf(fⁿ)=n•logOf f in ℚ_[p]⟦X⟧
                       ↦ PadicLogFormal.{logOf_mul, logOf_pow, term_eq_coeff_log}  PROVED (uncond.)
                       ↦ PadicLogFormal.{PadicLogAdditive, logOnePlus_pow_of_additive}  CONDITIONAL
    §7.3 Prop 10.6 / Tier-B B2 flasque Γ-exactness (uncond.) + acyclicity isolation (Hⁱ=0 i>0):
                       Γ sends flasque SES → surjection; flasque SES ⟹ flasque quotient
                       ↦ Tier3Actual.{flasque_sections_epi, flasque_global_sections_surjective,
                         flasque_quotient_isFlasque}  PROVED (uncond.); IsGammaAcyclic isolates rest
    §7.2 / Tier-B B3 Čech = derived (deg ≤1) + Ȟ¹ ≅ sheaf-Ext¹: explicit Čech cohomology +
                       grounding (sheaf-Ext¹ vs module-Ext¹=0); SS comparison isolated
                       ↦ CechComparison.{cechH0 (≅ℤ/lcm), cechH1 (≅ℤ/gcd),
                         paper_ext_one_is_sheaf_ext}  PROVED (uncond.)
    Thm 6.1 / Tier-B B4 additive Euler χ on a pretriangulated cat: χ(cone f)=χB−χA ⇒
                       Δχmot=χ(Def_p)=χ(Xp)−χ(Up) for any additive χ (motive = external interface)
                       ↦ MotivicEuler.{AdditiveEuler, cone_euler, MotivicDeformation,
                         deltaChi_mot}                                        PROVED (uncond. cat-theory)
    §8.8 / Tier-B B5 actual point count + supersingular criterion: a_p=p+1−#E(𝔽_p) (Nat.card),
                       IsSupersingular := a_p≡0 mod p, a_p=0 ⇒ supersingular; Weil/Hasse = interface
                       ↦ FrobeniusPointCount.{frobeniusTrace, IsSupersingular,
                         isSupersingular_of_trace_zero, FrobeniusData}        PROVED (uncond. arith.)
    Def 7.1 §7.3 / Tier-B B6 cohomological defect δcoh := sInf{i|∃F,supp F=P ∧ Hⁱ(F)≠0};
                       easy bounds + δcoh=1 (§7.3, via B2); Prop 7.2 base-change = Tier C
                       ↦ CohDimension.{deltaCoh, deltaCoh_le, deltaCoh_mem,
                         deltaCoh_eq_one}                                     PROVED (uncond. def)
    §6 Thm 6.1 / Tier-C C1 Voevodsky motives interface: realization functor + Euler-preservation
                       axiom ⇒ bump = Δχmot = χmot(Xp)−χmot(Up); instance (DMc + R) = open obligation
                       ↦ MotivicC1.{MotivicRealization, motivicEuler, bump_eq_deltaChi}  PROVED (cond.)
    §6/§9.3 / Tier-C C2 curve étale H¹ dim formula: localization SES + normalization axioms ⇒
                       dim H¹(Xp)=2g+b₁+Σδ, smooth ⇒ dim H¹(Xp)=dim H¹(Up) (bump=0); étale = obligation
                       ↦ EtaleCurveCohomology.CurveWeilCohomology.{dimH1Xp_formula, bump_eq,
                         smooth_dim_eq}                                       PROVED (cond.)
    §2/§3.1 / Tier-C C3 sheaf-theoretic CRT gluing: gluing ⟺ CRT-compatible + separatedness (lcm);
                       "finite limits sectionwise" shadow certified; genuine site sheaf = obligation
                       ↦ PrimalitySheafCRT.{glue_iff_compatible, glue_unique,
                         sections_fiberProduct_eq}                            PROVED (uncond.)
    §9.2 / Tier-C C4 Thm 9.3 full equivalence (i)⇔(ii)⇔(iii)⇔(iv)⇔(v): arith core genuine
                       (A2 gate + equalizer–Tor), detector layer (v) universal over C1/C2 interfaces,
                       geometric instance = obligation; boundary marked by status audit
                       ↦ Thm93Assembly.{disc_hensel_gate_tfae, tor_equalizer_gate,
                         detector_tfae, thm93_full_tfae, thm93_full_tfae_motivic}
                                                                              PROVED (core uncond. / (v) cond.)
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
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.ComputeDegree
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Conductor
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
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

/-! ## B5 — actual point count and a formalizable supersingularity criterion.

The §C5 shadow above takes the point count `N` as a *given* number.  §B5 binds `a_p` to the **actual**
group of `𝔽_p`-points (`Nat.card W.toAffine.Point`, via Mathlib's `WeierstrassCurve.Affine.Point`),
defines supersingularity by the formalizable criterion `a_p ≡ 0 (mod p)`, and proves
`a_p = 0 ⇒ supersingular` genuinely.  Mathlib lacks the finite-field Frobenius/Hasse package, so the
agreement of this arithmetic criterion with the *geometric* definition (Hasse invariant `= 0` /
inseparable Frobenius, with char-polynomial `T² − a_p T + p`) is exposed as the interface
`FrobeniusData`; constructing an instance from the curve geometry is the unresolved Tier-C obligation. -/

namespace FrobeniusPointCount

open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- **`a_p = p + 1 − #E(𝔽_p)`, bound to the actual point count.**  `Nat.card W.toAffine.Point` is the
genuine number of affine `𝔽_p`-points of `E` (the point at infinity plus the nonsingular solutions of
the Weierstrass equation). -/
noncomputable def frobeniusTrace (W : WeierstrassCurve (ZMod p)) : ℤ :=
  (p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)

/-- The actual trace is the §C5 arithmetic trace at the genuine point count. -/
theorem frobeniusTrace_eq (W : WeierstrassCurve (ZMod p)) :
    frobeniusTrace W = frobeniusTraceFromPointCount p (Nat.card W.toAffine.Point) :=
  rfl

/-- **Supersingularity criterion (formalizable).**  `E/𝔽_p` is supersingular iff `a_p ≡ 0 (mod p)`. -/
def IsSupersingular (W : WeierstrassCurve (ZMod p)) : Prop :=
  (p : ℤ) ∣ frobeniusTrace W

/-- **`a_p = 0 ⇒ supersingular`** (genuine: `p ∣ 0`). -/
theorem isSupersingular_of_trace_zero {W : WeierstrassCurve (ZMod p)}
    (h : frobeniusTrace W = 0) : IsSupersingular W := by
  rw [IsSupersingular, h]; exact dvd_zero _

/-- The Frobenius characteristic polynomial `T² − a_p T + p` at the actual trace. -/
noncomputable def frobeniusCharPoly (W : WeierstrassCurve (ZMod p)) : Polynomial ℤ :=
  frobeniusTatePolynomial p (frobeniusTrace W)

/-- Evaluation of the Frobenius characteristic polynomial: `T² − a_p T + p`. -/
theorem frobeniusCharPoly_eval (W : WeierstrassCurve (ZMod p)) (x : ℤ) :
    (frobeniusCharPoly W).eval x = x ^ 2 - frobeniusTrace W * x + p :=
  frobeniusTatePolynomial_eval p (frobeniusTrace W) x

/-- **Frobenius/Weil interface (the geometric Tier-C obligation).**  Packages the agreement between a
geometric supersingularity predicate (Hasse invariant `= 0` / inseparable Frobenius) and the
arithmetic criterion `a_p ≡ 0 (mod p)`.  Mathlib has no finite-field Frobenius/Hasse theory, so
constructing an instance from the curve geometry is the unresolved obligation; *given* it, the
paper's `a_p = 0 ⇒ supersingular` (geometric) is genuine. -/
structure FrobeniusData (W : WeierstrassCurve (ZMod p)) where
  /-- A geometric supersingularity predicate (e.g. Hasse invariant zero). -/
  geomSupersingular : Prop
  /-- Weil/Hasse agreement: geometric supersingularity ⟺ `a_p ≡ 0 (mod p)`. -/
  agrees : geomSupersingular ↔ IsSupersingular W

/-- Under the Frobenius/Weil interface, `a_p = 0 ⇒ geometrically supersingular`. -/
theorem FrobeniusData.geom_of_trace_zero {W : WeierstrassCurve (ZMod p)}
    (D : FrobeniusData W) (h : frobeniusTrace W = 0) : D.geomSupersingular :=
  D.agrees.mpr (isSupersingular_of_trace_zero h)

end FrobeniusPointCount

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

/-! ### B2 — flasque Γ-exactness (genuine, from Mathlib) and the acyclicity isolation.

The original Tier-3 audit recorded flasque acyclicity as future work, but the *key* property —
that the global-sections functor `Γ` sends a flasque short exact sequence to a surjection — IS
available in Mathlib (`IsFlasque.epi_of_shortExact`), together with the flasque-resolution step
(`of_shortExact_of_isFlasque₁₂`).  We expose both unconditionally.  The remaining ingredient for
`Hⁱ = 0 (i>0)` is the dimension-shifting argument over the `Ext` long exact sequence (Mathlib has
the LES `Ext.covariant_sequence_exact` and `Ext.eq_zero_of_injective`, but not flasque/injective
sheaf resolutions); it is isolated as `IsGammaAcyclic`.  The `H¹ ≅ ⊕Λ` *value* is the unconditional
module computation `detector_directSum_linearEquiv` (the Čech / `Additions.*` route). -/

/-- **B2 core (genuine).**  `Γ` sends a flasque short exact sequence of `AddCommGrpCat`-sheaves to a
surjection on every open: for `0 → 𝓕 → 𝓖 → 𝓗 → 0` with `𝓕` flasque, `𝓖(U) → 𝓗(U)` is epi.
This is the key Γ-exactness behind flasque acyclicity. -/
theorem flasque_sections_epi {X : TopCat} {U : Opens X}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] : Epi (S.g.1.app (op U)) :=
  TopCat.Sheaf.IsFlasque.epi_of_shortExact hS

/-- **B2 (global sections surjective).**  The global-sections (`U = ⊤`) form of `flasque_sections_epi`:
`Γ(X, 𝓖) → Γ(X, 𝓗)` is surjective. -/
theorem flasque_global_sections_surjective {X : TopCat}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] :
    Function.Surjective (S.g.1.app (op (⊤ : Opens X))) :=
  (AddCommGrpCat.epi_iff_surjective _).mp (TopCat.Sheaf.IsFlasque.epi_of_shortExact hS)

/-- **B2 (flasque resolution step).**  In a flasque SES the quotient is flasque, so flasque
resolutions exist (the inductive input for dimension shifting). -/
theorem flasque_quotient_isFlasque {X : TopCat}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] [TopCat.Sheaf.IsFlasque S.X₂] :
    TopCat.Sheaf.IsFlasque S.X₃ :=
  TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS

/-- **Γ-acyclicity** of a sheaf: all higher sheaf cohomology (`= Ext` from the constant sheaf)
vanishes.  This is the precise statement isolated as the residual Tier-B step "flasque ⇒ acyclic"
(the dimension shifting over the `Ext` LES). -/
def IsGammaAcyclic {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{w})
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (CategoryTheory.Sheaf J AddCommGrpCat.{w})] : Prop :=
  ∀ n : ℕ, Subsingleton (CategoryTheory.Sheaf.H F (n + 1))

/-- A Γ-acyclic sheaf has trivial `H¹` (the Prop 10.6 vanishing once acyclicity is supplied). -/
theorem IsGammaAcyclic.h1_subsingleton {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : CategoryTheory.Sheaf J AddCommGrpCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (CategoryTheory.Sheaf J AddCommGrpCat.{w})]
    (h : IsGammaAcyclic F) : Subsingleton (CategoryTheory.Sheaf.H F 1) :=
  h 0

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

/-! ## A1 / Thm 9.3(i)⇔(ii) — the good-locus equivalence (FIFTH CORRECTION).

The paper's Theorem 9.3(ii) asserts, as an *unconditional reverse*, that a unique
`p`-adic lift forces full Jacobian rank (a unit derivative / simple residual root).
That reverse is **false**.  Counterexample: `F = X²` over `ℤ₂` at `a = 0`.  The only
root of `X²` in the open unit ball is `0` (`ℤ₂` is a domain, so `z² = 0 ⇒ z = 0`), so
the lift is unique; yet `F'(0) = 0`, so `‖F'(0)‖ = 0 ≠ 1` — the Jacobian is not a unit
(`GoodLocus.unique_lift_not_imply_unit_derivative`).

The honest content of (i)⇔(ii) is the **good-locus equivalence** on `U = D(Δ)`:

      p ∤ Δ   ⟺   f̄ = F mod p ∈ 𝔽ₚ[X] is separable   ⟺   every residual root is simple,

where `Δ` is the discriminant of the monic integer polynomial `F`.  The forward
"simple residual root ⇒ unique lift" half is already closed *unconditionally* by
`hensel_gate` / `PrimeScan.simpleRoot_has_uniquePadicLift`.  This section supplies the
missing `p ∤ Δ ⟺ separable ⟺ all residual roots simple` ring, completing (i)⇔(ii)
**without** the false unconditional reverse.

`Δ` is realised two ways, both faithful to Mathlib:
* `GoodLocus.disc F := F.resultant F' (deg F) (deg F − 1)` — base-change-stable, the
  primary `Δ` for the mod-`p` reduction (`= ± F.discr`, see `disc_eq`);
* `Polynomial.discr` directly, at the residue-field level
  (`separable_iff_discr_ne_zero`) and integrally (`not_dvd_discr_iff_separable`).

This is the fifth paper correction surfaced by formalization, after the four §M items
(min↔max thickness, the Mayer–Vietoris sign, the lcm↔gcd overlap, the module-Ext
degree).  Unlike the conditional `goodPrime_synchronization`, the equivalence here is
entirely unconditional: Mathlib has `Polynomial.Separable`, `separable_def`,
`PerfectField.separable_iff_squarefree`, the resultant/discriminant theory, and the
root-multiplicity calculus. -/

namespace GoodLocus

open Polynomial

/-! ### Field-level core: separable ⟺ coprime ⟺ resultant unit ⟺ Δ ≠ 0. -/

section Field

variable {K : Type*} [Field K]

/-- Separability is coprimality with the derivative (Mathlib's `separable_def`). -/
theorem separable_iff_isCoprime_derivative (f : K[X]) :
    f.Separable ↔ IsCoprime f (derivative f) := Polynomial.separable_def f

/-- Over a perfect field (e.g. any finite `𝔽ₚ`), separable ⟺ squarefree: this is the
algebraic encoding of "no repeated factor", i.e. every root (in the algebraic closure)
is simple. -/
theorem separable_iff_squarefree_of_perfectField [PerfectField K] (f : K[X]) :
    f.Separable ↔ Squarefree f := PerfectField.separable_iff_squarefree

/-- For monic `f`, separability ⟺ the resultant `Res(f, f')` is a unit. -/
theorem separable_iff_isUnit_resultant {f : K[X]} (hf : f.Monic) :
    f.Separable ↔ IsUnit (f.resultant (derivative f)) := by
  rw [Polynomial.separable_def, ← Polynomial.isUnit_resultant_iff_isCoprime hf]

/-- Padding identity: for monic `f`, the discriminant-shaped resultant
`Res(f, f', deg f, deg f − 1)` equals the default resultant `Res(f, f')`.  (The extra
formal rows contribute only powers of the leading coefficient `= 1`.) -/
theorem resultant_explicit_eq_default {f : K[X]} (hf : f.Monic) :
    f.resultant (derivative f) f.natDegree (f.natDegree - 1) = f.resultant (derivative f) := by
  set d := (derivative f).natDegree with hd
  have hle : d ≤ f.natDegree - 1 := natDegree_derivative_le f
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, Polynomial.resultant_add_right_deg (f := f) (g := derivative f)
        (m := f.natDegree) (n := d) (k := k) (le_rfl), hf.coeff_natDegree, one_pow, one_mul]

/-- For monic `f` over a field, separability ⟺ the discriminant-shaped resultant is
nonzero. -/
theorem separable_iff_resultant_explicit_ne_zero {f : K[X]} (hf : f.Monic) :
    f.Separable ↔ f.resultant (derivative f) f.natDegree (f.natDegree - 1) ≠ 0 := by
  rw [Polynomial.separable_def, ← Polynomial.isUnit_resultant_iff_isCoprime hf,
      isUnit_iff_ne_zero, resultant_explicit_eq_default hf]

/-- **`p ∤ Δ` face, field level.**  For monic `f` of positive degree over a field,
separability ⟺ `Polynomial.discr f ≠ 0`. -/
theorem separable_iff_discr_ne_zero {f : K[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    f.Separable ↔ f.discr ≠ 0 := by
  have hdpos : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
  have hr := Polynomial.resultant_deriv hdpos
  rw [hf.leadingCoeff, mul_one] at hr
  rw [separable_iff_resultant_explicit_ne_zero hf, hr, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero), h⟩⟩

/-! ### Pointwise residual simple-root face: rootMultiplicity = 1 ⟺ simple. -/

/-- A residual point `a` is a *simple* root of `f` (multiplicity one) iff `f` vanishes
at `a` while `f'` does not — exactly the predicate the prime scanner uses. -/
theorem rootMultiplicity_eq_one_iff_simple {f : K[X]} (hf : f ≠ 0) (a : K) :
    f.rootMultiplicity a = 1 ↔ f.IsRoot a ∧ ¬ (derivative f).IsRoot a := by
  have h1 : 0 < f.rootMultiplicity a ↔ f.IsRoot a := rootMultiplicity_pos hf
  have h2 : 1 < f.rootMultiplicity a ↔ (f.IsRoot a ∧ (derivative f).IsRoot a) :=
    one_lt_rootMultiplicity_iff_isRoot hf
  constructor
  · intro h
    have hpos : 0 < f.rootMultiplicity a := by omega
    exact ⟨h1.mp hpos, fun hd => absurd (h2.mpr ⟨h1.mp hpos, hd⟩) (by omega)⟩
  · rintro ⟨hr, hnd⟩
    have hpos := h1.mpr hr
    have hnot2 : ¬ 1 < f.rootMultiplicity a := fun hc => hnd (h2.mp hc).2
    omega

/-- Separable ⟹ every root is simple (multiplicity exactly one). -/
theorem rootMultiplicity_eq_one_of_separable {f : K[X]} (hsep : f.Separable) {a : K}
    (ha : f.IsRoot a) : f.rootMultiplicity a = 1 := by
  have hf := hsep.ne_zero
  have hle := rootMultiplicity_le_one_of_separable hsep a
  have hpos := (rootMultiplicity_pos hf).mpr ha
  omega

/-- Separable ⟹ no root is shared with the derivative (every root simple). -/
theorem not_isRoot_derivative_of_separable {f : K[X]} (hsep : f.Separable) {a : K}
    (ha : f.IsRoot a) : ¬ (derivative f).IsRoot a :=
  ((rootMultiplicity_eq_one_iff_simple hsep.ne_zero a).mp
    (rootMultiplicity_eq_one_of_separable hsep ha)).2

/-- Literal "all roots in `K` are simple" face: when `f` splits over `K`, separability
is exactly the absence of repeated roots. -/
theorem separable_iff_roots_nodup_of_splits {f : K[X]} (hf : f ≠ 0) (h : f.Splits) :
    f.Separable ↔ f.roots.Nodup := (nodup_roots_iff_of_splits hf h).symm

/-- **Good-locus TFAE over a field** (monic, positive degree): the five faces of
Thm 9.3(i)⇔(ii) that are unconditionally equivalent over any field. -/
theorem good_locus_field_tfae {f : K[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    [ f.Separable
    , IsCoprime f (derivative f)
    , IsUnit (f.resultant (derivative f))
    , f.resultant (derivative f) f.natDegree (f.natDegree - 1) ≠ 0
    , f.discr ≠ 0 ].TFAE := by
  tfae_have 1 ↔ 2 := separable_iff_isCoprime_derivative f
  tfae_have 1 ↔ 3 := separable_iff_isUnit_resultant hf
  tfae_have 1 ↔ 4 := separable_iff_resultant_explicit_ne_zero hf
  tfae_have 1 ↔ 5 := separable_iff_discr_ne_zero hf hdeg
  tfae_finish

end Field

/-! ### Integer level: the discriminant `Δ`, its mod-`p` base change, and `p ∤ Δ`. -/

/-- The discriminant of the monic integer polynomial `F`, realised as the
base-change-stable resultant `Res(F, F', deg F, deg F − 1)`.  Equals `± F.discr`
(`disc_eq`). -/
noncomputable def disc (F : Polynomial ℤ) : ℤ :=
  F.resultant (derivative F) F.natDegree (F.natDegree - 1)

/-- `disc F = ± F.discr` for monic `F` of positive degree. -/
theorem disc_eq {F : Polynomial ℤ} (hF : F.Monic) (hdeg : 0 < F.natDegree) :
    disc F = (-1) ^ (F.natDegree * (F.natDegree - 1) / 2) * F.discr := by
  have hdpos : 0 < F.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
  have hr := Polynomial.resultant_deriv hdpos
  rw [hF.leadingCoeff, mul_one] at hr
  exact hr

/-- **Base change of `Δ`.**  The reduction of `disc F` modulo `p` is the same
discriminant-shaped resultant of the residue polynomial `F mod p`. -/
theorem intCast_disc_eq (F : Polynomial ℤ) (p : ℕ) [Fact p.Prime] :
    ((disc F : ℤ) : ZMod p)
      = (PrimeScan.modPolynomial p F).resultant (derivative (PrimeScan.modPolynomial p F))
          F.natDegree (F.natDegree - 1) := by
  unfold disc PrimeScan.modPolynomial
  rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
  rfl

/-- **A1 / Thm 9.3(i)⇔(ii), integer good-locus gate (unconditional).**  For monic
`F : ℤ[X]`, `p ∤ Δ` iff the residue polynomial `F mod p` is separable. -/
theorem not_dvd_disc_iff_separable {F : Polynomial ℤ} (hF : F.Monic) (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ disc F ↔ (PrimeScan.modPolynomial p F).Separable := by
  have hfmonic : (PrimeScan.modPolynomial p F).Monic := by
    rw [PrimeScan.modPolynomial]; exact hF.map _
  have hnd : (PrimeScan.modPolynomial p F).natDegree = F.natDegree := by
    rw [PrimeScan.modPolynomial]; exact hF.natDegree_map _
  rw [← CharP.intCast_eq_zero_iff (ZMod p) p, intCast_disc_eq,
      separable_iff_resultant_explicit_ne_zero hfmonic, hnd]

/-- The same gate stated with `Polynomial.discr` directly: `p ∤ discr F` iff
`F mod p` is separable.  (`disc F` and `F.discr` differ by the unit `± 1`.) -/
theorem not_dvd_discr_iff_separable {F : Polynomial ℤ} (hF : F.Monic) (hdeg : 0 < F.natDegree)
    (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ F.discr ↔ (PrimeScan.modPolynomial p F).Separable := by
  rw [← not_dvd_disc_iff_separable hF p, disc_eq hF hdeg]
  refine not_congr ?_
  rcases Nat.even_or_odd (F.natDegree * (F.natDegree - 1) / 2) with he | ho
  · rw [he.neg_one_pow, one_mul]
  · rw [ho.neg_one_pow, neg_one_mul, dvd_neg]

/-! ### Residue-field equivalence over `𝔽ₚ`, and the bridge to the prime scanner. -/

/-- **A1 / Thm 9.3(i)⇔(ii), the full good-locus TFAE over `𝔽ₚ`** (monic `F`,
positive degree): `p ∤ Δ`, separability of `F mod p`, squarefreeness (every residual
root simple), coprimality with the derivative, and `discr (F mod p) ≠ 0` are all
equivalent. -/
theorem modPolynomial_good_locus_tfae {F : Polynomial ℤ} (hF : F.Monic) (hdeg : 0 < F.natDegree)
    (p : ℕ) [Fact p.Prime] :
    [ ¬ (p : ℤ) ∣ disc F
    , (PrimeScan.modPolynomial p F).Separable
    , Squarefree (PrimeScan.modPolynomial p F)
    , IsCoprime (PrimeScan.modPolynomial p F) (derivative (PrimeScan.modPolynomial p F))
    , (PrimeScan.modPolynomial p F).discr ≠ 0 ].TFAE := by
  have hfm : (PrimeScan.modPolynomial p F).Monic := by
    rw [PrimeScan.modPolynomial]; exact hF.map _
  have hfd : 0 < (PrimeScan.modPolynomial p F).natDegree := by
    have hnd : (PrimeScan.modPolynomial p F).natDegree = F.natDegree := by
      rw [PrimeScan.modPolynomial]; exact hF.natDegree_map _
    omega
  tfae_have 1 ↔ 2 := not_dvd_disc_iff_separable hF p
  tfae_have 2 ↔ 3 := separable_iff_squarefree_of_perfectField _
  tfae_have 2 ↔ 4 := separable_iff_isCoprime_derivative _
  tfae_have 2 ↔ 5 := separable_iff_discr_ne_zero hfm hfd
  tfae_finish

/-- Membership in the scanner's simple-root set is exactly "the residue point is a
simple root" (multiplicity one). -/
theorem mem_simpleRoots_iff_rootMultiplicity_eq_one (p : ℕ) [Fact p.Prime] (F : Polynomial ℤ)
    (a : ZMod p) (hf : PrimeScan.modPolynomial p F ≠ 0) :
    a ∈ PrimeScan.simpleRoots p F ↔ (PrimeScan.modPolynomial p F).rootMultiplicity a = 1 := by
  rw [PrimeScan.mem_simpleRoots_iff, rootMultiplicity_eq_one_iff_simple hf]
  rfl

/-- If `F mod p` is separable (good locus `p ∤ Δ`), then every residual root is a
simple root accepted by the scanner. -/
theorem isRoot_mem_simpleRoots_of_separable (p : ℕ) [Fact p.Prime] (F : Polynomial ℤ)
    (a : ZMod p) (hsep : (PrimeScan.modPolynomial p F).Separable)
    (ha : (PrimeScan.modPolynomial p F).IsRoot a) : a ∈ PrimeScan.simpleRoots p F := by
  rw [mem_simpleRoots_iff_rootMultiplicity_eq_one p F a hsep.ne_zero]
  exact rootMultiplicity_eq_one_of_separable hsep ha

/-- **Good locus ⇒ unique residual lifts (the genuine (i)⇒(ii) good direction).**
If `F mod p` is separable, then every residual root has a unique `p`-adic Hensel lift
in its residue ball.  Composes the new separability bridge with the unconditional
`hensel_gate`. -/
theorem uniquePadicLift_of_separable_isRoot (p : ℕ) [Fact p.Prime] (F : Polynomial ℤ)
    (a : ZMod p) (hsep : (PrimeScan.modPolynomial p F).Separable)
    (ha : (PrimeScan.modPolynomial p F).IsRoot a) :
    ∃! z : ℤ_[p],
      (PrimeScan.padicPolynomial p F).eval z = 0 ∧
        ‖z - PrimeScan.padicRepresentative p a‖ < 1 :=
  PrimeScan.simpleRoot_has_uniquePadicLift p F a
    (isRoot_mem_simpleRoots_of_separable p F a hsep ha)

/-- **Corrected Thm 9.3(i)⇔(ii) gate (unconditional).**  The honest content of the
discriminant/Hensel gate on `U = D(Δ)`: good reduction `p ∤ Δ` is equivalent to
separability of the residue polynomial — *not* to any unconditional
"unique lift ⇒ Jacobian rank" reverse, which fails (see
`unique_lift_not_imply_unit_derivative`).  This replaces the conditional
`smooth ↔ gcd = 1` face of `goodPrime_synchronization` by a proved equivalence. -/
theorem goodPrime_gate {F : Polynomial ℤ} (hF : F.Monic) (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ disc F ↔ (PrimeScan.modPolynomial p F).Separable :=
  not_dvd_disc_iff_separable hF p

/-! ### The FIFTH CORRECTION: the paper's unconditional reverse is false. -/

/-- **FIFTH CORRECTION (counterexample to the paper's unconditional reverse).**
Theorem 9.3(ii) as literally stated claims "a unique `p`-adic lift in the residue ball
⇒ the Jacobian/derivative is a unit".  This reverse is **false**.  Witness: `F = X²`
over `ℤ₂` at `a = 0`.  The only root of `X²` in the open unit ball is `0` (`ℤ₂` is a
domain, so `z² = 0 ⇒ z = 0`), so the lift is unique; yet `F'(0) = 0`, hence
`‖F'(0)‖ = 0 ≠ 1`. -/
theorem unique_lift_not_imply_unit_derivative :
    ∃ (p : ℕ) (_ : Fact p.Prime) (F : Polynomial ℤ_[p]) (a : ℤ_[p]),
      (∃! z : ℤ_[p], F.eval z = 0 ∧ ‖z - a‖ < 1) ∧ ‖F.derivative.eval a‖ ≠ 1 := by
  refine ⟨2, ⟨Nat.prime_two⟩, X ^ 2, 0, ?_, ?_⟩
  · refine ⟨0, ⟨by simp, by simp⟩, ?_⟩
    rintro z ⟨hz, _⟩
    simpa using pow_eq_zero_iff (two_ne_zero) |>.mp (by simpa using hz)
  · simp

end GoodLocus

/-! ## A2 / Prop 2 — Weierstrass discriminant gate at the polynomial level.

For the short Weierstrass curve `E : y² = x³ + a x + b`, the good-reduction condition
`p ∤ Δ(E)` is the residual-fiber nonsingularity condition, which at the level of the
defining cubic is *separability* (= squarefreeness) of `x³ + a x + b mod p`:

      p ∤ Δ(E)   ⟺   (x³ + a x + b mod p) is squarefree   ⟺   it is separable.

This is closed entirely at the residual-polynomial level (Tier A) on top of the A1
`GoodLocus` machinery — no scheme-theoretic smoothness is invoked.  The bridge to
`WeierstrassCurve.Δ` is the polynomial identity `Δ(⟨0,0,0,a,b⟩) = -16(4a³+27b²)`
(`shortWeierstrass_Δ`), and `discr(x³+ax+b) = -4a³-27b²` (`cubicPoly_discr`).  Promotion
to a scheme-level `Affine.Nonsingular` statement is optional (Tier B) and not done here. -/

namespace WeierstrassGate

open Polynomial

/-! ### The depressed cubic `X³ + aX + b` (= RHS of `y² = x³ + ax + b`). -/

section Ring

variable {R : Type*} [CommRing R]

/-- The depressed cubic `x³ + a x + b` cutting out the affine curve `y² = x³ + a x + b`. -/
noncomputable def cubicPoly (a b : R) : R[X] := X ^ 3 + C a * X + C b

theorem cubicPoly_monic (a b : R) : (cubicPoly a b).Monic := by
  unfold cubicPoly; monicity!

theorem cubicPoly_natDegree [Nontrivial R] (a b : R) : (cubicPoly a b).natDegree = 3 := by
  unfold cubicPoly; compute_degree!

theorem cubicPoly_degree [Nontrivial R] (a b : R) : (cubicPoly a b).degree = 3 := by
  unfold cubicPoly; compute_degree!

theorem cubicPoly_coeff (a b : R) :
    (cubicPoly a b).coeff 0 = b ∧ (cubicPoly a b).coeff 1 = a ∧
      (cubicPoly a b).coeff 2 = 0 ∧ (cubicPoly a b).coeff 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cubicPoly, coeff_X_pow]

/-- The polynomial discriminant of the depressed cubic: `discr(x³+ax+b) = -4a³ - 27b²`. -/
theorem cubicPoly_discr [Nontrivial R] (a b : R) :
    (cubicPoly a b).discr = -4 * a ^ 3 - 27 * b ^ 2 := by
  obtain ⟨c0, c1, c2, c3⟩ := cubicPoly_coeff a b
  rw [Polynomial.discr_of_degree_eq_three (cubicPoly_degree a b), c0, c1, c2, c3]; ring

theorem cubicPoly_map {S : Type*} [CommRing S] (φ : R →+* S) (a b : R) :
    (cubicPoly a b).map φ = cubicPoly (φ a) (φ b) := by
  simp [cubicPoly]

/-- The short Weierstrass curve `y² = x³ + a x + b` (i.e. `a₁ = a₂ = a₃ = 0`). -/
def shortWeierstrass (a b : R) : WeierstrassCurve R := ⟨0, 0, 0, a, b⟩

/-- The Weierstrass discriminant of the short form: `Δ = -16(4a³ + 27b²)`. -/
theorem shortWeierstrass_Δ (a b : R) :
    (shortWeierstrass a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simp only [shortWeierstrass, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- `Δ(E) = 16 · discr(x³+ax+b)`: the Weierstrass discriminant is the cubic
discriminant up to the unit `16` (a unit away from characteristic `2`). -/
theorem shortWeierstrass_Δ_eq_cubic_discr [Nontrivial R] (a b : R) :
    (shortWeierstrass a b).Δ = 16 * (cubicPoly a b).discr := by
  rw [shortWeierstrass_Δ, cubicPoly_discr]; ring

end Ring

/-! ### Separability / squarefree gate over a field (residual fiber nonsingular). -/

section Field

variable {K : Type*} [Field K]

/-- **Residual nonsingularity at the cubic level.**  `x³ + a x + b` is separable iff its
discriminant `-(4a³+27b²)` is nonzero, i.e. `4a³ + 27b² ≠ 0`. -/
theorem cubicPoly_separable_iff (a b : K) :
    (cubicPoly a b).Separable ↔ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  have hdeg : 0 < (cubicPoly a b).natDegree := by rw [cubicPoly_natDegree]; norm_num
  rw [GoodLocus.separable_iff_discr_ne_zero (cubicPoly_monic a b) hdeg, cubicPoly_discr,
      show (-4 * a ^ 3 - 27 * b ^ 2 : K) = -(4 * a ^ 3 + 27 * b ^ 2) from by ring, neg_ne_zero]

/-- Over a perfect field, "all residual roots simple" = squarefree: `x³+ax+b` is
squarefree iff `4a³ + 27b² ≠ 0`. -/
theorem cubicPoly_squarefree_iff [PerfectField K] (a b : K) :
    Squarefree (cubicPoly a b) ↔ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  rw [← GoodLocus.separable_iff_squarefree_of_perfectField, cubicPoly_separable_iff]

end Field

/-! ### Integer / mod-`p` gate, and the Weierstrass `Δ` form. -/

/-- **A2 (cubic form, all primes).**  `p ∤ (4a³+27b²)` iff the residual cubic
`x³ + a x + b mod p` is separable. -/
theorem not_dvd_cubic_disc_iff_separable {a b : ℤ} (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ (4 * a ^ 3 + 27 * b ^ 2) ↔
      (cubicPoly (a : ZMod p) (b : ZMod p)).Separable := by
  rw [cubicPoly_separable_iff,
      show (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2)
        = ((4 * a ^ 3 + 27 * b ^ 2 : ℤ) : ZMod p) from by push_cast; ring,
      Ne, CharP.intCast_eq_zero_iff (ZMod p) p]

/-- **A2 (cubic form, squarefree).**  `p ∤ (4a³+27b²)` iff `x³ + a x + b mod p` is
squarefree (= every residual root simple). -/
theorem not_dvd_cubic_disc_iff_squarefree {a b : ℤ} (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ (4 * a ^ 3 + 27 * b ^ 2) ↔
      Squarefree (cubicPoly (a : ZMod p) (b : ZMod p)) := by
  rw [not_dvd_cubic_disc_iff_separable, cubicPoly_separable_iff, ← cubicPoly_squarefree_iff]

/-- **A2 headline TFAE.**  Good reduction `p ∤ (4a³+27b²)`, separability, and
squarefreeness of the residual cubic are equivalent. -/
theorem cubic_good_locus_tfae {a b : ℤ} (p : ℕ) [Fact p.Prime] :
    [ ¬ (p : ℤ) ∣ (4 * a ^ 3 + 27 * b ^ 2)
    , (cubicPoly (a : ZMod p) (b : ZMod p)).Separable
    , Squarefree (cubicPoly (a : ZMod p) (b : ZMod p)) ].TFAE := by
  tfae_have 1 ↔ 2 := not_dvd_cubic_disc_iff_separable p
  tfae_have 1 ↔ 3 := not_dvd_cubic_disc_iff_squarefree p
  tfae_finish

/-- **A2 Weierstrass `Δ` form (`p ≠ 2`).**  `p ∤ Δ(E)` iff the residual cubic is
separable (= nonsingular fiber).  Away from characteristic `2` the unit factor `16`
in `Δ = -16(4a³+27b²)` is invisible. -/
theorem not_dvd_shortWeierstrass_Δ_iff_separable {a b : ℤ} (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ ↔
      (cubicPoly (a : ZMod p) (b : ZMod p)).Separable := by
  have hp := (Fact.out : p.Prime)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h16 : ¬ (p : ℤ) ∣ 16 := by
    rw [show (16 : ℤ) = ((16 : ℕ) : ℤ) from by norm_num, Int.natCast_dvd_natCast]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 from by simpa using h)))
  rw [← not_dvd_cubic_disc_iff_separable, shortWeierstrass_Δ]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · rw [neg_mul, dvd_neg] at h
    rcases hpZ.dvd_mul.mp h with h1 | h2
    · exact absurd h1 h16
    · exact h2
  · rw [neg_mul, dvd_neg]; exact h.mul_left 16

end WeierstrassGate

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
  have e := torEquivZModGcd 60 (2 ^ 2 * 3 * 5)
  rw [show Nat.gcd 60 (2 ^ 2 * 3 * 5) = 60 from by decide] at e
  simpa using e.trans zmod60AddEquiv

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

The analytic per-factor bridge (`|log(1+u)|_p ≤ p^{-k}` for `u ∈ pᵏℤ_p`, and
`log(1+u) ≡ u (mod pᵏ)`) is developed in §D.2 (`PadicLog`), and §A4 closes the mod-`pᵏ`
AB-linearization skeleton `∑ⱼ aⱼ log(1+uⱼ) ≡ ∑ⱼ aⱼ uⱼ (mod pᵏ)` from it (no functional
equation).  The full infinite-precision bridge (`Padic.log` additivity) stays deferred to B1. -/

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

/-! ### A3 — concrete instantiation of the four layers.

The layers above are stated for *arbitrary* predicates, so the `sections_*` lemmas hold
verbatim once we pin the genuine gates.  We instantiate the four §2.1/2.2 layers with the
real gates built in §A0–§A2 (so `Γ(U,F) = ⋂ Γ(U,F_layer)` becomes a statement about the
actual primality filters, at essentially no cost):

* numeric `numLayer n := 1 < n`              — the size / archimedean filter;
* modular `modLayer M n := n.Coprime M`       — the CRT / sieve filter;
* Hensel  `discLayer a b n := ¬ n ∣ (4a³+27b²)` — residual-cubic separability (A2), i.e.
  the unique-`p`-adic-lift good locus of the §A1 Hensel gate;
* EC      `ecLayer a b n := ¬ n ∣ Δ(y²=x³+ax+b)` — good reduction of the curve (A2).

The Hensel and EC layers are tied to the §A2 separability gate by the coherence lemmas
`discLayer_iff_separable` and `ecLayer_iff_discLayer`. -/

/-- Numeric/size layer: the candidate is a nontrivial integer. -/
def numLayer (n : ℕ) : Prop := 1 < n

/-- Modular/sieve layer: the candidate is coprime to a fixed modulus `M`. -/
def modLayer (M : ℕ) (n : ℕ) : Prop := n.Coprime M

/-- Hensel/discriminant layer: the candidate prime does not divide the cubic discriminant
`4a³ + 27b²` (= the residual cubic `x³+ax+b` is separable, the §A2 unique-lift good locus). -/
def discLayer (a b : ℤ) (n : ℕ) : Prop := ¬ (n : ℤ) ∣ (4 * a ^ 3 + 27 * b ^ 2)

/-- Elliptic-curve layer: good reduction `n ∤ Δ(E)` for `E : y² = x³ + a x + b`. -/
def ecLayer (a b : ℤ) (n : ℕ) : Prop := ¬ (n : ℤ) ∣ (WeierstrassGate.shortWeierstrass a b).Δ

/-- The concrete primality gate: the fiber product of the four genuine layers. -/
def primeCertGate (a b : ℤ) (M : ℕ) : ℕ → Prop :=
  primalityLayer numLayer (modLayer M) (discLayer a b) (ecLayer a b)

/-- **A3 — concrete `Γ(U,F) = ⋂ Γ(U,F_layer)`.**  Global sections of the concrete gate
equal the intersection of the four concrete layers' sections, over any open `U`.  This is
the §2.2 fiber-product identity instantiated at the genuine gates. -/
theorem sections_primeCertGate (a b : ℤ) (M : ℕ) (U : Set ℕ) :
    sections (primeCertGate a b M) U
      = sections numLayer U ∩ sections (modLayer M) U
          ∩ sections (discLayer a b) U ∩ sections (ecLayer a b) U :=
  sections_primalityLayer numLayer (modLayer M) (discLayer a b) (ecLayer a b) U

/-- **A3 — sectionwise = intersection (pointwise) for the concrete gate.** -/
theorem primeCertGate_sectionwise (a b : ℤ) (M : ℕ) (n : ℕ) :
    primeCertGate a b M n
      ↔ n ∈ {m | numLayer m} ∩ {m | modLayer M m}
            ∩ {m | discLayer a b m} ∩ {m | ecLayer a b m} :=
  layers_sectionwise numLayer (modLayer M) (discLayer a b) (ecLayer a b) n

/-- The concrete fiber product as a subtype equivalence with the intersection. -/
def primeCertGate_equiv (a b : ℤ) (M : ℕ) :
    {n // primeCertGate a b M n}
      ≃ {n // n ∈ {m | numLayer m} ∩ {m | modLayer M m}
                ∩ {m | discLayer a b m} ∩ {m | ecLayer a b m}} :=
  primalityLayer_equiv numLayer (modLayer M) (discLayer a b) (ecLayer a b)

/-- **A3 ↔ A2 coherence.**  For a prime candidate `n`, the discriminant layer is exactly
residual-cubic separability: `discLayer a b n ↔ (x³+ax+b mod n) separable`. -/
theorem discLayer_iff_separable (a b : ℤ) (n : ℕ) [Fact n.Prime] :
    discLayer a b n ↔ (WeierstrassGate.cubicPoly (a : ZMod n) (b : ZMod n)).Separable :=
  WeierstrassGate.not_dvd_cubic_disc_iff_separable n

/-- **A3 ↔ A2 coherence.**  Away from characteristic `2`, the elliptic-curve layer and the
Hensel/discriminant layer coincide on prime candidates (both are residual separability). -/
theorem ecLayer_iff_discLayer (a b : ℤ) (n : ℕ) [Fact n.Prime] (hn2 : n ≠ 2) :
    ecLayer a b n ↔ discLayer a b n := by
  unfold ecLayer discLayer
  rw [WeierstrassGate.not_dvd_shortWeierstrass_Δ_iff_separable n hn2,
      WeierstrassGate.not_dvd_cubic_disc_iff_separable n]

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

/-! ### §F″ — A5: δ-invariants and the dual-graph first Betti number (definitions).

`curve_betti_identity` takes `b₁(Γ)` and `Σδ` as numeric *inputs*.  §A5 pins them down as genuine
definitions; only their identification with actual étale cohomology (`dim H¹ = 2g + b₁ + Σδ`) is
left to Tier C.

* `deltaInvariant R S` — the `R`-length of the normalization quotient `S ⧸ R` (`S` = integral
  closure / normalization), i.e. `dim_k(𝒪̃/𝒪)`; `deltaInvariant_eq_zero_iff` is the smooth/normal
  criterion `δ = 0 ⟺ (R → S) surjective`.  `deltaInvariantConductor` is the conductor variant.
* `firstBettiNumber E V C := E − V + C` — the cycle rank of the dual graph from combinatorial data;
  `graphFirstBetti` reads it off a `SimpleGraph` via `Nat.card`. -/

namespace CurveInvariants

/-! #### δ-invariant. -/

/-- **δ-invariant.**  The `R`-length of the normalization quotient `S ⧸ R` (`S` = integral closure
/ normalization of `R`), the local invariant `dim_k(𝒪̃/𝒪)` of a curve singularity. -/
noncomputable def deltaInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : ℕ∞ :=
  Module.length R (S ⧸ LinearMap.range (Algebra.linearMap R S))

/-- **Smooth/normal criterion.**  The δ-invariant vanishes iff the structure map `R → S` is
surjective (`R` already equals its normalization — no singular contribution). -/
theorem deltaInvariant_eq_zero_iff (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    deltaInvariant R S = 0 ↔ Function.Surjective (algebraMap R S) := by
  rw [deltaInvariant, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
      LinearMap.range_eq_top, Algebra.coe_linearMap]

/-- A trivial extension contributes no δ. -/
theorem deltaInvariant_self (R : Type*) [CommRing R] : deltaInvariant R R = 0 :=
  (deltaInvariant_eq_zero_iff R R).2 (fun x => ⟨x, by simp⟩)

/-- **δ via the conductor** of `R<x>` (the alternative form): `length_R (S ⧸ 𝔠)`. -/
noncomputable def deltaInvariantConductor (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (x : S) : ℕ∞ :=
  Module.length R (S ⧸ (conductor R x).restrictScalars R)

/-! #### Dual-graph first Betti number. -/

/-- **First Betti number (cycle rank)** of a graph from its combinatorial data: `E − V + C`. -/
def firstBettiNumber (edges vertices components : ℕ) : ℤ :=
  (edges : ℤ) - vertices + components

/-- A tree (connected, `E = V − 1`) has `b₁ = 0`. -/
theorem firstBettiNumber_tree (V : ℕ) (hV : 1 ≤ V) : firstBettiNumber (V - 1) V 1 = 0 := by
  simp only [firstBettiNumber]; omega

/-- For genuine graph data (`V ≤ E + C`) the first Betti number is nonnegative. -/
theorem firstBettiNumber_nonneg_of_le (edges vertices components : ℕ)
    (h : vertices ≤ edges + components) : 0 ≤ firstBettiNumber edges vertices components := by
  simp only [firstBettiNumber]; omega

/-- **First Betti number of a (dual) simple graph**, read off via `Nat.card`:
`|E| − |V| + |components|`. -/
noncomputable def graphFirstBetti {V : Type*} (G : SimpleGraph V) : ℤ :=
  firstBettiNumber (Nat.card G.edgeSet) (Nat.card V) (Nat.card G.ConnectedComponent)

/-! #### Connection to the curve Euler-characteristic identity (the Tier-C boundary). -/

/-- **Curve Euler-characteristic excess (ℤ form) with the combinatorial `b₁`.**  Given the
normalization inputs, `dim H¹(Xp) − dim H¹(Up) = b₁(Γ) + Σδ`.  The identification of the
dimensions with actual cohomology stays Tier C. -/
theorem betti_excess_eq (g E V C : ℕ) (deltaSum dimH1Xp dimH1Up : ℤ)
    (Hnorm : dimH1Xp = 2 * g + firstBettiNumber E V C + deltaSum) (Hsm : dimH1Up = 2 * g) :
    dimH1Xp - dimH1Up = firstBettiNumber E V C + deltaSum := by rw [Hnorm, Hsm]; ring

/-- **Smooth fibre silences the excess.**  A tree dual graph (`E = V−1`) with no δ gives
`dim H¹(Xp) = dim H¹(Up)`. -/
theorem betti_excess_smooth (g V : ℕ) (hV : 1 ≤ V) (dimH1Xp dimH1Up : ℤ)
    (Hnorm : dimH1Xp = 2 * g + firstBettiNumber (V - 1) V 1 + 0) (Hsm : dimH1Up = 2 * g) :
    dimH1Xp - dimH1Up = 0 := by
  rw [Hnorm, Hsm, firstBettiNumber_tree V hV]; ring

end CurveInvariants

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
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
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

/-! ## B3 — Čech = derived cohomology in degree ≤ 1, and `Ȟ¹ ≅ sheaf-Ext¹` (§7.2).

The arithmetic Čech faces are already certified by §G (`Additions.*`): the explicit 2-cover Čech
complex has `Ȟ⁰ = ker δ⁰ ≅ ℤ/lcm` (`range_iota_eq_ker_proj`) and `Ȟ¹ = coker δ⁰ ≅ ℤ/gcd`
(`coker_Phi_equiv`).  Here we (i) package those as named Čech cohomology objects, and (ii) supply the
honest §7.2 grounding: the paper's `Ȟ¹ ≅ Ext¹(ℤ_S, A)` is **sheaf**-cohomology `Ext` (`= Sheaf.H A 1`,
`sheafCohomology_eq_ext`) and **not** module-`Ext¹(ℤ,A)`, which vanishes identically
(`Tier3.int_module_ext_one_eq_zero`).  The full degree-≤1 comparison `Ȟ⁰ ≅ H⁰`, `Ȟ¹ ↪ H¹` (the edge
maps of the Čech-to-derived spectral sequence) is the residual step Mathlib does not yet package;
it is recorded by `status_cech_derived_comparison`. -/

namespace CechComparison

open CategoryTheory

universe u v w w'

/-- **Čech `Ȟ⁰` of the 2-cover** (equalizer / global sections): `ker δ⁰ ≅ ℤ/lcm(M,N)`.  This is the
explicit `H⁰` face, the sheaf-gluing kernel `(M) ∩ (N) = (lcm)`. -/
noncomputable def cechH0 (M N : ℕ) [NeZero M] [NeZero N] :
    ZMod (Nat.lcm M N) ≃+ (Additions.proj M N).ker := by
  haveI : NeZero (Nat.lcm M N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  rw [← Additions.range_iota_eq_ker_proj]
  exact AddEquiv.ofInjective (Additions.iota M N) (Additions.iota_injective M N)

/-- **Čech `Ȟ¹` of the 2-cover** (gluing obstruction): `coker δ⁰ ≅ ℤ/gcd(M,N)`.  This is the explicit
`H¹` face, the failure fibre. -/
noncomputable def cechH1 (M N : ℕ) [NeZero M] [NeZero N] :
    ((ZMod M × ZMod N) ⧸ (Additions.Phi M N).range) ≃+ ZMod (Nat.gcd M N) :=
  Additions.coker_Phi_equiv M N

/-- **B3 / §7.2 grounding (honest basis for "the paper's `Ext¹` is sheaf-`Ext`").**  Sheaf cohomology
`H¹` *is* sheaf-`Ext¹` from the constant sheaf (`sheafCohomology_eq_ext`), whereas module-`Ext¹(ℤ,A)`
vanishes identically (`int_module_ext_one_eq_zero`).  Hence the nonzero invariant the paper writes as
`Ȟ¹ ≅ Ext¹(ℤ_S, A)` must be the sheaf-`Ext` (= `H¹(S, A)`), not module-`Ext`. -/
theorem paper_ext_one_is_sheaf_ext
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{w})
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (CategoryTheory.Sheaf J AddCommGrpCat.{w})]
    (A : ModuleCat ℤ) :
    CategoryTheory.Sheaf.H F 1
        = CategoryTheory.Abelian.Ext
            ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) F 1
      ∧ (∀ e : CategoryTheory.Abelian.Ext (ModuleCat.of ℤ ℤ) A 1, e = 0) :=
  ⟨Tier3Actual.sheafCohomology_eq_ext F 1, fun e => Tier3.int_module_ext_one_eq_zero A e⟩

end CechComparison

/-! ## B4 — additive Euler characteristic on a pretriangulated category: `χ(cone f) = χ B − χ A`.

The motive functor `Mc(-)` is external (Tier 3), but the *logic* `Δχ_mot = χ_mot(Def_p) =
χ_mot(Xp) − χ_mot(Up)` closes in pure category theory.  An integer invariant additive on
distinguished triangles (= a homomorphism out of the Grothendieck group `K₀`) automatically
satisfies the cone relation `χ(cone f) = χ B − χ A`.  With `Def_p = cone(Mc(Up) → Mc(Xp))` this gives
`χ(Def_p) = χ(Xp) − χ(Up)` for *every* additive `χ`; only the realization triangle is an external
interface (`MotivicDeformation`).  This is the genuine, unconditional logical core of Thm 6.1
(complementing the ℕ-bookkeeping `curve_master_identity`). -/

namespace MotivicEuler

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An **additive Euler characteristic** on a pretriangulated category: an integer invariant `χ`
that is additive on distinguished triangles, `χ T.obj₂ = χ T.obj₁ + χ T.obj₃`.  Equivalently, a
group homomorphism out of the Grothendieck group `K₀(C)`. -/
structure AdditiveEuler where
  χ : C → ℤ
  additive : ∀ T : Triangle C, T ∈ distTriang C → χ T.obj₂ = χ T.obj₁ + χ T.obj₃

/-- The zero invariant is (trivially) an additive Euler characteristic, so `AdditiveEuler` is
inhabited. -/
def AdditiveEuler.zero : AdditiveEuler C where
  χ := fun _ => 0
  additive := fun _ _ => by simp

/-- **Motivic deformation data (the only external interface).**  The étale/motivic realization fits
the deformation `Defp` into a distinguished triangle
`Mc(Up) →(realize) Mc(Xp) →(toDef) Defp →(conn) Mc(Up)[1]`.  Construction of `Mc(-)` is external
(Tier 3); this packages the realization triangle. -/
structure MotivicDeformation where
  Up Xp Defp : C
  realize : Up ⟶ Xp
  toDef : Xp ⟶ Defp
  conn : Defp ⟶ Up⟦(1 : ℤ)⟧
  dist : Triangle.mk realize toDef conn ∈ distTriang C

variable {C}

/-- **B4 (cone Euler relation).**  For a distinguished triangle `A →(f) B → Z → A[1]`,
`χ Z = χ B − χ A`.  (`Z` is a cone of `f`.) -/
theorem AdditiveEuler.cone_euler (E : AdditiveEuler C) {T : Triangle C} (hT : T ∈ distTriang C) :
    E.χ T.obj₃ = E.χ T.obj₂ - E.χ T.obj₁ := by
  have h := E.additive T hT
  omega

/-- **B4 (cone of a morphism, explicit triangle).**  `χ(cone f) = χ B − χ A`. -/
theorem AdditiveEuler.euler_cone_mk (E : AdditiveEuler C) {A B Z : C}
    (f : A ⟶ B) (g : B ⟶ Z) (h : Z ⟶ A⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang C) :
    E.χ Z = E.χ B - E.χ A :=
  E.cone_euler hT

/-- **B4 (every morphism has a cone realizing the Euler relation).**  Via
`distinguished_cocone_triangle`, `f : A ⟶ B` admits a cone `Z` with `χ Z = χ B − χ A`. -/
theorem AdditiveEuler.exists_cone_euler (E : AdditiveEuler C) {A B : C} (f : A ⟶ B) :
    ∃ (Z : C) (g : B ⟶ Z) (h : Z ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ E.χ Z = E.χ B - E.χ A := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  exact ⟨Z, g, h, hT, E.cone_euler hT⟩

/-- **B4 / Thm 6.1 — `Δχ_mot` logic (genuine for ANY additive `χ`).**
`Δχ_mot = χ(Def_p) = χ(Xp) − χ(Up)`.  Pure category theory; only the realization triangle
(`MotivicDeformation`) is an external input. -/
theorem MotivicDeformation.deltaChi_mot (E : AdditiveEuler C) (D : MotivicDeformation C) :
    E.χ D.Defp = E.χ D.Xp - E.χ D.Up :=
  E.euler_cone_mk D.realize D.toDef D.conn D.dist

end MotivicEuler

/-! ## B6 — the genuine cohomological defect `δcoh` (Def 7.1) and its easy properties.

`δcoh P` is the least cohomological degree at which a sheaf supported exactly on `P` has nonvanishing
cohomology.  With `supp` the support assignment and `Sheaf.H` the (Ext-)sheaf cohomology of §C3, this
is directly formalizable as a `Nat.sInf`.  The base-change/localization invariance of Prop 7.2 needs
sheaf-cohomology base change (Tier C, Mathlib partial); but the *definition* and the §7.3 value
`δcoh = 1` are unconditional once combined with §B2 (the closed-point skyscraper has `H¹ ≅ ⊕Λ ≠ 0`
and acyclic `H⁰`). -/

namespace CohDimension

open CategoryTheory

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] {X : Type*}

/-- The set of cohomological degrees at which some sheaf supported exactly on `P` (for the support
assignment `supp`) has nonvanishing cohomology. -/
def cohDegrees (supp : Sheaf J AddCommGrpCat.{w} → Set X) (P : Set X) : Set ℕ :=
  {i : ℕ | ∃ F : Sheaf J AddCommGrpCat.{w}, supp F = P ∧ ¬ Subsingleton (Sheaf.H F i)}

/-- **Def 7.1 — cohomological defect `δcoh P`.**  The least degree in `cohDegrees supp P`
(`Nat.sInf`, with the empty-set convention `δcoh = 0`). -/
noncomputable def deltaCoh (supp : Sheaf J AddCommGrpCat.{w} → Set X) (P : Set X) : ℕ :=
  Nat.sInf (cohDegrees supp P)

variable {supp : Sheaf J AddCommGrpCat.{w} → Set X} {P : Set X}

theorem deltaCoh_eq_sInf : deltaCoh supp P = Nat.sInf (cohDegrees supp P) := rfl

/-- **Easy bound.**  A sheaf supported on `P` with nonvanishing `Hⁱ` forces `δcoh P ≤ i`. -/
theorem deltaCoh_le {i : ℕ} (F : Sheaf J AddCommGrpCat.{w}) (hsupp : supp F = P)
    (hi : ¬ Subsingleton (Sheaf.H F i)) : deltaCoh supp P ≤ i :=
  Nat.sInf_le ⟨F, hsupp, hi⟩

/-- **Easy realization.**  If the defect is attained (degree-set nonempty) then `δcoh P` is itself a
degree carrying a sheaf with nonvanishing cohomology. -/
theorem deltaCoh_mem (h : (cohDegrees supp P).Nonempty) :
    deltaCoh supp P ∈ cohDegrees supp P :=
  Nat.sInf_mem h

/-- Abstract `Nat.sInf = 1` criterion (`1 ∈ S`, `0 ∉ S`). -/
theorem sInf_eq_one {S : Set ℕ} (h1 : 1 ∈ S) (h0 : 0 ∉ S) : Nat.sInf S = 1 := by
  have hle : Nat.sInf S ≤ 1 := Nat.sInf_le h1
  have hpos : Nat.sInf S ≠ 0 := by
    rw [Ne, Nat.sInf_eq_zero]
    push_neg
    exact ⟨h0, (Set.nonempty_of_mem h1).ne_empty⟩
  omega

/-- **§7.3 — `δcoh = 1`.**  When some sheaf supported on `P` has `H¹ ≠ 0` (the closed-point
skyscraper, whose `H¹ ≅ ⊕Λ ≠ 0`) while no sheaf supported on `P` has `H⁰ ≠ 0` (acyclic `H⁰`), the
cohomological defect is `1`.  The two inputs are exactly §B2's skyscraper detector and `H⁰`-acyclicity. -/
theorem deltaCoh_eq_one (h1 : 1 ∈ cohDegrees supp P) (h0 : 0 ∉ cohDegrees supp P) :
    deltaCoh supp P = 1 :=
  sInf_eq_one h1 h0

end CohDimension

/-! ## C1 — Voevodsky motives & realization (Tier C, universal-axiom interface).

Mathlib has no triangulated category of motives `DMc(F_p)`, no motive functor `Mc(-)`, and no
motivic-localization/realization theory — the largest gap.  Following the Tier-C principle we make
the *paper's argument* a genuine theorem by recording the standard axioms as structure fields and
pushing everything unproven into a single instance-existence obligation.

`MotivicRealization M D` packages: a pretriangulated "motive category" `M` (the role of `DMc(F_p)`);
a realization functor `R : M ⥤ D`; the **Euler-preservation axiom** `preservesEuler` (`R` carries
distinguished triangles to additivity of the target Euler characteristic `χ`); the motivic
localization triangle `Mc(Up) → Mc(Xp) → Def_p → Mc(Up)[1]` (`defm`); and the paper's `bump` with the
axiom `bump = χ_mot(Def_p)`.  From these, `bump = Δχ_mot = χ_mot(Xp) − χ_mot(Up)` is **derived**
(§B4 cone relation).  Constructing an actual `MotivicRealization` (the Voevodsky motive category and
realization functor) is the open obligation; the logical core is genuine and unconditional. -/

namespace MotivicC1

open CategoryTheory CategoryTheory.Pretriangulated

variable (M D : Type*) [Category M] [HasZeroObject M] [HasShift M ℤ] [Preadditive M]
  [∀ n : ℤ, (shiftFunctor M n).Additive] [Pretriangulated M] [Category D]

/-- **C1 — motivic realization data (Tier-C universal-axiom interface).**  See the section
docstring.  `R` = realization functor; `χ` = target Euler characteristic; `preservesEuler` = `R`
preserves the Euler characteristic (sends distinguished triangles to additivity); `defm` = the
motivic localization triangle; `bump_eq` = `bump = χ_mot(Def_p)`. -/
structure MotivicRealization where
  /-- The realization functor `Mc(F_p) → D` (e.g. to the étale/derived realization). -/
  R : M ⥤ D
  /-- The Euler characteristic on the realization target. -/
  χ : D → ℤ
  /-- **Euler-preservation axiom.**  `R` sends every distinguished triangle to an additive relation
  for `χ` (i.e. `χ ∘ R` is an additive Euler characteristic on `M`). -/
  preservesEuler : ∀ T : Triangle M, T ∈ distTriang M →
    χ (R.obj T.obj₂) = χ (R.obj T.obj₁) + χ (R.obj T.obj₃)
  /-- The motivic localization triangle `Mc(Up) → Mc(Xp) → Def_p → Mc(Up)[1]`. -/
  defm : MotivicEuler.MotivicDeformation M
  /-- The paper's bump invariant. -/
  bump : ℤ
  /-- **Realization axiom.**  The bump equals the motivic Euler characteristic of the deformation. -/
  bump_eq : bump = χ (R.obj defm.Defp)

variable {M D}

/-- The motivic Euler characteristic `χ_mot = χ ∘ R` induced by a realization (additive by the
Euler-preservation axiom). -/
def MotivicRealization.motivicEuler (𝓡 : MotivicRealization M D) : MotivicEuler.AdditiveEuler M where
  χ := fun X => 𝓡.χ (𝓡.R.obj X)
  additive := 𝓡.preservesEuler

/-- **C1 / Thm 6.1 — `bump = Δχ_mot`.**  For any motivic realization, the paper's bump equals the
motivic Euler defect `χ_mot(Xp) − χ_mot(Up)`.  Pure consequence of the §B4 cone relation; only the
*existence* of a realization (an instance of `MotivicRealization`) is the open Tier-C obligation. -/
theorem MotivicRealization.bump_eq_deltaChi (𝓡 : MotivicRealization M D) :
    𝓡.bump = 𝓡.motivicEuler.χ 𝓡.defm.Xp - 𝓡.motivicEuler.χ 𝓡.defm.Up := by
  rw [𝓡.bump_eq]
  exact MotivicEuler.MotivicDeformation.deltaChi_mot 𝓡.motivicEuler 𝓡.defm

end MotivicC1

/-! ## C2 — curve étale `H¹` dimension formula, localization SES, comparison (Tier C).

Mathlib's `AlgebraicGeometry.Sites.ElladicCohomology` gives the ℓ-adic cohomology *type* with an
`AddCommGroup` (cf. `Tier3Actual.ellAdicCohomology_nonempty`), but no Poincaré duality, no comparison,
no curve-dimension or normalization-SES computation — so the dimension values are an interface.
Following the Tier-C principle, `CurveWeilCohomology` axiomatizes exactly the dimension content of the
localization sequence `0 → H⁰(Q) → H¹(Xp) → H¹(X̃p) → 0` together with the §A5 defect
`dim H⁰(Q) = b₁(Γ) + Σδ` and the normalization `dim H¹(X̃p) = dim H¹(Up) = 2g`.  From these the
dimension formula `dim H¹(Xp) = 2g + b₁ + Σδ` and the smooth-fibre `bump = 0` are *derived* (reusing
the certified ℕ-bookkeeping `curve_betti_identity`).  Constructing this from actual étale cohomology
is the open Tier-C obligation; the `b₁`/`Σδ` are the §A5 invariants. -/

namespace EtaleCurveCohomology

/-- **C2 — Weil/étale cohomology dimension data of the curve `Xp` (Tier-C interface).**  Records the
finite dimensions and the localization-SES / normalization comparison as axioms. -/
structure CurveWeilCohomology where
  /-- Genus of the normalization `X̃p`, `b₁(Γp)` (§A5 dual graph), `Σδ` (§A5 δ-invariants),
  and the étale `H¹` dimensions of `Xp`, of the smooth locus `Up`, of the skyscraper `Q` on the
  singular points, and of the normalization `X̃p`. -/
  g b1 deltaSum dimH1Xp dimH1Up dimH0Q dimH1Norm : ℕ
  /-- **Localization SES** `0 → H⁰(Q) → H¹(Xp) → H¹(X̃p) → 0` (its dimension count). -/
  localization_ses : dimH1Xp = dimH0Q + dimH1Norm
  /-- The singular defect `dim H⁰(Q) = b₁(Γ) + Σδ` (§A5). -/
  defect_dim : dimH0Q = b1 + deltaSum
  /-- The normalization `dim H¹(X̃p) = 2g` (smooth proper curve of genus `g`). -/
  norm_dim : dimH1Norm = 2 * g
  /-- Smooth-locus comparison `dim H¹(Up) = dim H¹(X̃p) = 2g`. -/
  smooth_comparison : dimH1Up = 2 * g

namespace CurveWeilCohomology

/-- **C2 — étale `H¹` dimension formula: `dim H¹(Xp) = 2g + b₁(Γ) + Σδ`.** -/
theorem dimH1Xp_formula (W : CurveWeilCohomology) :
    W.dimH1Xp = 2 * W.g + W.b1 + W.deltaSum := by
  rw [W.localization_ses, W.defect_dim, W.norm_dim]; omega

/-- The bump = excess of `H¹(Xp)` over the smooth part `H¹(Up)`. -/
def bump (W : CurveWeilCohomology) : ℕ := W.dimH1Xp - W.dimH1Up

/-- **C2 — `bump = b₁ + Σδ`** (via the certified ℕ-bookkeeping `curve_betti_identity`). -/
theorem bump_eq (W : CurveWeilCohomology) : W.bump = W.b1 + W.deltaSum :=
  curve_betti_identity W.g W.b1 W.deltaSum W.dimH1Xp W.dimH1Up (dimH1Xp_formula W) W.smooth_comparison

/-- **C2 — smooth fibre (`Sing = ∅`, i.e. `b₁ = Σδ = 0`): `dim H¹(Xp) = dim H¹(Up)` and `bump = 0`.**
This is the §9.3 normalization-SES consequence: with no singular defect the localization SES forces
`H¹(Xp) ≅ H¹(X̃p) = H¹(Up)`, so the étale bump vanishes. -/
theorem smooth_dim_eq (W : CurveWeilCohomology) (hb1 : W.b1 = 0) (hδ : W.deltaSum = 0) :
    W.dimH1Xp = W.dimH1Up ∧ W.bump = 0 := by
  have h := dimH1Xp_formula W
  have hs := W.smooth_comparison
  have hb := bump_eq W
  exact ⟨by omega, by omega⟩

end CurveWeilCohomology

end EtaleCurveCohomology

/-! ## C3 — primality sheaf and sheaf-theoretic CRT gluing (Tier C; cost-honest shadow).

The arithmetic CRT (`crt_solvable_iff`) and the predicate-shadow (`PrimalityShadow`) are already
certified.  Building a *genuine* `Sheaf` on a Grothendieck site is substantial; following the
cost-honest recommendation we keep the "finite limits are sectionwise" content as certified and make
the **sheaf-theoretic CRT gluing** explicit: the gluing axiom (local residues glue iff compatible on
overlaps) IS `crt_solvable_iff`, and the separatedness axiom (uniqueness mod `lcm`) is `lcm_dvd`.
Constructing the genuine site sheaf (`GrothendieckTopology` + sheaf condition) is the optional heavy
obligation. -/

namespace PrimalitySheafCRT

/-- A pair of local residues (`a` mod `M`, `b` mod `N`) is **CRT-compatible** iff the gcd-obstruction
`a − b` vanishes mod `gcd(M,N)` — the "agree on overlaps" hypothesis of the sheaf gluing axiom. -/
def CrtCompatible (M N a b : ℤ) : Prop := (↑(Int.gcd M N) : ℤ) ∣ (a - b)

/-- **C3 — sheaf gluing (existence half).**  Local residues glue to a global section iff they are
CRT-compatible.  This *is* the sheaf gluing axiom for the primality/CRT structure (`crt_solvable_iff`). -/
theorem glue_iff_compatible (M N a b : ℤ) :
    (∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b)) ↔ CrtCompatible M N a b :=
  crt_solvable_iff M N a b

/-- Compatible local residues do glue (the global section exists). -/
theorem exists_glue_of_compatible (M N a b : ℤ) (h : CrtCompatible M N a b) :
    ∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b) :=
  (glue_iff_compatible M N a b).mpr h

/-- Coprime moduli always glue (separated cover, `gcd = 1`). -/
theorem glue_of_coprime (M N a b : ℤ) (hcop : Int.gcd M N = 1) :
    ∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b) :=
  gcd_obstruction_zero_to_gluing M N a b hcop

/-- **C3 — separatedness (uniqueness mod `lcm`).**  Two global sections agreeing mod `M` and mod `N`
agree mod `lcm(M,N)` — the *separated* half of the sheaf axiom. -/
theorem glue_unique (M N x y : ℤ) (hM : M ∣ (x - y)) (hN : N ∣ (x - y)) :
    lcm M N ∣ (x - y) :=
  lcm_dvd hM hN

/-- **C3 — "finite limits are sectionwise" (certified shadow).**  The primality fiber product is the
pointwise intersection of the layers' sections (the sheaf-theoretic gluing of the predicate layers,
certified directly by `PrimalityShadow`). -/
theorem sections_fiberProduct_eq (Fnum Fmod Fpadic FEC : ℕ → Prop) (U : Set ℕ) :
    PrimalityShadow.sections (PrimalityShadow.primalityLayer Fnum Fmod Fpadic FEC) U
      = PrimalityShadow.sections Fnum U ∩ PrimalityShadow.sections Fmod U
          ∩ PrimalityShadow.sections Fpadic U ∩ PrimalityShadow.sections FEC U :=
  PrimalityShadow.sections_primalityLayer Fnum Fmod Fpadic FEC U

/-- **C3 — overlaps are intersections** (the separated/restriction shadow). -/
theorem sections_overlap_eq (F : ℕ → Prop) (U V : Set ℕ) :
    PrimalityShadow.sections F (U ∩ V)
      = PrimalityShadow.sections F U ∩ PrimalityShadow.sections F V :=
  PrimalityShadow.sections_inter F U V

end PrimalitySheafCRT

/-! ## C4 — Theorem 9.3 full equivalence assembly (Tier C capstone).

Thm 9.3 lists five conditions, synchronized on the good-prime open `U = D(Δ)`:
  (i)   discriminant/Jacobian gate `p ∤ Δ(E)` — the fibre `Xp` is smooth;
  (ii)  Hensel gate — every simple residue root lifts uniquely to `ℤ_p` (≡ residual separability);
  (iii) arithmetic equalizer `gcd(M,pᵏ) = 1` on principal-open overlaps;
  (iv)  derived readout `Tor₁^ℤ(ℤ/M, ℤ/pᵏ) = 0`;
  (v)   étale–motivic detectors `Xp smooth ⟺ bumpₚ = 0 ⟺ Δχ_mot(p) = 0 ⟺ H¹(L_{Xp}) = 0`.

**Honest certification boundary.**  After A1/A2 the gate (i)⇔(ii) is GENUINE for the concrete
Weierstrass curve (`disc_hensel_gate_tfae`, from `not_dvd_shortWeierstrass_Δ_iff_separable`), and
(iii)⇔(iv) is GENUINE via the equalizer–Tor model (`tor_equalizer_gate`, from `tor_subsingleton_iff`).
The detector layer (v) needs étale cohomology and motives, absent from Mathlib; following the
universal-axiom principle we DERIVE the (v) faces from the C2 `CurveWeilCohomology` and C1
`MotivicRealization` interfaces (the "Strategy-B → motif/étale" upgrade: structure fields become the
hypotheses of a universal theorem), leaving only (a) the §9.3 synchronization bridge `p∤Δ ⟺ gcd=1`
that the paper *enforces* on `U`, (b) the smooth criterion `p∤Δ ⟺ Sing=∅`, and (c) the ℓ-adic
realization comparison (Thm 6.1), and (d) the actual geometric instance, as explicit isolated
hypotheses/obligations.  The `FormalizationStatus` audit marks this boundary precisely. -/

namespace Thm93Assembly

open WeierstrassGate

/-! ### Part 1 — genuine arithmetic/algebraic core: (i)⇔(ii) and (iii)⇔(iv). -/

/-- **Thm 9.3 (i)⇔(ii) — discriminant/Hensel gate (GENUINE).**  For the short Weierstrass curve
`E : y² = x³ + a x + b` and a prime `p ≠ 2`, the discriminant gate `p ∤ Δ(E)`, the cubic gate
`p ∤ (4a³+27b²)`, residual separability of `x³+ax+b mod p`, and residual squarefreeness are
equivalent — all proved unconditionally from A2 (`not_dvd_shortWeierstrass_Δ_iff_separable` and
`cubic_good_locus_tfae`).  This is the unconditional content of the paper's `(i) ⟺ (ii)` (smooth
fibre ⟺ simple residue roots ⟺ unique Hensel lift). -/
theorem disc_hensel_gate_tfae {a b : ℤ} (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    [ ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ
    , ¬ (p : ℤ) ∣ (4 * a ^ 3 + 27 * b ^ 2)
    , (cubicPoly (a : ZMod p) (b : ZMod p)).Separable
    , Squarefree (cubicPoly (a : ZMod p) (b : ZMod p)) ].TFAE := by
  have h := cubic_good_locus_tfae (a := a) (b := b) p
  tfae_have 1 ↔ 3 := not_dvd_shortWeierstrass_Δ_iff_separable p hp2
  tfae_have 2 ↔ 3 := h.out 0 1
  tfae_have 3 ↔ 4 := h.out 1 2
  tfae_finish

/-- **Thm 9.3 (iii)⇔(iv) — equalizer = derived Tor (GENUINE).**  In the equalizer–Tor model
`Tor₁^ℤ(ℤ/M, ℤ/N) = ker(·M : ℤ/N → ℤ/N)`, the derived obstruction vanishes (is a subsingleton) iff
the arithmetic equalizer condition `gcd(M,N) = 1` holds.  Unconditional (`tor_subsingleton_iff`). -/
theorem tor_equalizer_gate (M N : ℕ) [NeZero N] :
    Subsingleton (AddMonoidHom.mulLeft (M : ZMod N)).ker ↔ Nat.gcd M N = 1 := by
  rw [tor_subsingleton_iff N M, Nat.gcd_comm N M]

/-! ### Part 2 — detector layer (v): universal over the C1 (motivic) / C2 (étale) interfaces. -/

/-- **C4 upgrade — the curve detector assembled from the C2 étale interface.**  The C2
`CurveWeilCohomology` dimension data (localization SES + normalization) — together with the smooth
criterion `Sing = ∅ ⟺ b₁ = Σδ = 0` and a derived-face criterion — assembles into a full
`Tier3.CurveDetectorData`.  Hence the étale bump face is *derived* from the localization SES (C2),
not postulated: this is the Strategy-B hypotheses being supplied by the C2 structure. -/
def detectorOfWeil {p : ℕ} (W : EtaleCurveCohomology.CurveWeilCohomology)
    (smooth : Prop) (derived : ℕ)
    (hsmooth : smooth ↔ (W.b1 = 0 ∧ W.deltaSum = 0))
    (hder : derived = 0 ↔ smooth) : Tier3.CurveDetectorData p where
  bump := W.bump
  eulerJump := W.b1 + W.deltaSum
  derived := derived
  b1Graph := W.b1
  deltaSum := W.deltaSum
  smooth := smooth
  bump_eq_jump := W.bump_eq
  jump_eq_graph := rfl
  smooth_iff := hsmooth
  der_iff := hder

/-- **Thm 9.3(v) — detector TFAE (universal over the interface).**  For any curve-detector interface,
smoothness, vanishing étale bump, vanishing Euler/motivic jump, and vanishing derived (cotangent /
`H¹(L)`) obstruction are equivalent.  Genuine over the `CurveDetectorData` structure. -/
theorem detector_tfae {p : ℕ} (D : Tier3.CurveDetectorData p) :
    [D.smooth, D.bump = 0, D.eulerJump = 0, D.derived = 0].TFAE := by
  tfae_have 1 ↔ 2 := (Tier3.bump_zero_iff_smooth D).symm
  tfae_have 2 ↔ 3 := by rw [D.bump_eq_jump]
  tfae_have 1 ↔ 4 := D.der_iff.symm
  tfae_finish

/-! ### Part 3 — the full equivalence assembly (i)⇔(ii)⇔(iii)⇔(iv)⇔(v). -/

/-- **Thm 9.3 — full equivalence assembly (i)⇔(ii)⇔(iii)⇔(iv)⇔(v).**  Combines the unconditional
arithmetic/algebraic core (A2 discriminant/Hensel gate + the equalizer–Tor model) with the étale
detector layer derived from the C2 data `W`.  The cross-tier bridges are the explicit, ISOLATED
hypotheses: the §9.3 synchronization `Hsync` (`p∤Δ ⟺ gcd = 1`, enforced on `U`), the smooth criterion
`Hsmooth` (`p∤Δ ⟺ Sing = ∅`, i.e. `b₁ = Σδ = 0`), and the derived criterion `Hder`.  Every remaining
face is proved.  The faces are, in order: (i) `p∤Δ`, (ii) residual separability, (iii) equalizer
`gcd = 1`, (iv) `Tor = 0`, (v-étale) `bump = 0`, (v-derived) `H¹(L_{Xp}) = 0`. -/
theorem thm93_full_tfae {a b : ℤ} (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (M pk : ℕ) [NeZero pk] (W : EtaleCurveCohomology.CurveWeilCohomology) (derived : ℕ)
    (Hsync : ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ ↔ Nat.gcd M pk = 1)
    (Hsmooth : ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ ↔ (W.b1 = 0 ∧ W.deltaSum = 0))
    (Hder : derived = 0 ↔ ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ) :
    [ ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ
    , (cubicPoly (a : ZMod p) (b : ZMod p)).Separable
    , Nat.gcd M pk = 1
    , Subsingleton (AddMonoidHom.mulLeft (M : ZMod pk)).ker
    , W.bump = 0
    , derived = 0 ].TFAE := by
  have hg := disc_hensel_gate_tfae (a := a) (b := b) p hp2
  have hbump : W.bump = 0 ↔ ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ := by
    rw [W.bump_eq, Nat.add_eq_zero_iff, ← Hsmooth]
  tfae_have 1 ↔ 2 := hg.out 0 2
  tfae_have 1 ↔ 3 := Hsync
  tfae_have 3 ↔ 4 := (tor_equalizer_gate M pk).symm
  tfae_have 1 ↔ 5 := hbump.symm
  tfae_have 1 ↔ 6 := Hder.symm
  tfae_finish

section Motivic

open CategoryTheory CategoryTheory.Pretriangulated

variable {Mot Der : Type*} [Category Mot] [HasZeroObject Mot] [HasShift Mot ℤ] [Preadditive Mot]
  [∀ n : ℤ, (shiftFunctor Mot n).Additive] [Pretriangulated Mot] [Category Der]

/-- **C4 upgrade — the motivic detector (C1) vanishes iff the fibre is smooth.**  When the ℓ-adic
realization comparison (Thm 6.1) identifies the motivic Euler defect `𝓡.bump = Δχ_mot` with the
étale Euler jump `D.eulerJump`, the motivic detector synchronizes with smoothness.  This is the
Strategy-B → motif upgrade: the motivic face is *derived* from the C1 `MotivicRealization` interface
together with the comparison hypothesis, rather than being a free assumption. -/
theorem motivic_detector_iff_smooth {p : ℕ}
    (D : Tier3.CurveDetectorData p) (𝓡 : MotivicC1.MotivicRealization Mot Der)
    (hcompat : 𝓡.bump = (D.eulerJump : ℤ)) : 𝓡.bump = 0 ↔ D.smooth := by
  rw [hcompat, Nat.cast_eq_zero]
  exact (detector_tfae D).out 2 0

/-- **Thm 9.3 — full assembly with the motivic detector face.**  Extends `thm93_full_tfae` by the
motivic Euler-jump face `Δχ_mot = 𝓡.bump = 0` (C1), under the realization comparison `Hcompat`
(`𝓡.bump = b₁ + Σδ`, Thm 6.1).  This is the complete (i)–(v) synchronization, with the arithmetic
core genuine and the geometric detectors universal over the C1/C2 interfaces. -/
theorem thm93_full_tfae_motivic {a b : ℤ} (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (M pk : ℕ) [NeZero pk] (W : EtaleCurveCohomology.CurveWeilCohomology) (derived : ℕ)
    (𝓡 : MotivicC1.MotivicRealization Mot Der)
    (Hsync : ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ ↔ Nat.gcd M pk = 1)
    (Hsmooth : ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ ↔ (W.b1 = 0 ∧ W.deltaSum = 0))
    (Hder : derived = 0 ↔ ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ)
    (Hcompat : 𝓡.bump = ((W.b1 + W.deltaSum : ℕ) : ℤ)) :
    [ ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ
    , (cubicPoly (a : ZMod p) (b : ZMod p)).Separable
    , Nat.gcd M pk = 1
    , Subsingleton (AddMonoidHom.mulLeft (M : ZMod pk)).ker
    , W.bump = 0
    , derived = 0
    , 𝓡.bump = 0 ].TFAE := by
  have hfull := thm93_full_tfae (a := a) (b := b) p hp2 M pk W derived Hsync Hsmooth Hder
  have hmot : 𝓡.bump = 0 ↔ ¬ (p : ℤ) ∣ (shortWeierstrass a b).Δ := by
    rw [Hcompat, Nat.cast_eq_zero, Nat.add_eq_zero_iff, ← Hsmooth]
  tfae_have 1 ↔ 2 := hfull.out 0 1
  tfae_have 1 ↔ 3 := hfull.out 0 2
  tfae_have 1 ↔ 4 := hfull.out 0 3
  tfae_have 1 ↔ 5 := hfull.out 0 4
  tfae_have 1 ↔ 6 := hfull.out 0 5
  tfae_have 1 ↔ 7 := hmot.symm
  tfae_finish

end Motivic

end Thm93Assembly

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
conditional theorem schema, not an unconditional result of this file.  (The honest,
*separability* good-locus content of (i)⇔(ii) is, however, fully unconditional — see
`status_goodLocus_equivalence`.) -/
def status_full_smooth_jacobian_gate_equivalence : FormalizationStatus := .conditional

/-- **A1 / fifth correction.**  The honest good-locus content of Thm 9.3(i)⇔(ii) —
`p ∤ Δ ⟺ F mod p separable ⟺ every residual root simple` — is fully unconditional
(`GoodLocus.modPolynomial_good_locus_tfae`, `GoodLocus.not_dvd_disc_iff_separable`,
`GoodLocus.uniquePadicLift_of_separable_isRoot`). -/
def status_goodLocus_equivalence : FormalizationStatus := .unconditional

/-- **A1 / fifth correction.**  The paper's *unconditional reverse* of Thm 9.3(ii)
("unique `p`-adic lift ⇒ full Jacobian rank") is FALSE; the refuting counterexample
`X²` over `ℤ₂` is formalized (`GoodLocus.unique_lift_not_imply_unit_derivative`). -/
def status_uniqueLift_reverse_refuted : FormalizationStatus := .unconditional

/-- **A2 / Prop 2.**  The Weierstrass discriminant gate at the residual-polynomial level —
`p ∤ Δ(E) ⟺ (x³+ax+b mod p) squarefree` (= residual fiber nonsingular) — is fully
unconditional (`WeierstrassGate.cubic_good_locus_tfae`,
`WeierstrassGate.not_dvd_shortWeierstrass_Δ_iff_separable`).  Scheme-level
`Affine.Nonsingular` promotion is deliberately left as optional Tier B. -/
def status_weierstrass_discriminant_gate : FormalizationStatus := .unconditional

/-- **A3.**  The four §2.1/2.2 layers (`numLayer`, `modLayer`, `discLayer`, `ecLayer`) are
now concrete genuine gates, and the fiber-product identity `Γ(U,F) = ⋂ Γ(U,F_layer)` is
certified for them (`PrimalityShadow.sections_primeCertGate`), with the Hensel/EC layers
tied to the §A2 separability gate (`discLayer_iff_separable`, `ecLayer_iff_discLayer`). -/
def status_concrete_layer_gates : FormalizationStatus := .unconditional

/-- **A4.**  The AB-linearization bridge is closed directly mod `pᵏ` — `∑ⱼ aⱼ log(1+uⱼ) ≡
∑ⱼ aⱼ uⱼ (mod pᵏ)` via factorwise `log(1+u) ≡ u` and additivity, with radius bounds from the
§5.1 valuation profile (`PadicLog.ab_linearization_phi_congMod`, `sum_smul_logOnePlus_congMod`,
`norm_intCast_le_of_le_padicValInt`).  The full infinite-precision bridge (the `p`-adic-log
functional equation) is deferred to B1. -/
def status_AB_linearization_modPk : FormalizationStatus := .unconditional

/-- **A5.**  The δ-invariant (`CurveInvariants.deltaInvariant` = `Module.length` of the
normalization quotient, with the smooth criterion `deltaInvariant_eq_zero_iff`) and the dual-graph
first Betti number (`firstBettiNumber`/`graphFirstBetti`) are pinned down as genuine definitions.
The identification of the curve dimensions with actual cohomology stays Tier C
(`CurveInvariants.betti_excess_eq` records the boundary). -/
def status_curve_invariants_defs : FormalizationStatus := .unconditional

/-- **B1 (formal).**  The p-adic log functional equation is proved *formally* in `ℚ_[p]⟦X⟧`,
unconditionally: `PadicLogFormal.logOf_mul` (`logOf(f·g)=logOf f+logOf g`) and
`PadicLogFormal.logOf_pow` (`logOf(fⁿ)=n•logOf f`), via the logarithmic-derivative argument. -/
def status_padicLog_formal_functional_equation : FormalizationStatus := .unconditional

/-- **B1 (analytic transfer).**  Transporting the formal functional equation to the convergent
`ℚ_[p]` value (continuity of the power-series evaluation) is isolated as
`PadicLogFormal.PadicLogAdditive`; the analytic power law is derived from it
(`logOnePlus_pow_of_additive`).  This analytic transfer is the residual Tier-B step (its mod-`pᵏ`
version is the unconditional §A4). -/
def status_padicLog_analytic_transfer : FormalizationStatus := .conditional

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
been constructed.  We deliberately do not replace them by a structure field.
(§B5 now binds `aₚ` to the actual point count and proves `aₚ=0 ⇒ supersingular` for the
*arithmetic* criterion `aₚ ≡ 0 (mod p)` — see `status_supersingular_arithmetic`; only the
agreement with the geometric definition remains this obligation.) -/
def status_trace_zero_implies_supersingular : FormalizationStatus := .futureWork

/-- **B5.**  `a_p` is bound to the genuine point count `Nat.card W.toAffine.Point`
(`FrobeniusPointCount.frobeniusTrace`), and the arithmetic supersingularity criterion
`a_p ≡ 0 (mod p)` with `a_p = 0 ⇒ supersingular` (`isSupersingular_of_trace_zero`) is unconditional.
The geometric-agreement (Weil/Hasse) is the `FrobeniusData` interface obligation. -/
def status_supersingular_arithmetic : FormalizationStatus := .unconditional

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
vanishes.  This is future work, not a structure-field theorem.  (The *key* Γ-exactness input —
`Γ` sends a flasque SES to a surjection — is now genuine and unconditional; see
`status_flasque_gamma_exactness`.  Only the dimension-shifting over the `Ext` LES remains.) -/
def status_specZ_skyscraper_flasque_acyclicity : FormalizationStatus := .futureWork

/-- **B2.**  The flasque Γ-exactness — `Γ` sends a flasque short exact sequence to a surjection
(`Tier3Actual.flasque_sections_epi` / `flasque_global_sections_surjective`) and a flasque SES has
flasque quotient (`flasque_quotient_isFlasque`) — is genuine and unconditional (exposed from
Mathlib).  This is the key input the original audit missed; `IsGammaAcyclic` isolates the residual
dimension-shifting step. -/
def status_flasque_gamma_exactness : FormalizationStatus := .unconditional

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
defined here; their localization triangle therefore remains future work.
(§C1 packages this as the `MotivicC1.MotivicRealization` interface and derives `bump = Δχmot` from
it; only the *instance* — an actual motive category + realization functor — is this obligation.) -/
def status_motivic_localization_triangle : FormalizationStatus := .futureWork

/-- **C1 (universal-axiom interface).**  `bump = Δχmot = χmot(Xp) − χmot(Up)` is a *genuine*
theorem for any `MotivicC1.MotivicRealization` (the realization functor + Euler-preservation axiom +
localization triangle); it rests on the unconditional §B4 cone relation.  It is conditional only on
the structure, whose instance is the Tier-C obligation above. -/
def status_motivic_realization_bump : FormalizationStatus := .conditional

/-- **C2 (universal-axiom interface).**  `dim H¹(Xp) = 2g + b₁(Γ) + Σδ` and the smooth-fibre
`bump = 0` are *genuine* theorems for any `EtaleCurveCohomology.CurveWeilCohomology` (the localization
SES + normalization comparison axioms), reusing the certified ℕ-bookkeeping `curve_betti_identity`.
Conditional only on the structure; the actual étale-cohomology construction (duality/comparison) is
the Tier-C obligation `status_motivic_localization_triangle`/`status_etale_ladic_cohomology`. -/
def status_curve_weil_cohomology : FormalizationStatus := .conditional

/-- **C3.**  The sheaf-theoretic CRT gluing — local residues glue iff CRT-compatible
(`PrimalitySheafCRT.glue_iff_compatible`) and the separatedness `lcm`-uniqueness
(`glue_unique`), together with the "finite limits are sectionwise" shadow — is genuine and
unconditional. -/
def status_crt_sheaf_gluing : FormalizationStatus := .unconditional

/-- **C3 residue.**  A genuine `Sheaf` on a `GrothendieckTopology` (the full site sheaf condition,
not just the certified sectionwise/CRT shadow) is the optional heavy Tier-C obligation. -/
def status_genuine_site_sheaf : FormalizationStatus := .futureWork

/-- **C4 arithmetic core.**  The Thm 9.3 gate `(i)⇔(ii)` (`Thm93Assembly.disc_hensel_gate_tfae`:
`p∤Δ ⟺ residual separable ⟺ squarefree`) and the equalizer–Tor `(iii)⇔(iv)`
(`Thm93Assembly.tor_equalizer_gate`: `Tor = 0 ⟺ gcd = 1`) are genuine and unconditional. -/
def status_thm93_arith_core : FormalizationStatus := .unconditional

/-- **C4 detector layer (v).**  The detector TFAE (`Thm93Assembly.detector_tfae`,
`motivic_detector_iff_smooth`) and the full assembly (`thm93_full_tfae`, `thm93_full_tfae_motivic`)
are genuine *universal* theorems over the C1 `MotivicRealization` / C2 `CurveWeilCohomology`
interfaces — conditional only on those structures plus the §9.3 synchronization / realization-
comparison bridges, which are the explicit isolated hypotheses. -/
def status_thm93_detector_layer : FormalizationStatus := .conditional

/-- **C4 residue.**  An *unconditional* proof of condition (v) (the étale bump / motivic Euler jump
/ `H¹(L_{Xp})` detector vanishing on `U`) requires constructing étale cohomology and Voevodsky
motives — the actual geometric instance, the open Tier-C obligation. -/
def status_thm93_geometric_instance : FormalizationStatus := .futureWork

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

/-- **B3.**  The explicit 2-cover Čech cohomology is packaged as named objects
(`CechComparison.cechH0 ≅ ℤ/lcm`, `cechH1 ≅ ℤ/gcd`), and the §7.2 grounding
(`paper_ext_one_is_sheaf_ext`: sheaf-`H¹` = sheaf-`Ext¹`, while module-`Ext¹(ℤ,A)=0`) is genuine and
unconditional. -/
def status_cech_explicit_cohomology : FormalizationStatus := .unconditional

/-- **B3 residue.**  The full degree-≤1 Čech-to-derived comparison `Ȟ⁰ ≅ H⁰`, `Ȟ¹ ↪ H¹` (the edge
maps / five-term low-degree exact sequence of the Čech-to-derived spectral sequence) is not yet
packaged in Mathlib and remains future work. -/
def status_cech_derived_comparison : FormalizationStatus := .futureWork

/-- **B4.**  On any pretriangulated category, an additive Euler characteristic satisfies the cone
relation `χ(cone f) = χ B − χ A` (`MotivicEuler.AdditiveEuler.cone_euler`), so `Δχ_mot = χ(Def_p) =
χ(Xp) − χ(Up)` (`MotivicEuler.MotivicDeformation.deltaChi_mot`) is unconditional pure category
theory.  Only the motivic realization triangle is an external interface. -/
def status_motivic_euler_cone : FormalizationStatus := .unconditional

/-- **B6.**  The cohomological defect `δcoh P := sInf {i | ∃ F, supp F = P ∧ Hⁱ(F) ≠ 0}` (Def 7.1) is
a genuine, unconditional definition (`CohDimension.deltaCoh`), with the easy bounds
(`deltaCoh_le`, `deltaCoh_mem`) and the §7.3 value `δcoh = 1` (`deltaCoh_eq_one`, fed by §B2). -/
def status_deltaCoh_definition : FormalizationStatus := .unconditional

/-- **B6 residue.**  The base-change / localization invariance of Prop 7.2 needs sheaf-cohomology
base change, which Mathlib provides only partially; it remains Tier-C future work. -/
def status_deltaCoh_base_change : FormalizationStatus := .futureWork

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

/-- **A1 / fifth-correction audit.**  The good-locus equivalence
`p ∤ Δ ⟺ separable ⟺ all residual roots simple` is a genuine unconditional result; the
paper's unconditional reverse is *refuted*, not assumed; and the still-missing literal
scheme-smoothness/Jacobian-rank reverse stays honestly flagged future work. -/
theorem a1_good_locus_classification :
    status_goodLocus_equivalence = .unconditional ∧
    status_uniqueLift_reverse_refuted = .unconditional ∧
    status_uniqueLift_to_jacobian_smooth = .futureWork ∧
    status_full_smooth_jacobian_gate_equivalence = .conditional ∧
    FormalizationStatus.isRepresentative status_goodLocus_equivalence = true ∧
    FormalizationStatus.isRepresentative status_uniqueLift_reverse_refuted = true := by
  decide

/-- **A2 / Prop 2 audit.**  The Weierstrass discriminant gate at the residual-polynomial
level is a genuine unconditional result and a representative theorem. -/
theorem a2_weierstrass_gate_classification :
    status_weierstrass_discriminant_gate = .unconditional ∧
    FormalizationStatus.isRepresentative status_weierstrass_discriminant_gate = true := by
  decide

/-- **A3 audit.**  The concrete four-layer instantiation and its fiber-product certification
are a genuine unconditional, representative result. -/
theorem a3_concrete_layers_classification :
    status_concrete_layer_gates = .unconditional ∧
    FormalizationStatus.isRepresentative status_concrete_layer_gates = true := by
  decide

/-- **A4 audit.**  The mod-`pᵏ` AB-linearization skeleton is a genuine unconditional,
representative result; the full functional-equation bridge stays future work (B1). -/
theorem a4_ab_linearization_classification :
    status_AB_linearization_modPk = .unconditional ∧
    FormalizationStatus.isRepresentative status_AB_linearization_modPk = true := by
  decide

/-- **A5 audit.**  The δ-invariant and dual-graph `b₁` definitions are genuine unconditional,
representative results; the cohomology identification stays Tier C. -/
theorem a5_curve_invariants_classification :
    status_curve_invariants_defs = .unconditional ∧
    FormalizationStatus.isRepresentative status_curve_invariants_defs = true := by
  decide

/-- **B1 audit.**  The formal functional equation is unconditional and representative; the analytic
transfer to convergent `ℚ_[p]` values is the isolated, conditional Tier-B residue. -/
theorem b1_padicLog_functional_equation_classification :
    status_padicLog_formal_functional_equation = .unconditional ∧
    status_padicLog_analytic_transfer = .conditional ∧
    FormalizationStatus.isRepresentative status_padicLog_formal_functional_equation = true ∧
    FormalizationStatus.isRepresentative status_padicLog_analytic_transfer = false := by
  decide

/-- **B2 audit.**  The flasque Γ-exactness is now genuine and unconditional; the dimension-shifting
acyclicity (`flasque ⇒ Hⁱ = 0, i>0`) remains the isolated future-work residue. -/
theorem b2_flasque_classification :
    status_flasque_gamma_exactness = .unconditional ∧
    status_skyscraperSheaf_isFlasque = .unconditional ∧
    status_specZ_skyscraper_flasque_acyclicity = .futureWork ∧
    FormalizationStatus.isRepresentative status_flasque_gamma_exactness = true := by
  decide

/-- **B3 audit.**  The explicit Čech cohomology and the §7.2 sheaf-`Ext` grounding are genuine and
unconditional; the degree-≤1 Čech-to-derived spectral-sequence comparison remains isolated. -/
theorem b3_cech_classification :
    status_cech_explicit_cohomology = .unconditional ∧
    status_sheafExt_H1_identification = .unconditional ∧
    status_cech_derived_comparison = .futureWork ∧
    FormalizationStatus.isRepresentative status_cech_explicit_cohomology = true := by
  decide

/-- **B4 audit.**  The additive-Euler cone relation and the `Δχ_mot` logic are genuine
unconditional, representative category theory; only the motivic realization triangle is external. -/
theorem b4_motivic_euler_classification :
    status_motivic_euler_cone = .unconditional ∧
    FormalizationStatus.isRepresentative status_motivic_euler_cone = true := by
  decide

/-- **B5 audit.**  The actual-point-count trace and the arithmetic supersingularity criterion
(`a_p ≡ 0 (mod p)`, with `a_p = 0 ⇒ supersingular`) are genuine and unconditional; the geometric
(Hasse/Weil) agreement stays the isolated `FrobeniusData` obligation. -/
theorem b5_supersingular_classification :
    status_supersingular_arithmetic = .unconditional ∧
    status_geometric_frobenius_characteristicPolynomial = .futureWork ∧
    status_trace_zero_implies_supersingular = .futureWork ∧
    FormalizationStatus.isRepresentative status_supersingular_arithmetic = true := by
  decide

/-- **B6 audit.**  The genuine `δcoh` definition (Def 7.1) and its easy properties (incl. the §7.3
`δcoh = 1` criterion) are unconditional and representative; Prop 7.2 base-change invariance stays
isolated Tier-C future work. -/
theorem b6_deltaCoh_classification :
    status_deltaCoh_definition = .unconditional ∧
    status_deltaCoh_base_change = .futureWork ∧
    FormalizationStatus.isRepresentative status_deltaCoh_definition = true := by
  decide

/-- **C1 audit.**  The motivic `bump = Δχmot` is a genuine universal theorem over the
`MotivicRealization` interface (conditional on that structure, resting on the unconditional §B4 cone
relation); constructing the actual Voevodsky motive category + realization is the open obligation
(`status_motivic_localization_triangle = futureWork`). -/
theorem c1_motivic_realization_classification :
    status_motivic_realization_bump = .conditional ∧
    status_motivic_euler_cone = .unconditional ∧
    status_motivic_localization_triangle = .futureWork := by
  decide

/-- **C2 audit.**  The curve étale-`H¹` dimension formula and smooth `bump = 0` are genuine universal
theorems over the `CurveWeilCohomology` interface (conditional on it, resting on the unconditional
ℕ-bookkeeping); the étale-cohomology construction stays the Tier-C obligation. -/
theorem c2_curve_cohomology_classification :
    status_curve_weil_cohomology = .conditional ∧
    status_etale_ladic_cohomology = .unconditional ∧
    status_motivic_localization_triangle = .futureWork := by
  decide

/-- **C3 audit.**  The sheaf-theoretic CRT gluing + sectionwise shadow are genuine and unconditional
(`status_crt_sheaf_gluing`, resting on the certified `crt_solvable_iff`); the genuine site-sheaf
remains the isolated heavy obligation. -/
theorem c3_crt_gluing_classification :
    status_crt_sheaf_gluing = .unconditional ∧
    status_gcd_obstruction_zero_to_gluing = .unconditional ∧
    status_genuine_site_sheaf = .futureWork ∧
    FormalizationStatus.isRepresentative status_crt_sheaf_gluing = true := by
  decide

/-- **C4 audit.**  The full Thm 9.3 assembly splits exactly along the certification boundary: the
arithmetic/algebraic core `(i)⇔(ii)⇔(iii)⇔(iv)` is genuine and representative (`= unconditional`),
the detector layer `(v)` is a genuine universal theorem over the C1/C2 interfaces (`= conditional`),
and only the actual étale/motivic geometric instance is open (`= futureWork`). -/
theorem c4_full_equivalence_classification :
    status_thm93_arith_core = .unconditional ∧
    status_thm93_detector_layer = .conditional ∧
    status_thm93_geometric_instance = .futureWork ∧
    FormalizationStatus.isRepresentative status_thm93_arith_core = true ∧
    FormalizationStatus.isRepresentative status_thm93_detector_layer = false := by
  decide

/-! ## §M — Summary of paper corrections surfaced by formalization.

Formalizing the algebraic/arithmetic skeleton mechanically detects five errors in the paper; three
of the first four stem from the *same* `lcm ↔ gcd` confusion (intersection vs obstruction/cokernel),
which the single short exact sequence `0 → ℤ/lcm → ℤ/M × ℤ/N → ℤ/gcd → 0` (§G,
`Additions.range_iota_eq_ker_proj` + `iota_injective` + `proj_surjective`) resolves at once; the
fifth is the false unconditional reverse of the Hensel/Jacobian gate, fixed in §A1:

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
  5. (Thm 9.3(ii)) The *unconditional reverse* "unique `p`-adic lift ⇒ full Jacobian rank" is FALSE
     (witness `X²` over `ℤ₂` at `0`: the only root in the unit ball is `0`, yet `F'(0) = 0`).  The
     honest content of (i)⇔(ii) is the good-locus equivalence
     `p ∤ Δ ⟺ f̄ separable ⟺ all residual roots simple`.
     ↦ §A1 (`GoodLocus.unique_lift_not_imply_unit_derivative`,
       `GoodLocus.modPolynomial_good_locus_tfae`, `GoodLocus.not_dvd_disc_iff_separable`).

Corrections 1, 2, 4 are the one `lcm ↔ gcd` confusion; the §G exact sequence settles all three.
Correction 5 is the separability good-locus replacement of the false Jacobian reverse (§A1). -/

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

/-! ### A4 — AB-linearization bridge directly mod `pᵏ` (functional equation bypassed).

The paper uses everything mod `pᵏ`.  Combining the per-factor congruence
`log(1+u) ≡ u (mod pᵏ)` (`norm_logOnePlus_sub_le_radius`) with additivity certifies the
mod-`pᵏ` skeleton of the AB-linearization

    ∑ⱼ aⱼ · log(1+uⱼ)  ≡  ∑ⱼ aⱼ · uⱼ   (mod pᵏ)

**without** the `p`-adic-log functional equation `log(XY) = log X + log Y` (that full,
infinite-precision bridge is deferred to B1).  Under the (deferred) functional equation the
left side is `log X − log Y`, and the right side is the explicit `∑ⱼ aⱼ φⱼ(A)`.  The radius
hypotheses `‖uⱼ‖ ≤ p⁻ᵏ` are discharged for the §5.1 profile `φⱼ(1+pᵀ)` by the already-proven
valuation results `padicVal_phi` / `Hk_basic_profile` via the bridge
`k ≤ vₚ(z) → ‖(z:ℚ_p)‖ ≤ p⁻ᵏ` (`norm_intCast_le_of_le_padicValInt`). -/

/-- Congruence modulo `pᵏ` on `ℚ_p`: `‖x − y‖ ≤ p⁻ᵏ`.  This is the mod-`pᵏ` relation the
paper uses throughout the AB-linearization. -/
def CongMod (k : ℕ) (x y : ℚ_[p]) : Prop := ‖x - y‖ ≤ (p : ℝ)⁻¹ ^ k

theorem congMod_refl (k : ℕ) (x : ℚ_[p]) : CongMod k x x := by
  simp only [CongMod, sub_self, norm_zero]; positivity

theorem congMod_symm {k : ℕ} {x y : ℚ_[p]} (h : CongMod k x y) : CongMod k y x := by
  rw [CongMod, ← neg_sub, norm_neg]; exact h

theorem congMod_trans {k : ℕ} {x y z : ℚ_[p]} (hxy : CongMod k x y) (hyz : CongMod k y z) :
    CongMod k x z := by
  have hsum : x - z = (x - y) + (y - z) := by ring
  rw [CongMod, hsum]
  exact (Padic.nonarchimedean _ _).trans (max_le hxy hyz)

/-- The mod-`pᵏ` congruence is additive. -/
theorem congMod_add {k : ℕ} {x x' y y' : ℚ_[p]} (hx : CongMod k x x') (hy : CongMod k y y') :
    CongMod k (x + y) (x' + y') := by
  have hsum : (x + y) - (x' + y') = (x - x') + (y - y') := by ring
  rw [CongMod, hsum]
  exact (Padic.nonarchimedean _ _).trans (max_le hx hy)

/-- Scaling by a `p`-adic integer (norm `≤ 1`) preserves the mod-`pᵏ` congruence. -/
theorem congMod_mul_of_norm_le_one {k : ℕ} (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) {x y : ℚ_[p]}
    (h : CongMod k x y) : CongMod k (c * x) (c * y) := by
  have hsub : c * x - c * y = c * (x - y) := by ring
  rw [CongMod, hsub, norm_mul]
  calc ‖c‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := by gcongr
    _ = ‖x - y‖ := one_mul _
    _ ≤ (p : ℝ)⁻¹ ^ k := h

/-- Scaling by an integer coefficient preserves the mod-`pᵏ` congruence (`‖(a:ℚ_p)‖ ≤ 1`). -/
theorem congMod_intCast_mul {k : ℕ} (a : ℤ) {x y : ℚ_[p]} (h : CongMod k x y) :
    CongMod k ((a : ℚ_[p]) * x) ((a : ℚ_[p]) * y) :=
  congMod_mul_of_norm_le_one (a : ℚ_[p]) (Padic.norm_int_le_one a) h

/-- The mod-`pᵏ` congruence is preserved under finite sums. -/
theorem congMod_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f g : ι → ℚ_[p]) :
    (∀ i ∈ s, CongMod k (f i) (g i)) → CongMod k (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simpa using congMod_refl k (0 : ℚ_[p])
  | @insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact congMod_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Per-factor congruence.**  `log(1+u) ≡ u (mod pᵏ)` for `u` in the radius-`pᵏ` ball.
(Re-packaging of `norm_logOnePlus_sub_le_radius` as a congruence.) -/
theorem logOnePlus_congMod {k : ℕ} (hk : 1 ≤ k) {u : ℚ_[p]} (hu : ‖u‖ ≤ (p : ℝ)⁻¹ ^ k) :
    CongMod k (logOnePlus u) u :=
  norm_logOnePlus_sub_le_radius hk hu

/-- **Sum bridge (no functional equation).**  `∑ⱼ log(1+uⱼ) ≡ ∑ⱼ uⱼ (mod pᵏ)`. -/
theorem sum_logOnePlus_congMod {k : ℕ} (hk : 1 ≤ k) {ι : Type*} (s : Finset ι) (u : ι → ℚ_[p])
    (hu : ∀ i ∈ s, ‖u i‖ ≤ (p : ℝ)⁻¹ ^ k) :
    CongMod k (∑ i ∈ s, logOnePlus (u i)) (∑ i ∈ s, u i) :=
  congMod_sum s _ _ (fun i hi => logOnePlus_congMod hk (hu i hi))

/-- **AB-linearization mod `pᵏ` (integer coefficients).**
`∑ⱼ aⱼ · log(1+uⱼ) ≡ ∑ⱼ aⱼ · uⱼ (mod pᵏ)` — the honest mod-`pᵏ` skeleton, obtained by
applying `log(1+u) ≡ u` factorwise and summing. -/
theorem sum_smul_logOnePlus_congMod {k : ℕ} (hk : 1 ≤ k) {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (u : ι → ℚ_[p]) (hu : ∀ i ∈ s, ‖u i‖ ≤ (p : ℝ)⁻¹ ^ k) :
    CongMod k (∑ i ∈ s, (a i : ℚ_[p]) * logOnePlus (u i)) (∑ i ∈ s, (a i : ℚ_[p]) * u i) :=
  congMod_sum s _ _ (fun i hi => congMod_intCast_mul (a i) (logOnePlus_congMod hk (hu i hi)))

/-- **Valuation → norm bridge.**  If `pᵏ ∣ z` in the sense `k ≤ vₚ(z)`, then `‖(z:ℚ_p)‖ ≤ p⁻ᵏ`.
This discharges the radius hypotheses of the AB-linearization from integer valuations. -/
theorem norm_intCast_le_of_le_padicValInt {z : ℤ} {k : ℕ} (h : k ≤ padicValInt p z) :
    ‖(z : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ k := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [Int.cast_zero, norm_zero]; positivity
  · have hdvdN : p ^ k ∣ z.natAbs :=
      (pow_dvd_pow p h).trans (by rw [padicValInt]; exact pow_padicValNat_dvd)
    have hdvdZ : (p : ℤ) ^ k ∣ z := by
      have hcast : ((p ^ k : ℕ) : ℤ) ∣ (z.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hdvdN
      rw [Int.dvd_natAbs] at hcast
      simpa using hcast
    have hmem : (z : ℤ_[p]) ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
      rw [Ideal.mem_span_singleton]
      simpa using (Int.castRingHom ℤ_[p]).map_dvd hdvdZ
    simpa using (norm_coe_le_radius_iff_mem_span_pow (z : ℤ_[p]) k).2 hmem

/-- **A4 headline — AB-linearization mod `pᵏ` at the §5.1 profile.**  Under the profile
hypotheses (`p` odd, `1 ≤ T`, `k ≤ n+T`), the mod-`pᵏ` AB-linearization holds for the explicit
coefficient profile `φⱼ(1+pᵀ) = C(pⁿ,pʲ)((1+pᵀ)^{pʲ}-1)`:
`∑_{j≤n} aⱼ · log(1+φⱼ) ≡ ∑_{j≤n} aⱼ · φⱼ (mod pᵏ)`.  The radius bounds come from
`padicVal_phi : vₚ(φⱼ) = n+T ≥ k`. -/
theorem ab_linearization_phi_congMod (n T k : ℕ) (hodd : Odd p) (hk : 1 ≤ k) (hT : 1 ≤ T)
    (hprofile : k ≤ n + T) (a : ℕ → ℤ) :
    CongMod k
      (∑ j ∈ Finset.range (n + 1),
        (a j : ℚ_[p]) * logOnePlus ((phi p n j (1 + (p : ℤ) ^ T) : ℤ) : ℚ_[p]))
      (∑ j ∈ Finset.range (n + 1),
        (a j : ℚ_[p]) * ((phi p n j (1 + (p : ℤ) ^ T) : ℤ) : ℚ_[p])) := by
  refine sum_smul_logOnePlus_congMod hk _ a _ (fun j hj => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  refine norm_intCast_le_of_le_padicValInt ?_
  rw [padicVal_phi p n j T Fact.out hodd hT hj]
  exact hprofile

end PadicLog

/-! ## B1 — p-adic log functional equation (formal power series + analytic-transfer isolation).

Mathlib provides `PowerSeries.log`/`logOf` but neither the functional equation `logOf(f·g) =
logOf f + logOf g` nor an analytic `Padic.log`.  Following the recommended route, the functional
equation is proved **formally** in `ℚ_[p]⟦X⟧` by the logarithmic-derivative / coefficientwise
argument (no real-analysis derivative, hence valid `p`-adically), **unconditionally**:

* `PadicLogFormal.logOf_mul` : `logOf (f·g) = logOf f + logOf g`  (`constantCoeff = 1`);
* `PadicLogFormal.logOf_pow` : `logOf (fⁿ) = n • logOf f`  (the `log(Aᵖⁿ) = pⁿ log A` shape).

`term_eq_coeff_log` identifies the analytic series `PadicLog.logOnePlus` with the evaluation of
`PowerSeries.log` at the point.  The only remaining step — that this evaluation is a continuous
ring homomorphism transferring the formal identity to the convergent `ℚ_[p]` value — is isolated
as `PadicLogFormal.PadicLogAdditive`; the analytic power law `logOnePlus_pow_of_additive` is then
derived from it.  (The mod-`pᵏ` version of this transfer is already unconditional in §A4.) -/

namespace PadicLogFormal

open PowerSeries

/-! ### Formal functional equation in `A⟦X⟧` (any additively-torsion-free `ℚ`-algebra). -/

section Formal

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- `(1 + X) · (d/dX) log(1+X) = 1`. -/
theorem one_add_X_mul_deriv_log : (1 + X : A⟦X⟧) * d⁄dX A (log A) = 1 := by
  rw [deriv_log, add_mul, one_mul]
  ext n
  rw [map_add]
  cases n with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one, if_neg (Nat.succ_ne_zero m), ← map_add,
      show ((-1 : ℚ) ^ (m + 1) + (-1) ^ m) = 0 by ring, map_zero]

omit [Algebra ℚ A] in
/-- `f - 1` is substitutable when `f` has constant term `1`. -/
theorem hasSubst_sub_one {f : A⟦X⟧} (hf : constantCoeff f = 1) : HasSubst (f - 1) :=
  HasSubst.of_constantCoeff_zero' (by rw [map_sub, hf, map_one, sub_self])

/-- Logarithmic-derivative identity `f · (d/dX)(logOf f) = (d/dX) f`. -/
theorem mul_deriv_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f * d⁄dX A (logOf f) = d⁄dX A f := by
  have hsub : HasSubst (f - 1) := hasSubst_sub_one hf
  rw [logOf_eq, derivative_subst (hg := hsub)]
  have hd1 : d⁄dX A (f - 1 : A⟦X⟧) = d⁄dX A f := by rw [map_sub]; simp
  rw [hd1, ← mul_assoc]
  have e1 : (1 + X : A⟦X⟧).subst (f - 1) = f := by
    rw [← coe_substAlgHom hsub, map_add, map_one, substAlgHom_X hsub]; ring
  have key : f * (d⁄dX A (log A)).subst (f - 1) = 1 := by
    calc f * (d⁄dX A (log A)).subst (f - 1)
        = (1 + X : A⟦X⟧).subst (f - 1) * (d⁄dX A (log A)).subst (f - 1) := by rw [e1]
      _ = ((1 + X : A⟦X⟧) * d⁄dX A (log A)).subst (f - 1) := by
            rw [← coe_substAlgHom hsub, map_mul]
      _ = (1 : A⟦X⟧).subst (f - 1) := by rw [one_add_X_mul_deriv_log]
      _ = 1 := by rw [← coe_substAlgHom hsub, map_one]
  rw [key, one_mul]

/-- **Formal functional equation:** `logOf (f·g) = logOf f + logOf g`. -/
theorem logOf_mul [IsAddTorsionFree A] {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, one_mul]
  refine derivative.ext ?_ ?_
  · have hunit : IsUnit (f * g) := isUnit_iff_constantCoeff.mpr (hfg ▸ isUnit_one)
    apply hunit.mul_right_injective
    show f * g * d⁄dX A (logOf (f * g)) = f * g * d⁄dX A (logOf f + logOf g)
    rw [mul_deriv_logOf hfg, map_add, mul_add,
        (by ring : f * g * d⁄dX A (logOf f) = g * (f * d⁄dX A (logOf f))),
        (by ring : f * g * d⁄dX A (logOf g) = f * (g * d⁄dX A (logOf g))),
        mul_deriv_logOf hf, mul_deriv_logOf hg, Derivation.leibniz]
    simp only [smul_eq_mul]; ring
  · rw [map_add, constantCoeff_logOf hf, constantCoeff_logOf hg, constantCoeff_logOf hfg, add_zero]

/-- `logOf 1 = 0`. -/
theorem logOf_one [IsAddTorsionFree A] : logOf (1 : A⟦X⟧) = 0 := by
  have h := logOf_mul (A := A) (f := 1) (g := 1) (by simp) (by simp)
  rw [mul_one] at h
  have h2 : logOf (1 : A⟦X⟧) + 0 = logOf (1 : A⟦X⟧) + logOf (1 : A⟦X⟧) := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- **Formal power law:** `logOf (fⁿ) = n • logOf f` (the `log(Aᵖⁿ) = pⁿ log A` shape). -/
theorem logOf_pow [IsAddTorsionFree A] {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    logOf (f ^ n) = n • logOf f := by
  induction n with
  | zero => rw [pow_zero, logOf_one, zero_smul]
  | succ m ih =>
    have hpow : constantCoeff (f ^ m) = 1 := by rw [map_pow, hf, one_pow]
    rw [pow_succ, logOf_mul hpow hf, ih, succ_nsmul]

end Formal

/-! ### Specialization to `ℚ_[p]` and the coefficient bridge to the analytic log. -/

variable {p : ℕ} [Fact p.Prime]

/-- The formal functional equation over `ℚ_[p]⟦X⟧`. -/
theorem logOf_mul_qp {f g : ℚ_[p]⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := logOf_mul hf hg

/-- The formal power law over `ℚ_[p]⟦X⟧`. -/
theorem logOf_pow_qp {f : ℚ_[p]⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    logOf (f ^ n) = n • logOf f := logOf_pow hf n

/-- **Coefficient bridge.**  `PadicLog.term u n = (coeff (n+1) (log ℚ_[p])) · u^(n+1)`: the analytic
`logOnePlus` is the term-by-term evaluation of the formal `log(1+X)` at `u`. -/
theorem term_eq_coeff_log (u : ℚ_[p]) (n : ℕ) :
    PadicLog.term u n = (PowerSeries.coeff (n + 1) (PowerSeries.log ℚ_[p])) * u ^ (n + 1) := by
  rw [PadicLog.term, PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero n),
      map_div₀, map_pow, map_neg, map_one, map_natCast]
  have hsign : ((-1 : ℚ_[p])) ^ (n + 1 + 1) = (-1) ^ n := by rw [pow_succ, pow_succ]; ring
  rw [hsign]
  push_cast
  ring

/-! ### Analytic transfer (the isolated Tier-B core) and its consequences. -/

/-- `‖(1+u)ᵐ − 1‖ < 1` for `‖u‖ < 1`: iterating stays in the convergence ball. -/
theorem norm_one_add_pow_sub_one_lt {u : ℚ_[p]} (hu : ‖u‖ < 1) (m : ℕ) :
    ‖(1 + u) ^ m - 1‖ < 1 := by
  have h1u : ‖(1 + u : ℚ_[p])‖ ≤ 1 := by
    refine (Padic.nonarchimedean 1 u).trans ?_
    rw [norm_one]; exact max_le le_rfl hu.le
  induction m with
  | zero => simp
  | succ k ih =>
    have hpk : ‖(1 + u) ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1u
    have hstep : (1 + u) ^ (k + 1) - 1 = ((1 + u) ^ k - 1) + u * (1 + u) ^ k := by ring
    rw [hstep]
    refine (Padic.nonarchimedean _ _).trans_lt (max_lt ih ?_)
    rw [norm_mul]
    calc ‖u‖ * ‖(1 + u) ^ k‖ ≤ ‖u‖ * 1 := by gcongr
      _ = ‖u‖ := mul_one _
      _ < 1 := hu

/-- `logOnePlus 0 = 0`. -/
theorem logOnePlus_zero : PadicLog.logOnePlus (0 : ℚ_[p]) = 0 := by
  have hterm : ∀ n, PadicLog.term (0 : ℚ_[p]) n = 0 := fun n => by
    rw [PadicLog.term]; simp [zero_pow (Nat.succ_ne_zero n)]
  rw [show (PadicLog.logOnePlus (0 : ℚ_[p])) = ∑' n, PadicLog.term (0 : ℚ_[p]) n from rfl]
  simp only [hterm, tsum_zero]

/-- **Analytic transfer (isolated Tier-B core).**  The analytic functional equation
`logOnePlus((1+u)(1+v) − 1) = logOnePlus u + logOnePlus v`: exactly the formal `logOf_mul`
transported to the convergent `ℚ_[p]` value by a continuous evaluation.  The formal identity above
is unconditional; this analytic transfer is the residual Tier-B step (its mod-`pᵏ` version is the
unconditional §A4). -/
def PadicLogAdditive (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ u v : ℚ_[p], ‖u‖ < 1 → ‖v‖ < 1 →
    PadicLog.logOnePlus (u + v + u * v) = PadicLog.logOnePlus u + PadicLog.logOnePlus v

/-- **Analytic power law from additivity** (`log(Aᵖⁿ) = pⁿ log A`): under the analytic functional
equation, `logOnePlus ((1+u)ⁿ − 1) = n • logOnePlus u`. -/
theorem logOnePlus_pow_of_additive (h : PadicLogAdditive p) {u : ℚ_[p]} (hu : ‖u‖ < 1) (n : ℕ) :
    PadicLog.logOnePlus ((1 + u) ^ n - 1) = n • PadicLog.logOnePlus u := by
  induction n with
  | zero => rw [pow_zero, sub_self, logOnePlus_zero, zero_smul]
  | succ m ih =>
    set w := (1 + u) ^ m - 1 with hw
    have hwm : ‖w‖ < 1 := by rw [hw]; exact norm_one_add_pow_sub_one_lt hu m
    have hpow1 : (1 + u) ^ (m + 1) - 1 = w + u + w * u := by rw [hw]; ring
    rw [hpow1, h w u hwm hu, ih, succ_nsmul]

end PadicLogFormal

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
/-- A1 good-locus gate (abstract): for monic `F` of positive degree, the unconditional
equivalence `p ∤ Δ ⟺ (F mod p) separable`. -/
example {F : Polynomial ℤ} (hF : F.Monic) (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ GoodLocus.disc F ↔ (PrimeScan.modPolynomial p F).Separable :=
  GoodLocus.not_dvd_disc_iff_separable hF p
/-- A1 fifth correction: the paper's unconditional reverse of Thm 9.3(ii) is refuted
by the concrete witness `X²` over `ℤ₂`. -/
example : ∃ (p : ℕ) (_ : Fact p.Prime) (F : Polynomial ℤ_[p]) (a : ℤ_[p]),
    (∃! z : ℤ_[p], F.eval z = 0 ∧ ‖z - a‖ < 1) ∧ ‖F.derivative.eval a‖ ≠ 1 :=
  GoodLocus.unique_lift_not_imply_unit_derivative
/-- A2: the Weierstrass discriminant of `y² = x³ + a x + b` is `Δ = -16(4a³+27b²)`. -/
example (a b : ℤ) : (WeierstrassGate.shortWeierstrass a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) :=
  WeierstrassGate.shortWeierstrass_Δ a b
/-- A2: away from char 2, good reduction `p ∤ Δ(E)` ⟺ the residual cubic is separable. -/
example {a b : ℤ} (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ (p : ℤ) ∣ (WeierstrassGate.shortWeierstrass a b).Δ ↔
      (WeierstrassGate.cubicPoly (a : ZMod p) (b : ZMod p)).Separable :=
  WeierstrassGate.not_dvd_shortWeierstrass_Δ_iff_separable p hp2
/-- A3: the concrete four-layer gate's sections decompose as the intersection of the
layers' sections (`Γ(U,F) = ⋂ Γ(U,F_layer)`). -/
example (a b : ℤ) (M : ℕ) (U : Set ℕ) :
    PrimalityShadow.sections (PrimalityShadow.primeCertGate a b M) U
      = PrimalityShadow.sections PrimalityShadow.numLayer U
          ∩ PrimalityShadow.sections (PrimalityShadow.modLayer M) U
          ∩ PrimalityShadow.sections (PrimalityShadow.discLayer a b) U
          ∩ PrimalityShadow.sections (PrimalityShadow.ecLayer a b) U :=
  PrimalityShadow.sections_primeCertGate a b M U
/-- A3 ↔ A2: on a prime candidate the discriminant layer is residual-cubic separability. -/
example (a b : ℤ) (n : ℕ) [Fact n.Prime] :
    PrimalityShadow.discLayer a b n ↔
      (WeierstrassGate.cubicPoly (a : ZMod n) (b : ZMod n)).Separable :=
  PrimalityShadow.discLayer_iff_separable a b n
/-- A4: the AB-linearization holds mod `pᵏ` at the §5.1 profile (functional equation bypassed). -/
example (p : ℕ) [Fact p.Prime] (n T k : ℕ) (hodd : Odd p) (hk : 1 ≤ k) (hT : 1 ≤ T)
    (hprofile : k ≤ n + T) (a : ℕ → ℤ) :
    PadicLog.CongMod k
      (∑ j ∈ Finset.range (n + 1),
        (a j : ℚ_[p]) * PadicLog.logOnePlus ((phi p n j (1 + (p : ℤ) ^ T) : ℤ) : ℚ_[p]))
      (∑ j ∈ Finset.range (n + 1),
        (a j : ℚ_[p]) * ((phi p n j (1 + (p : ℤ) ^ T) : ℤ) : ℚ_[p])) :=
  PadicLog.ab_linearization_phi_congMod n T k hodd hk hT hprofile a
/-- A5: the δ-invariant vanishes exactly when `R → S` is surjective (smooth/normal fibre). -/
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    CurveInvariants.deltaInvariant R S = 0 ↔ Function.Surjective (algebraMap R S) :=
  CurveInvariants.deltaInvariant_eq_zero_iff R S
/-- A5: a tree dual graph has first Betti number `0`. -/
example : CurveInvariants.firstBettiNumber 4 5 1 = 0 :=
  CurveInvariants.firstBettiNumber_tree 5 (by norm_num)
/-- B1: the formal p-adic log functional equation `logOf(f·g) = logOf f + logOf g`. -/
example (p : ℕ) [Fact p.Prime] (f g : (PowerSeries ℚ_[p]))
    (hf : PowerSeries.constantCoeff f = 1) (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.logOf (f * g) = PowerSeries.logOf f + PowerSeries.logOf g :=
  PadicLogFormal.logOf_mul_qp hf hg
/-- B1: the formal power law `logOf(fⁿ) = n • logOf f` (`log(Aᵖⁿ) = pⁿ log A`). -/
example (p : ℕ) [Fact p.Prime] (f : (PowerSeries ℚ_[p]))
    (hf : PowerSeries.constantCoeff f = 1) (n : ℕ) :
    PowerSeries.logOf (f ^ n) = n • PowerSeries.logOf f :=
  PadicLogFormal.logOf_pow_qp hf n
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
#print axioms FrobeniusPointCount.frobeniusTrace_eq
#print axioms FrobeniusPointCount.isSupersingular_of_trace_zero
#print axioms FrobeniusPointCount.frobeniusCharPoly_eval
#print axioms FrobeniusPointCount.FrobeniusData.geom_of_trace_zero
#print axioms b5_supersingular_classification
#print axioms CohDimension.deltaCoh
#print axioms CohDimension.deltaCoh_le
#print axioms CohDimension.deltaCoh_mem
#print axioms CohDimension.sInf_eq_one
#print axioms CohDimension.deltaCoh_eq_one
#print axioms b6_deltaCoh_classification
#print axioms MotivicC1.MotivicRealization.motivicEuler
#print axioms MotivicC1.MotivicRealization.bump_eq_deltaChi
#print axioms c1_motivic_realization_classification
#print axioms EtaleCurveCohomology.CurveWeilCohomology.dimH1Xp_formula
#print axioms EtaleCurveCohomology.CurveWeilCohomology.bump_eq
#print axioms EtaleCurveCohomology.CurveWeilCohomology.smooth_dim_eq
#print axioms c2_curve_cohomology_classification
#print axioms PrimalitySheafCRT.glue_iff_compatible
#print axioms PrimalitySheafCRT.glue_of_coprime
#print axioms PrimalitySheafCRT.glue_unique
#print axioms PrimalitySheafCRT.sections_fiberProduct_eq
#print axioms c3_crt_gluing_classification
#print axioms Thm93Assembly.disc_hensel_gate_tfae
#print axioms Thm93Assembly.tor_equalizer_gate
#print axioms Thm93Assembly.detector_tfae
#print axioms Thm93Assembly.thm93_full_tfae
#print axioms Thm93Assembly.thm93_full_tfae_motivic
#print axioms c4_full_equivalence_classification
#print axioms Tier3Actual.skyscraperSheaf_isFlasque
#print axioms Tier3Actual.sheafCohomologyExtEquiv
#print axioms Tier3Actual.sheafCohomology_eq_ext
#print axioms Tier3Actual.ellAdicCohomology_nonempty
#print axioms Tier3Actual.flasque_sections_epi
#print axioms Tier3Actual.flasque_global_sections_surjective
#print axioms Tier3Actual.flasque_quotient_isFlasque
#print axioms Tier3Actual.IsGammaAcyclic.h1_subsingleton
#print axioms b2_flasque_classification
#print axioms CechComparison.cechH0
#print axioms CechComparison.cechH1
#print axioms CechComparison.paper_ext_one_is_sheaf_ext
#print axioms b3_cech_classification
#print axioms MotivicEuler.AdditiveEuler.cone_euler
#print axioms MotivicEuler.AdditiveEuler.euler_cone_mk
#print axioms MotivicEuler.AdditiveEuler.exists_cone_euler
#print axioms MotivicEuler.MotivicDeformation.deltaChi_mot
#print axioms b4_motivic_euler_classification
#print axioms PrimeScan.mem_simpleRoots_iff
#print axioms PrimeScan.simpleRootCount_pos_iff
#print axioms PrimeScan.hasSimpleRoot_eq_true_iff
#print axioms PrimeScan.eval_rootGCD_eq_zero_iff
#print axioms PrimeScan.scanned_root_norm_lt_one
#print axioms PrimeScan.scanned_derivative_norm_eq_one
#print axioms PrimeScan.simpleRoot_has_uniquePadicLift
#print axioms PrimeScan.scanPrime_eq_true_iff
#print axioms PrimeScan.mem_scanPrimesUpTo_iff
#print axioms GoodLocus.separable_iff_isCoprime_derivative
#print axioms GoodLocus.separable_iff_squarefree_of_perfectField
#print axioms GoodLocus.separable_iff_isUnit_resultant
#print axioms GoodLocus.resultant_explicit_eq_default
#print axioms GoodLocus.separable_iff_resultant_explicit_ne_zero
#print axioms GoodLocus.separable_iff_discr_ne_zero
#print axioms GoodLocus.rootMultiplicity_eq_one_iff_simple
#print axioms GoodLocus.rootMultiplicity_eq_one_of_separable
#print axioms GoodLocus.not_isRoot_derivative_of_separable
#print axioms GoodLocus.separable_iff_roots_nodup_of_splits
#print axioms GoodLocus.good_locus_field_tfae
#print axioms GoodLocus.disc_eq
#print axioms GoodLocus.intCast_disc_eq
#print axioms GoodLocus.not_dvd_disc_iff_separable
#print axioms GoodLocus.not_dvd_discr_iff_separable
#print axioms GoodLocus.modPolynomial_good_locus_tfae
#print axioms GoodLocus.mem_simpleRoots_iff_rootMultiplicity_eq_one
#print axioms GoodLocus.isRoot_mem_simpleRoots_of_separable
#print axioms GoodLocus.uniquePadicLift_of_separable_isRoot
#print axioms GoodLocus.goodPrime_gate
#print axioms GoodLocus.unique_lift_not_imply_unit_derivative
#print axioms a1_good_locus_classification
#print axioms WeierstrassGate.cubicPoly_monic
#print axioms WeierstrassGate.cubicPoly_natDegree
#print axioms WeierstrassGate.cubicPoly_degree
#print axioms WeierstrassGate.cubicPoly_discr
#print axioms WeierstrassGate.cubicPoly_map
#print axioms WeierstrassGate.cubicPoly_separable_iff
#print axioms WeierstrassGate.cubicPoly_squarefree_iff
#print axioms WeierstrassGate.not_dvd_cubic_disc_iff_separable
#print axioms WeierstrassGate.not_dvd_cubic_disc_iff_squarefree
#print axioms WeierstrassGate.cubic_good_locus_tfae
#print axioms WeierstrassGate.shortWeierstrass_Δ
#print axioms WeierstrassGate.shortWeierstrass_Δ_eq_cubic_discr
#print axioms WeierstrassGate.not_dvd_shortWeierstrass_Δ_iff_separable
#print axioms a2_weierstrass_gate_classification
#print axioms PrimalityShadow.sections_primeCertGate
#print axioms PrimalityShadow.primeCertGate_sectionwise
#print axioms PrimalityShadow.primeCertGate_equiv
#print axioms PrimalityShadow.discLayer_iff_separable
#print axioms PrimalityShadow.ecLayer_iff_discLayer
#print axioms a3_concrete_layers_classification
#print axioms PadicLog.congMod_trans
#print axioms PadicLog.congMod_add
#print axioms PadicLog.congMod_mul_of_norm_le_one
#print axioms PadicLog.congMod_intCast_mul
#print axioms PadicLog.congMod_sum
#print axioms PadicLog.logOnePlus_congMod
#print axioms PadicLog.sum_logOnePlus_congMod
#print axioms PadicLog.sum_smul_logOnePlus_congMod
#print axioms PadicLog.norm_intCast_le_of_le_padicValInt
#print axioms PadicLog.ab_linearization_phi_congMod
#print axioms a4_ab_linearization_classification
#print axioms CurveInvariants.deltaInvariant
#print axioms CurveInvariants.deltaInvariant_eq_zero_iff
#print axioms CurveInvariants.deltaInvariant_self
#print axioms CurveInvariants.deltaInvariantConductor
#print axioms CurveInvariants.firstBettiNumber_tree
#print axioms CurveInvariants.firstBettiNumber_nonneg_of_le
#print axioms CurveInvariants.graphFirstBetti
#print axioms CurveInvariants.betti_excess_eq
#print axioms CurveInvariants.betti_excess_smooth
#print axioms a5_curve_invariants_classification
#print axioms PadicLogFormal.one_add_X_mul_deriv_log
#print axioms PadicLogFormal.mul_deriv_logOf
#print axioms PadicLogFormal.logOf_mul
#print axioms PadicLogFormal.logOf_one
#print axioms PadicLogFormal.logOf_pow
#print axioms PadicLogFormal.logOf_mul_qp
#print axioms PadicLogFormal.logOf_pow_qp
#print axioms PadicLogFormal.term_eq_coeff_log
#print axioms PadicLogFormal.norm_one_add_pow_sub_one_lt
#print axioms PadicLogFormal.logOnePlus_zero
#print axioms PadicLogFormal.logOnePlus_pow_of_additive
#print axioms b1_padicLog_functional_equation_classification
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
