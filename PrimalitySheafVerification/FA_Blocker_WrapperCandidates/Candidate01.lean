import PrimalitySheafVerification.FA_Blocker_Prefix

namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace P5DiscriminantHardTruncation

open Set Function Topology Filter MeasureTheory
open scoped ENNReal NNReal
open DefinitionOneSobolev
open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
open DefinitionOneSobolev.FixedPhaseGraphCompletion
open DefinitionOneSobolev.WeightCorePetersson
open GammaTwoQuotientGeometry
open FixedPhaseClosedOperators
open FixedPhaseClosedOperators.PhysicalLocalL2
open ExplicitDiscriminantPotential
open ExplicitDiscriminantPotential.FixedPhaseGraphPotential
open P5PhysicalHardStageRestriction

/-- Generic wrapper: its subtraction instance is synthesized before the large
index-dependent graph-completion type is substituted. -/
private noncomputable def weakAntiOperatorSub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) : WeakAntiOperator E :=
  A - B

private theorem weakAntiOperatorSub_apply_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) (u v : E) :
    weakAntiOperatorSub A B u v = A u v - B u v :=
  rfl

/-- Full carrier multiplication is the sum of hard and tail multiplication. -/
theorem discriminantFullCarrierMul_eq_hard_add_tail_wrapper
    (N : ℕ) (n : ℤ) (u : GraphSobolevCompletion n) :
    (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
        OrbitEuclideanL2 n) =
      (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n) +
      (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n) := by
  apply Lp.ext
  filter_upwards [
    coeFn_discriminantFullCarrierWeightLp,
    coeFn_discriminantHardCarrierWeightLp N,
    coeFn_discriminantTailCarrierWeightLp N,
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      discriminantFullCarrierWeightLp (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantHardCarrierWeightLp N) (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantTailCarrierWeightLp N) (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_add
      (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n)
      (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
        OrbitEuclideanL2 n)] with
      z hfull hhard htail hfullmul hhardmul htailmul hadd
  rw [hfullmul, hadd, Pi.add_apply, hhardmul, htailmul]
  change ((discriminantFullCarrierWeightLp : ℍ → ℂ) z) *
        ((graphEuclideanBase n u : ℍ → ℂ) z) =
      ((discriminantHardCarrierWeightLp N : ℍ → ℂ) z) *
          ((graphEuclideanBase n u : ℍ → ℂ) z) +
        ((discriminantTailCarrierWeightLp N : ℍ → ℂ) z) *
          ((graphEuclideanBase n u : ℍ → ℂ) z)
  rw [hfull, hhard, htail, discriminantFull_eq_hard_add_tail]
  ring

/-- Pointwise splitting, represented through a generic subtraction wrapper to
avoid global WHNF expansion of the bundled dependent operator type. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail_wrapper
    (N : ℕ) (n : ℤ) :
    weakAntiOperatorSub
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n) =
      weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [weakAntiOperatorSub_apply_apply]
  have hhard :
      discriminantHardStageOperator N n u v =
        weightedGraphOperator n (discriminantHardCarrierWeightLp N) u v :=
    congrArg (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
      (discriminantHardStageOperator_eq_weightedHard N n)
  rw [hhard]
  simp only [weightedGraphOperator, LinearMap.mkContinuous₂_apply,
    weightedGraphLinear, lpInfinityMultiplier_apply]
  rw [← inner_sub_right]
  have hmul := discriminantFullCarrierMul_eq_hard_add_tail_wrapper N n u
  have hsub :
      (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
          OrbitEuclideanL2 n) -
        (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
          OrbitEuclideanL2 n) =
        (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
          OrbitEuclideanL2 n) := by
    rw [hmul]
    abel
  exact congrArg
    (fun w : OrbitEuclideanL2 n ↦ inner ℂ (graphEuclideanBase n v) w) hsub

end P5DiscriminantHardTruncation
end Mock2FA.PaperCorrections.AutomorphicSobolev
