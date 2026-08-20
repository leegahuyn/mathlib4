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

private noncomputable def weakAntiOperatorSub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) : WeakAntiOperator E := A - B

private theorem weakAntiOperatorSub_apply_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) (u v : E) :
    weakAntiOperatorSub A B u v = A u v - B u v := rfl

/-- Pointwise scalar multiplication identity, avoiding an Lp addition theorem. -/
theorem weightedFull_sub_weightedHard_apply_apply_eq_tail
    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) :
    weakAntiOperatorSub
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n) u v =
      weightedGraphOperator n (discriminantTailCarrierWeightLp N) u v := by
  rw [weakAntiOperatorSub_apply_apply]
  have hhard := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (discriminantHardStageOperator_eq_weightedHard N n)
  rw [hhard]
  simp only [weightedGraphOperator, LinearMap.mkContinuous₂_apply,
    weightedGraphLinear, lpInfinityMultiplier_apply]
  rw [← inner_sub_right]
  congr 2
  apply Lp.ext
  filter_upwards [
    coeFn_discriminantFullCarrierWeightLp,
    coeFn_discriminantTailCarrierWeightLp N,
    coeFn_discriminantHardCarrierWeightLp N,
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      discriminantFullCarrierWeightLp (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantTailCarrierWeightLp N) (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (discriminantHardCarrierWeightLp N) (graphEuclideanBase n u)] with
      z hfull htail hhardW hfullmul htailmul hhardmul
  rw [hfullmul, hhardmul, htailmul]
  change ((discriminantFullCarrierWeightLp : ℍ → ℂ) z) *
        ((graphEuclideanBase n u : ℍ → ℂ) z) -
      ((discriminantHardCarrierWeightLp N : ℍ → ℂ) z) *
        ((graphEuclideanBase n u : ℍ → ℂ) z) =
      ((discriminantTailCarrierWeightLp N : ℍ → ℂ) z) *
        ((graphEuclideanBase n u : ℍ → ℂ) z)
  rw [hfull, hhardW, htail, discriminantFull_eq_hard_add_tail]
  ring

/-- Bundled form obtained only after pointwise elaboration has fixed the type. -/
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
  exact weightedFull_sub_weightedHard_apply_apply_eq_tail N n u v

end P5DiscriminantHardTruncation
end Mock2FA.PaperCorrections.AutomorphicSobolev
