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

/-- Generic subtraction is elaborated before the large index-dependent
completion is substituted. -/
@[reducible] noncomputable def weakAntiOperatorSubFrozen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) : WeakAntiOperator E :=
  A - B

@[simp]
theorem weakAntiOperatorSubFrozen_apply_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) (u v : E) :
    weakAntiOperatorSubFrozen A B u v = A u v - B u v :=
  rfl

/-- Generic additivity of the inner product in its second argument. -/
theorem inner_add_right_frozen
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y z : E) :
    inner ℂ x (y + z) = inner ℂ x y + inner ℂ x z :=
  inner_add_right x y z

/-- Full carrier multiplication is the sum of hard and tail multiplication. -/
theorem discriminantFullCarrierMul_eq_hard_add_tail_frozen
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
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfull, hhard, htail, discriminantFull_eq_hard_add_tail]
  ring

/-- Pointwise operator splitting, obtained from an additive L² identity before
performing scalar subtraction. -/
theorem weightedFull_sub_weightedHard_apply_apply_eq_tail_frozen
    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) :
    weakAntiOperatorSubFrozen
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n) u v =
      weightedGraphOperator n (discriminantTailCarrierWeightLp N) u v := by
  rw [weakAntiOperatorSubFrozen_apply_apply]
  rw [congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (discriminantHardStageOperator_eq_weightedHard N n)]
  simp only [weightedGraphOperator, LinearMap.mkContinuous₂_apply,
    weightedGraphLinear, lpInfinityMultiplier_apply]
  have hmul := discriminantFullCarrierMul_eq_hard_add_tail_frozen N n u
  have hinner :
      inner ℂ (graphEuclideanBase n v)
          (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
            OrbitEuclideanL2 n) =
        inner ℂ (graphEuclideanBase n v)
            (discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n) +
          inner ℂ (graphEuclideanBase n v)
            (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n) := by
    calc
      inner ℂ (graphEuclideanBase n v)
          (discriminantFullCarrierWeightLp • graphEuclideanBase n u :
            OrbitEuclideanL2 n) =
        inner ℂ (graphEuclideanBase n v)
          ((discriminantHardCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n) +
            (discriminantTailCarrierWeightLp N • graphEuclideanBase n u :
              OrbitEuclideanL2 n)) :=
        congrArg
          (fun w : OrbitEuclideanL2 n ↦
            inner ℂ (graphEuclideanBase n v) w) hmul
      _ = _ := inner_add_right_frozen _ _ _
  rw [hinner]
  ring

/-- Bundled splitting after the pointwise proof has fixed all dependent types. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail_frozen
    (N : ℕ) (n : ℤ) :
    weakAntiOperatorSubFrozen
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n) =
      weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact weightedFull_sub_weightedHard_apply_apply_eq_tail_frozen N n u v

end P5DiscriminantHardTruncation
end Mock2FA.PaperCorrections.AutomorphicSobolev
