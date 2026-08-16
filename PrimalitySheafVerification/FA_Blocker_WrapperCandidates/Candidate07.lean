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

@[reducible] noncomputable def weakAntiOperatorSubFrozen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) : WeakAntiOperator E := A - B

@[simp]
theorem weakAntiOperatorSubFrozen_apply_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) (u v : E) :
    weakAntiOperatorSubFrozen A B u v = A u v - B u v := rfl

theorem inner_add_right_frozen
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y z : E) :
    inner ℂ x (y + z) = inner ℂ x y + inner ℂ x z :=
  inner_add_right x y z

/-- Scalar cancellation is elaborated generically, independently of the large
terms which later instantiate `a`, `b`, and `c`. -/
theorem complex_sub_eq_of_eq_add_frozen (a b c : ℂ)
    (h : a = b + c) : a - b = c := by
  calc
    a - b = (b + c) - b := congrArg (fun x : ℂ ↦ x - b) h
    _ = c := by ring

/-- Pointwise evaluation of the bundled weighted operator, frozen before the
large completion type is substituted into any subtraction expression. -/
theorem weightedGraphOperator_apply_apply_smul_frozen
    (n : ℤ)
    (a : MeasureTheory.Lp ℂ ∞ chosenEuclideanCarrierMeasure)
    (u v : GraphSobolevCompletion n) :
    weightedGraphOperator n a u v =
      inner ℂ (graphEuclideanBase n v)
        (a • graphEuclideanBase n u : OrbitEuclideanL2 n) :=
  rfl

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
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [hfull, hhard, htail, discriminantFull_eq_hard_add_tail]
  ring

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
  rw [weightedGraphOperator_apply_apply_smul_frozen,
    weightedGraphOperator_apply_apply_smul_frozen,
    weightedGraphOperator_apply_apply_smul_frozen]
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
          (fun w : OrbitEuclideanL2 n ↦ inner ℂ (graphEuclideanBase n v) w) hmul
      _ = _ := inner_add_right_frozen _ _ _
  exact complex_sub_eq_of_eq_add_frozen _ _ _ hinner

theorem weightedFull_sub_weightedHard_eq_weightedTail
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

/-- Generic norm symmetry, elaborated before the concrete graph space. -/
theorem norm_sub_rev_eq_norm_weakAntiOperatorSubFrozen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : WeakAntiOperator E) :
    ‖B - A‖ = ‖weakAntiOperatorSubFrozen A B‖ := by
  simpa only [weakAntiOperatorSubFrozen] using (norm_sub_rev B A)

theorem norm_discriminantHardStageOperator_sub_graphPotential_le
    (N : ℕ) (n : ℤ) :
    ‖discriminantHardStageOperator N n - graphPotentialOperator n‖ ≤
      discriminantCuspEpsilon N := by
  rw [graphPotentialOperator_eq_weightedFull]
  calc
    ‖discriminantHardStageOperator N n -
        weightedGraphOperator n discriminantFullCarrierWeightLp‖ =
      ‖weakAntiOperatorSubFrozen
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n)‖ :=
      norm_sub_rev_eq_norm_weakAntiOperatorSubFrozen
        (weightedGraphOperator n discriminantFullCarrierWeightLp)
        (discriminantHardStageOperator N n)
    _ = ‖weightedGraphOperator n
        (discriminantTailCarrierWeightLp N)‖ :=
      congrArg norm (weightedFull_sub_weightedHard_eq_weightedTail N n)
    _ ≤ discriminantCuspEpsilon N :=
      (norm_weightedGraphOperator_le n
        (discriminantTailCarrierWeightLp N)).trans
          (norm_discriminantTailCarrierWeightLp_le N)

/-- Compactness from the already concrete hard-stage operators, avoiding a
final definitional conversion back to the factorized composition. -/
theorem graphPotentialOperator_isCompact_of_hardStageOperators
    (n : ℤ)
    (hTail : ∀ N,
      ‖discriminantHardStageOperator N n - graphPotentialOperator n‖ ≤
        discriminantCuspEpsilon N) :
    IsCompactOperator (graphPotentialOperator n) := by
  apply isCompactOperator_of_tendsto (l := (Filter.atTop : Filter ℕ))
  · change Filter.Tendsto
      (fun N ↦ discriminantHardStageOperator N n)
      Filter.atTop
      (@nhds
        (GraphSobolevCompletion n →L[ℂ]
          StrongAntiDual (GraphSobolevCompletion n))
        (@UniformSpace.toTopologicalSpace
          (GraphSobolevCompletion n →L[ℂ]
            StrongAntiDual (GraphSobolevCompletion n))
          (@PseudoMetricSpace.toUniformSpace
            (GraphSobolevCompletion n →L[ℂ]
              StrongAntiDual (GraphSobolevCompletion n))
            SeminormedAddCommGroup.toPseudoMetricSpace))
        (graphPotentialOperator n))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero
      (fun N ↦ norm_nonneg
        (discriminantHardStageOperator N n - graphPotentialOperator n))
      hTail discriminantCuspEpsilon_tendsto_zero
  · exact Filter.Eventually.of_forall fun N ↦
      discriminantHardStageOperator_isCompact N n

/-- Exact final endpoint through the concrete hard-stage approximants. -/
theorem graphPotentialOperator_isCompact_unconditional (n : ℤ) :
    IsCompactOperator
      (ExplicitDiscriminantPotential.FixedPhaseGraphPotential.graphPotentialOperator n) := by
  exact graphPotentialOperator_isCompact_of_hardStageOperators n
    (fun N ↦ norm_discriminantHardStageOperator_sub_graphPotential_le N n)

end P5DiscriminantHardTruncation
end Mock2FA.PaperCorrections.AutomorphicSobolev
