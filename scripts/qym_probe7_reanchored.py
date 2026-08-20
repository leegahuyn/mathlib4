#!/usr/bin/env python3
"""Static Probe7 projection over the exact authoritative Probe6 QYM bytes.

This helper applies only observed direct-root API/coercion repairs.  It never
invokes Lean/Lake/Git or the network, never modifies repository source, and
never authorizes promotion.  Both directions are byte-identity locked.  Each
replacement is exact and occurrence counted, and the exact authoritative
Probe6 compiler log is checked for the corresponding diagnostic headers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe7-reanchored-transform-v1"
INPUT_SHA256 = "1941ed50883da7e1c6cc0fbdcab084f0184ab1b35d89e00a754cb60809723b34"
INPUT_GIT_BLOB = "21919f9a27529afa93b12bb8e88d8952cb63e292"
INPUT_BYTES = 2_912_719
INPUT_LF = 61_571
LOG_SHA256 = "1b0a91a839ba66bd03424978c8a72fc5cbbff7d8fb07921f150939d802383a86"

# Sealed after a deterministic bootstrap projection, then enforced both ways.
OUTPUT_SHA256 = "342eb7aab3d5e71fc242706188abdb7cb1804cd04c79ed254e1715fe0876f3eb"
OUTPUT_GIT_BLOB = "9b53049115afcc674fac88f998b6716abddb0162"
OUTPUT_BYTES = 2_913_545
OUTPUT_LF = 61_593


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    occurrences: int = 1
    rationale: str = ""


RULES: tuple[Rule, ...] = (
    Rule(
        "real_part_form_remove_stale_star_ring_end_rewrite",
        "        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r u, map_smulₛₗ,\n"
        "          smul_apply, starRingEnd_apply, RCLike.conj_ofReal,\n"
        "          smul_eq_mul, RCLike.re_ofReal_mul])\n",
        "        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r u, map_smulₛₗ,\n"
        "          smul_apply, RCLike.conj_ofReal,\n"
        "          smul_eq_mul, RCLike.re_ofReal_mul])\n",
        (Header(23245, 41, "Tactic `rewrite` failed"),),
        rationale="The preceding map_smul rewrite already exposes star ↑r; conj_ofReal is the applicable rewrite.",
    ),
    Rule(
        "real_solution_dense_range_change_coercion",
        "  simpa only [realSolutionMap, e, ContinuousLinearMap.coe_comp',\n"
        "    Function.comp_def] using hcomp\n",
        "  change DenseRange (fun x : H =>\n"
        "    e.symm ((j.restrictScalars ℝ).adjoint x))\n"
        "  exact hcomp\n",
        (Header(23689, 2, "Type mismatch: After simplification"),),
        rationale="State the definitionally equal function without the ContinuousLinearEquiv coercion wrapper.",
    ),
    Rule(
        "pmap_eigenvalue_unfold_domain_vector_and_star_end",
        "  simpa only [hxd, inner_smul_left, inner_smul_right] using hsymm xd xd\n",
        "  simpa only [xd, hxd, inner_smul_left, inner_smul_right,\n"
        "    starRingEnd_apply] using hsymm xd xd\n",
        (Header(24569, 2, "Type mismatch: After simplification"),),
        rationale="Unfold the domain subtype value and normalize starRingEnd to star in the symmetric-form equality.",
    ),
    Rule(
        "unit_eigenvectors_install_real_normed_space",
        "section UnitEigenvectors\n\n"
        "variable {𝕜 E : Type*} [RCLike 𝕜]\n"
        "variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]\n\n",
        "section UnitEigenvectors\n\n"
        "variable {𝕜 E : Type*} [RCLike 𝕜]\n"
        "variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]\n\n"
        "local instance instRealNormedSpaceE : NormedSpace ℝ E :=\n"
        "  NormedSpace.restrictScalars ℝ 𝕜 E\n\n",
        (
            Header(25144, 2, "failed to synthesize instance of type class"),
            Header(25149, 8, "failed to synthesize instance of type class"),
        ),
        rationale="Install Mathlib's explicit scalar-restriction structure required by NormedSpace.normalize.",
    ),
    Rule(
        "unit_eigenvector_orthogonal_family_current_api",
        "  exact hsymm.orthogonalFamily_eigenspaces.pairwise hμν\n"
        "    (unitEigenvector T μ) (unitEigenvector_hasEigenvector T μ).1\n"
        "    (unitEigenvector T ν) (unitEigenvector_hasEigenvector T ν).1\n",
        "  exact hsymm.orthogonalFamily_eigenspaces.pairwise hμν\n"
        "    (unitEigenvector_hasEigenvector T μ).1\n"
        "    (unitEigenvector_hasEigenvector T ν).1\n",
        (Header(25193, 4, "Application type mismatch"),),
        rationale="The current OrthogonalFamily.pairwise API takes eigenspace memberships, not explicit vectors.",
    ),
    Rule(
        "unit_eigenvector_norm_sub_fix_scalar",
        "    rw [norm_sub_sq, hinnerImage]\n",
        "    rw [norm_sub_sq (𝕜 := 𝕜), hinnerImage]\n",
        (Header(25230, 8, "typeclass instance problem is stuck"),),
        rationale="Fix the scalar metavariable of norm_sub_sq to the section's RCLike field.",
    ),
    Rule(
        "image_vector_injective_beta_expose",
        "    have hdist := himage_separated hne\n"
        "    rw [hμν, dist_self] at hdist\n",
        "    have hdist := himage_separated hne\n"
        "    change r ≤ dist (imageVector μ) (imageVector ν) at hdist\n"
        "    rw [hμν, dist_self] at hdist\n",
        (Header(25306, 8, "Tactic `rewrite` failed"),),
        rationale="Beta-reduce the pairwise predicate before rewriting its two imageVector arguments.",
    ),
    Rule(
        "operator_eigenvalue_unfold_before_difference_rewrite",
        "  have hdiff : z - (z - (ν : 𝕜)⁻¹) = (ν : 𝕜)⁻¹ := by ring\n"
        "  rw [hdiff]\n",
        "  have hdiff : z - (z - (ν : 𝕜)⁻¹) = (ν : 𝕜)⁻¹ := by ring\n"
        "  change z - (z - (ν : 𝕜)⁻¹) ≠ 0\n"
        "  rw [hdiff]\n",
        (Header(26434, 6, "Tactic `rewrite` failed"),),
        rationale="Unfold operatorEigenvalue by change before rewriting the calculated difference.",
    ),
    Rule(
        "closed_ball_bound_add_on_right",
        "          _ ≤ ‖z‖ + R := add_le_add_left hlambda.2 ‖z‖\n",
        "          _ ≤ ‖z‖ + R := add_le_add_right hlambda.2 ‖z‖\n",
        (Header(26642, 25, "Type mismatch"),),
        rationale="The fixed addend is on the left of both sides, so use add_le_add_right.",
    ),
    Rule(
        "resolvent_inverse_image_use_sub_right_injective",
        "      exact sub_left_inj.mp hsub\n",
        "      exact sub_right_inj.mp hsub\n",
        (Header(26652, 28, "Application type mismatch"),),
        rationale="The common minuend z is on the left; sub_right_inj cancels it and compares a with b.",
    ),
    Rule(
        "raw_differential_add_change_dependent_codomain",
        "  simpa only [rawDifferential, Submodule.coe_add] using mfderiv_add hg hh\n",
        "  change mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 + h.1) τ =\n"
        "    mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 τ + mfderiv 𝓘(ℂ) 𝓘(ℂ) h.1 τ\n"
        "  exact mfderiv_add hg hh\n",
        (Header(28358, 2, "Type mismatch: After simplification"),),
        rationale="Use change to expose the definitionally equal dependent tangent-space codomain before the API lemma.",
    ),
    Rule(
        "raw_differential_smul_change_dependent_codomain",
        "  simpa only [rawDifferential, Submodule.coe_smul] using\n"
        "    const_smul_mfderiv hg c\n",
        "  change mfderiv 𝓘(ℂ) 𝓘(ℂ) (c • g.1) τ =\n"
        "    c • mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 τ\n"
        "  exact const_smul_mfderiv hg c\n",
        (Header(28365, 2, "Type mismatch: After simplification"),),
        rationale="Expose the dependent tangent-space codomain explicitly, then use const_smul_mfderiv unchanged.",
    ),
    Rule(
        "eta_covariant_derivative_apply_unfold_linear_wrapper",
        "  simpa only [covariantDerivativeLinear, etaGaugeDifferential,\n"
        "    rawDifferential] using h\n",
        "  simpa only [etaCovariantDerivativeLinear, covariantDerivativeLinear,\n"
        "    etaGaugeDifferential, rawDifferential] using h\n",
        (Header(28516, 2, "Type mismatch: After simplification"),),
        rationale="Unfold the remaining etaCovariantDerivativeLinear wrapper on the left-hand side.",
    ),
    Rule(
        "ambient_restriction_add_unfold_pointwise_add",
        "  rw [hsum, hout, hu, hv, hin]\n",
        "  rw [hsum, hout, Pi.add_apply, hu, hv, hin]\n",
        (Header(50491, 18, "Tactic `rewrite` failed"),),
        rationale="Expose pointwise function addition before using the two pointwise restriction equalities.",
    ),
    Rule(
        "ambient_restriction_smul_unfold_pointwise_smul",
        "  rw [hleft, hright, hu, hin]\n",
        "  rw [hleft, hright, Pi.smul_apply, hu, hin]\n",
        (Header(50508, 21, "Tactic `rewrite` failed"),),
        rationale="Expose pointwise function scalar multiplication before rewriting the restriction value.",
    ),
    Rule(
        "ambient_restriction_linear_map_apply_in_norm_bound",
        "    simpa only [one_mul] using ambientRestriction_norm_le hYZ u)\n",
        "    simpa only [one_mul, ambientRestrictionLinearMap_apply] using\n"
        "      ambientRestriction_norm_le hYZ u)\n",
        (
            Header(50527, 4, "Type mismatch: After simplification"),
            Header(50538, 4, "Type mismatch: After simplification"),
        ),
        occurrences=2,
        rationale="Reduce the linear-map wrapper to the already proved restriction norm inequality.",
    ),
    Rule(
        "ambient_zero_extension_add_unfold_pointwise_add",
        "  rw [hleft, hright, hu, hv]\n"
        "  simp only [ambientZeroExtensionRepresentative] at hsrc ⊢\n",
        "  rw [hleft, hright, Pi.add_apply, hu, hv]\n"
        "  simp only [ambientZeroExtensionRepresentative] at hsrc ⊢\n",
        (Header(50624, 21, "Tactic `rewrite` failed"),),
        rationale="Expose the pointwise sum carried by the Lp representative.",
    ),
    Rule(
        "ambient_zero_extension_smul_unfold_pointwise_smul",
        "  rw [hleft, hright, hu]\n"
        "  simp only [ambientZeroExtensionRepresentative] at hsrc ⊢\n",
        "  rw [hleft, hright, Pi.smul_apply, hu]\n"
        "  simp only [ambientZeroExtensionRepresentative] at hsrc ⊢\n",
        (Header(50644, 21, "Tactic `rewrite` failed"),),
        rationale="Expose the pointwise scalar action carried by the Lp representative.",
    ),
    Rule(
        "zero_extension_trans_final_branch_reflexive",
        "    · simp only [hx, hxZ, Set.indicator_of_mem,\n"
        "        Set.indicator_of_notMem]\n"
        "    · simp only [hx, hxZ, Set.indicator_of_notMem]\n",
        "    · simp only [hx, hxZ, Set.indicator_of_mem,\n"
        "        Set.indicator_of_notMem]\n"
        "    · rfl\n",
        (Header(50767, 6, "`simp` made no progress"),),
        rationale="The prior pointwise rewrites already reduce the final outside/outside branch to reflexivity.",
    ),
    Rule(
        "inner_indicator_final_branch_reflexive",
        "  by_cases hx : x ∈ s\n"
        "  · simp only [hx, Set.indicator_of_mem]\n"
        "  · simp only [hx, Set.indicator_of_notMem, inner_zero_right]\n",
        "  by_cases hx : x ∈ s\n"
        "  · simp only [hx, Set.indicator_of_mem]\n"
        "  · rfl\n",
        (Header(50788, 4, "`simp` made no progress"),),
        rationale="Both sides are already definitionally zero in the not-member branch.",
    ),
    Rule(
        "ambient_zero_extension_inner_use_isometry_coercions",
        "  rw [inner_sub_left,\n"
        "    ← ambientRestriction_inner_eq_zeroExtension_inner hYZ u v,\n"
        "    (ambientZeroExtensionIsometry hYZ).inner_map_map,\n"
        "    sub_self]\n",
        "  rw [inner_sub_left,\n"
        "    ← ambientRestriction_inner_eq_zeroExtension_inner hYZ u v,\n"
        "    ← ambientZeroExtensionIsometry_apply hYZ (ambientRestriction hYZ u),\n"
        "    ← ambientZeroExtensionIsometry_apply hYZ v,\n"
        "    (ambientZeroExtensionIsometry hYZ).inner_map_map,\n"
        "    sub_self]\n",
        (Header(50834, 4, "Tactic `rewrite` failed"),),
        rationale="Expose both zero extensions as applications of the linear isometry before using inner_map_map.",
    ),
    Rule(
        "bounded_potential_no_go_preserve_implicit_parameters",
        "abbrev boundedPotentialCompactResolventNoGo :=\n"
        "  QYM.FullCertification.P4ActualStageL2InfiniteDimensionalExtension.actualStageDiscriminantPotential_not_compact_realResolvent\n",
        "abbrev boundedPotentialCompactResolventNoGo :=\n"
        "  @QYM.FullCertification.P4ActualStageL2InfiniteDimensionalExtension.actualStageDiscriminantPotential_not_compact_realResolvent\n",
        (
            Header(57535, 7, "Failed to infer type of definition"),
            Header(57536, 2, "don't know how to synthesize implicit argument `Y`"),
        ),
        rationale="Keep implicit Y as an argument of the alias instead of instantiating it with an unsolved metavariable.",
    ),
    Rule(
        "projection_hamiltonian_no_go_preserve_implicit_parameters",
        "abbrev projectionHamiltonianCompactResolventNoGo :=\n"
        "  QYM.FullCertification.P12ActualInverseEtaProjectionHamiltonianExtension.actualInverseEtaProjectionHamiltonian_no_compact_realResolventPoint\n",
        "abbrev projectionHamiltonianCompactResolventNoGo :=\n"
        "  @QYM.FullCertification.P12ActualInverseEtaProjectionHamiltonianExtension.actualInverseEtaProjectionHamiltonian_no_compact_realResolventPoint\n",
        (
            Header(57540, 7, "Failed to infer type of definition"),
            Header(57541, 2, "don't know how to synthesize implicit argument `Y`"),
        ),
        rationale="Preserve the theorem's implicit Y binder in the abbreviation type.",
    ),
    Rule(
        "item6_actual_stage_no_go_preserve_implicit_parameters",
        "abbrev item6_actualStage_boundedCompactResolventSurrogate_noGo :=\n"
        "  QYM.FullCertification.Mock3SpectralCoordinateH1RellichExtension.actualStage_no_bounded_compactResolvent_surrogate\n",
        "abbrev item6_actualStage_boundedCompactResolventSurrogate_noGo :=\n"
        "  @QYM.FullCertification.Mock3SpectralCoordinateH1RellichExtension.actualStage_no_bounded_compactResolvent_surrogate\n",
        (
            Header(59757, 7, "Failed to infer type of definition"),
            Header(59758, 2, "don't know how to synthesize implicit argument `Y`"),
        ),
        rationale="Preserve Y and hY as binders; this also removes the dependent #print unknown-constant cascade.",
    ),
    Rule(
        "item7_frame_bridge_preserve_all_implicit_parameters",
        "abbrev item7_lowerFrame_and_energyComparison_imply_excessCoercivity :=\n"
        "  QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.excessCoercivity_of_lowerFrame_and_energyComparison\n",
        "abbrev item7_lowerFrame_and_energyComparison_imply_excessCoercivity :=\n"
        "  @QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.excessCoercivity_of_lowerFrame_and_energyComparison\n",
        (Header(59765, 2, "typeclass instance problem is stuck"),),
        rationale="Retain H, K, and their structures as parameters rather than synthesizing instances for metavariable types.",
    ),
    Rule(
        "item7_compact_analysis_preserve_all_implicit_parameters",
        "abbrev item7_actualOffGround_compactAnalysis_noPositiveLowerFrame :=\n"
        "  QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualOffGround_compactAnalysis_has_no_positive_lowerFrame\n",
        "abbrev item7_actualOffGround_compactAnalysis_noPositiveLowerFrame :=\n"
        "  @QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualOffGround_compactAnalysis_has_no_positive_lowerFrame\n",
        (Header(59775, 2, "typeclass instance problem is stuck"),),
        rationale="Retain K, Y, and their structures as binders and remove the dependent #print cascade.",
    ),
    Rule(
        "escape_witness_norm_nonzero_from_positive_measure",
        "  rw [MeasureTheory.norm_indicatorConstLp'\n"
        "    (by norm_num : (2 : ℝ≥0∞) ≠ 0)\n"
        "    hMeasurePos.ne']\n"
        "  positivity\n",
        "  rw [MeasureTheory.norm_indicatorConstLp'\n"
        "    (by norm_num : (2 : ℝ≥0∞) ≠ 0)\n"
        "    hMeasurePos.ne']\n"
        "  simp only [norm_one, one_mul]\n"
        "  exact (Real.rpow_pos_of_pos hMeasureRealPos _).ne'\n",
        (Header(60913, 2, "failed to prove nonzeroness"),),
        rationale="Use the already established strict positivity of the real measure to prove the rpow factor nonzero.",
    ),
    Rule(
        "escape_projection_rewrite_pointwise_witness_inside_indicator",
        "  rw [hProjection, hZero,\n"
        "    QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionRepresentative, hWitness]\n"
        "  by_cases hx : x ∈ QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.naturalStageSet n\n"
        "  · rw [Set.indicator_of_mem hx]\n",
        "  rw [hProjection, hZero,\n"
        "    QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionRepresentative]\n"
        "  by_cases hx : x ∈ QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.naturalStageSet n\n"
        "  · rw [Set.indicator_of_mem hx, hWitness]\n",
        (Header(60939, 111, "Tactic `rewrite` failed"),),
        rationale="The pointwise equality is not a subterm while the function is still under indicator; expose the member branch first.",
    ),
    Rule(
        "norm_convergence_reduce_sub_zero",
        "    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hNorm)\n",
        "    simpa only [sub_zero] using\n"
        "      (tendsto_iff_norm_sub_tendsto_zero.mp hNorm)\n",
        (Header(61004, 4, "Type mismatch: After simplification"),),
        rationale="Normalize the displayed operator subtraction by zero explicitly.",
    ),
    Rule(
        "resolvent_error_reduce_clm_smul_application",
        "    QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffLimitNegativeOneResolvent_apply,\n"
        "    QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffEscapeHamiltonian_apply]\n",
        "    QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffLimitNegativeOneResolvent_apply,\n"
        "    ContinuousLinearMap.smul_apply,\n"
        "    QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffEscapeHamiltonian_apply]\n",
        (Header(61032, 4, "Tactic `rewrite` failed"),),
        rationale="Reduce scalar multiplication of the continuous linear map before rewriting its application.",
    ),
    Rule(
        "continuous_linear_map_zero_use_single_extensionality_layer",
        "    apply hQ\n"
        "    ext x\n"
        "    exact h x\n",
        "    apply hQ\n"
        "    apply ContinuousLinearMap.ext\n"
        "    intro x\n"
        "    simpa using h x\n",
        (Header(61056, 4, "Type mismatch"),),
        rationale="Do not let the generic ext tactic descend through the Lp subtype into an a.e. equality goal.",
    ),
    Rule(
        "half_scalar_norm_use_numeric_normalization",
        "    rw [hApply, norm_smul, Complex.norm_real,\n"
        "      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]\n",
        "    rw [hApply, norm_smul]\n"
        "    norm_num\n",
        (Header(61066, 27, "Tactic `rewrite` failed"),),
        rationale="The scalar is already a complex division term, not syntactically a coerced real; norm_num closes its norm directly.",
    ),
    Rule(
        "eventual_triviality_use_range_zero_api",
        "  simp [QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffMovingOffGround, hn]\n",
        "  rw [QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffMovingOffGround, hn]\n"
        "  exact LinearMap.range_zero\n",
        (Header(61142, 124, "unsolved goals"),),
        rationale="Close the residual LinearMap.range 0 = bottom with its dedicated theorem.",
    ),
    Rule(
        "escape_energy_limit_normalize_zero_norm_power",
        "  simpa [actualCutoffEscapeEnergy] using hNorm.pow 2\n",
        "  simpa only [actualCutoffEscapeEnergy, norm_zero,\n"
        "    zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hNorm.pow 2\n",
        (Header(61184, 2, "Type mismatch: After simplification"),),
        rationale="Normalize the target limit norm-zero squared to literal zero.",
    ),
    Rule(
        "limit_ground_block_use_kernel_zero_api",
        "theorem actualCutoffLimitGroundBlock_eq_top :\n"
        "    actualCutoffLimitGroundBlock = ⊤ := by\n"
        "  ext u\n"
        "  simp [actualCutoffLimitGroundBlock]\n",
        "theorem actualCutoffLimitGroundBlock_eq_top :\n"
        "    actualCutoffLimitGroundBlock = ⊤ := by\n"
        "  rw [actualCutoffLimitGroundBlock]\n"
        "  exact LinearMap.ker_zero\n",
        (Header(61221, 40, "unsolved goals"),),
        rationale="Use the exact kernel-of-zero theorem instead of relying on subtype-membership simp.",
    ),
    Rule(
        "limit_off_ground_block_use_top_orthogonal_api",
        "theorem actualCutoffLimitOffGroundBlock_eq_bot :\n"
        "    actualCutoffLimitOffGroundBlock = ⊥ := by\n"
        "  simp [actualCutoffLimitOffGroundBlock,\n"
        "    actualCutoffLimitGroundBlock_eq_top]\n",
        "theorem actualCutoffLimitOffGroundBlock_eq_bot :\n"
        "    actualCutoffLimitOffGroundBlock = ⊥ := by\n"
        "  rw [actualCutoffLimitOffGroundBlock,\n"
        "    actualCutoffLimitGroundBlock_eq_top]\n"
        "  exact Submodule.top_orthogonal_eq_bot\n",
        (Header(61226, 43, "unsolved goals"),),
        rationale="Close top-orthogonal = bottom with the dedicated inner-product-space theorem.",
    ),
    Rule(
        "limit_off_ground_nonzero_eliminate_bottom_membership",
        "theorem actualCutoffLimit_has_no_nonzero_offGroundVector :\n"
        "    ¬ ∃ u : ActualGlobalL2,\n"
        "      u ∈ actualCutoffLimitOffGroundBlock ∧ u ≠ 0 := by\n"
        "  rw [actualCutoffLimitOffGroundBlock_eq_bot]\n"
        "  simp\n",
        "theorem actualCutoffLimit_has_no_nonzero_offGroundVector :\n"
        "    ¬ ∃ u : ActualGlobalL2,\n"
        "      u ∈ actualCutoffLimitOffGroundBlock ∧ u ≠ 0 := by\n"
        "  rintro ⟨u, hu, hne⟩\n"
        "  rw [actualCutoffLimitOffGroundBlock_eq_bot] at hu\n"
        "  exact hne (Submodule.mem_bot.mp hu)\n",
        (Header(61233, 53, "unsolved goals"),),
        rationale="Eliminate the bottom-submodule membership explicitly, avoiding subtype representation simp.",
    ),
)


DELIBERATE_CASCADES_NOT_PATCHED = (
    25161, 25174, 26424, 28279, 28289, 28346,
    57619, 57620, 59833, 59834, 59836,
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8")
    return {
        "sha256": sha256(data),
        "git_blob": git_blob(data),
        "bytes": len(data),
        "lf": data.count(b"\n"),
        "cr": b"\r" in data,
        "nul": b"\0" in data,
        "bom": data.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": data.endswith(b"\n"),
    }


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def expected(inverse: bool, result: bool) -> tuple[str, str, int, int]:
    source = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    output = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    if inverse:
        source, output = output, source
    return output if result else source


def check_shape(
    actual: dict[str, object],
    wanted: tuple[str, str, int, int],
    *,
    allow_unsealed: bool = False,
) -> None:
    if wanted[0] == "__TO_SEAL__" and allow_unsealed:
        return
    for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
        if actual[key] != value:
            raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_log(log: bytes) -> list[dict[str, object]]:
    if sha256(log) != LOG_SHA256:
        raise RuntimeError(f"Probe6 log sha256 {sha256(log)} != {LOG_SHA256}")
    text = log.decode("utf-8")
    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = re.compile(
                rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
            )
            count = len(pattern.findall(text))
            if count != 1:
                raise RuntimeError(
                    f"{rule.label}: diagnostic {header.line}:{header.column} "
                    f"{header.message!r} count {count}, expected 1"
                )
            verified.append(
                {
                    "rule": rule.label,
                    "line": header.line,
                    "column": header.column,
                    "message": header.message,
                    "count": count,
                }
            )
    return verified


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    rules = tuple(reversed(RULES)) if inverse else RULES
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact count {count}, expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "direct_headers": [
                    {"line": h.line, "column": h.column, "message": h.message}
                    for h in rule.headers
                ],
                "rationale": rule.rationale,
            }
        )
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe6-log", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        expected(inverse, False),
        allow_unsealed=args.bootstrap_seal and inverse,
    )
    log_headers = verify_log(args.probe6_log.read_bytes())

    source_text = source.decode("utf-8")
    before_trust = trust(source_text)
    result_text, rule_audit = transform(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust changed: {before_trust} -> {after_trust}")
    if any(after_trust.values()):
        raise RuntimeError(f"nonzero trust inventory: {after_trust}")

    restored_text, _ = transform(result_text, not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_REANCHORED_INSTALL_READY_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe6_run_id": 31966015791,
            "probe6_job_id": 95211191616,
            "probe6_artifact_id": 9268603768,
            "probe6_candidate_sha256": INPUT_SHA256,
            "probe6_candidate_git_blob": INPUT_GIT_BLOB,
            "probe6_log_sha256": LOG_SHA256,
            "probe6_error_headers": 446,
            "probe6_warning_headers": 380,
            "probe6_panic": 0,
            "probe6_exit": 1,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "active_occurrences": sum(r["occurrences"] for r in rule_audit),
        "direct_headers_verified": len(log_headers),
        "rules": rule_audit,
        "selected_exact_probe6_lines": sorted(
            {h.line for rule in RULES for h in rule.headers}
        ),
        "deliberate_cascades_not_patched": list(DELIBERATE_CASCADES_NOT_PATCHED),
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
