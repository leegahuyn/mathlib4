#!/usr/bin/env python3
"""Conditional, byte-reversible Probe6 projection over the exact Probe5 candidate.

This helper is deliberately static.  It does not invoke Lean/Lake, modify the
checked-in source, or access a remote.  Every repair is an exact, occurrence-
counted replacement tied to an observed Probe4 diagnostic header.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path


EXPECTED_INPUT_SHA256 = "30edb320b25eadbfda284160016a5a23cc28a95d6228cbd061161d4ec615de7c"
EXPECTED_INPUT_GIT_BLOB = "9ea2ef7d03555cca4e82cbeeb01cba033dff6b99"
EXPECTED_INPUT_BYTES = 2_911_806
EXPECTED_INPUT_LF = 61_557

# Filled after the first mechanically verified forward projection.
EXPECTED_OUTPUT_SHA256 = "1d66e3a0cdc3446babe651d64dcc99e0b0f55ff282f0908d048b360dfd6f37df"
EXPECTED_OUTPUT_GIT_BLOB = "7cdc3e3da1afcbc8c77b7d1c5cdaa30c7d3de775"
EXPECTED_OUTPUT_BYTES = 2_911_882
EXPECTED_OUTPUT_LF = 61_554

PROBE4_LOG_SHA256 = "3ce6d19d831d1723b19fb15181e9561cb1e6b8744e130812838469a03011ddc6"
PROBE4_HEADERS_SHA256 = "a9b9ae54fcc4f44800bff26a75f6513beeaa469601df8aba7418a20e04356431"


@dataclass(frozen=True)
class ExactRule:
    label: str
    old: str
    new: str
    occurrences: int
    probe4_error_lines: tuple[int, ...]
    probe5_anchor_lines: tuple[int, ...]
    class_name: str
    rationale: str


RULES: tuple[ExactRule, ...] = (
    ExactRule(
        "domain_graph_map_componentwise_linearity",
        "  map_add' x y := by\n"
        "    apply Subtype.ext\n"
        "    ext <;> simp only [Submodule.coe_add, LinearPMap.map_add]\n"
        "  map_smul' a x := by\n"
        "    apply Subtype.ext\n"
        "    ext <;> simp only [Submodule.coe_smul, LinearPMap.map_smul]",
        "  map_add' x y := by\n"
        "    apply Subtype.ext\n"
        "    apply Prod.ext\n"
        "    · change ((x + y : D.domain) : H) = (x : H) + (y : H)\n"
        "      rfl\n"
        "    · change D (x + y) = D x + D y\n"
        "      exact LinearPMap.map_add D x y\n"
        "  map_smul' a x := by\n"
        "    apply Subtype.ext\n"
        "    apply Prod.ext\n"
        "    · change ((a • x : D.domain) : H) = a • (x : H)\n"
        "      rfl\n"
        "    · change D (a • x) = a • D x\n"
        "      exact LinearPMap.map_smul D a x",
        1, (26034, 26037), (26051, 26054), "explicit_componentwise_linearity",
        "The Probe5 goals expose only the two product coordinates; explicit Prod.ext and LinearPMap map laws avoid opaque product projections.",
    ),
    ExactRule(
        "operator_eigenvalue_nonresolvent_ring_normalization",
        "  apply sub_ne_zero.mp\n"
        "  simpa only [operatorEigenvalue, sub_sub_cancel_left] using\n"
        "    inv_ne_zero (resolventEigenvalue_ne_zero ρ ν)",
        "  apply sub_ne_zero.mp\n"
        "  have hdiff : z - (z - (ν : 𝕜)⁻¹) = (ν : 𝕜)⁻¹ := by ring\n"
        "  rw [hdiff]\n"
        "  exact inv_ne_zero (resolventEigenvalue_ne_zero ρ ν)",
        1, (26398,), (26414, 26415, 26416), "exact_ring_normalization",
        "The actual residual is exactly z - (z - nu^-1) != 0; the previous cancellation lemma has the wrong syntactic shape.",
    ),
    ExactRule(
        "operator_eigenspace_ring_normalization",
        "  have hzν := operatorEigenvalue_ne_resolventParameter ρ ν\n"
        "  simpa only [operatorEigenvalue, sub_sub_cancel_left, inv_inv] using\n"
        "    QYM.UnboundedCompactSpectralMappingExtension.operatorEigenspace_eq_resolventEigenspace ρ hzν",
        "  have hzν := operatorEigenvalue_ne_resolventParameter ρ ν\n"
        "  have hdiff : z - (z - (ν : 𝕜)⁻¹) = (ν : 𝕜)⁻¹ := by ring\n"
        "  simpa only [operatorEigenvalue, hdiff, inv_inv] using\n"
        "    QYM.UnboundedCompactSpectralMappingExtension.operatorEigenspace_eq_resolventEigenspace ρ hzν",
        1, (26409,), (26425, 26426, 26427), "exact_ring_normalization",
        "Normalizes the exact nested subtraction printed in the Probe5 target before inv_inv.",
    ),
    ExactRule(
        "eta_core_inverse_element_explicit_coeFn",
        "    inverseEtaCoreElement Y tau = inverseEtaSection tau := by",
        "    (inverseEtaCoreElement Y : H → ℂ) tau = inverseEtaSection tau := by",
        1, (27790,), (27798,), "explicit_subtype_function_coercion",
        "The observed term is a Submodule subtype and Lean does not chain its coercion to a function in application position.",
    ),
    ExactRule(
        "eta_core_bundle_lift_explicit_coeFn",
        "  Mock2.Definition15Geometry.lineBundleMk etaMultiplier (tau, f tau)",
        "  Mock2.Definition15Geometry.lineBundleMk etaMultiplier (tau, (f : H → ℂ) tau)",
        1, (27798,), (27806,), "explicit_subtype_function_coercion",
        "Makes the pointwise representative explicit at the bundle-lift producer.",
    ),
    ExactRule(
        "eta_core_invariance_pair_explicit_coeFn",
        "      Mock2.Definition15Geometry.lineSmul etaMultiplier gamma (tau, f tau) =\n"
        "        (gamma • tau, f (gamma • tau)) := by",
        "      Mock2.Definition15Geometry.lineSmul etaMultiplier gamma (tau, (f : H → ℂ) tau) =\n"
        "        (gamma • tau, (f : H → ℂ) (gamma • tau)) := by",
        1, (27813, 27814), (27821, 27822), "explicit_subtype_function_coercion",
        "Fixes both function-expected sites in the stored line-action equality.",
    ),
    ExactRule(
        "eta_core_invariance_final_explicit_coeFn",
        "    etaMultiplier gamma (tau, f tau)",
        "    etaMultiplier gamma (tau, (f : H → ℂ) tau)",
        1, (27820,), (27828,), "explicit_subtype_function_coercion",
        "Fixes the final lineBundleMk_lineSmul application after the producer equality.",
    ),
    ExactRule(
        "petersson_integrand_explicit_coeFns",
        "  ∫ tau : H, inner ℂ (f tau) (g tau) ∂truncatedHyperbolicMeasure Y",
        "  ∫ tau : H, inner ℂ ((f : H → ℂ) tau) ((g : H → ℂ) tau) ∂truncatedHyperbolicMeasure Y",
        1, (27859, 27859), (27867,), "explicit_subtype_function_coercion",
        "Fixes both observed function-expected headers at the Petersson integral producer.",
    ),
    ExactRule(
        "closed_ball_indicator_restricted_ae_direct",
        "  apply MeasureTheory.MemLp.toLp_congr\n"
        "  exact MeasureTheory.indicator_ae_eq_restrict\n"
        "    (μ := (volume : Measure H))\n"
        "    (hyperbolicClosedBallTruncation_measurable Y)",
        "  apply MeasureTheory.MemLp.toLp_congr\n"
        "  filter_upwards [\n"
        "    MeasureTheory.ae_restrict_mem\n"
        "      (hyperbolicClosedBallTruncation_measurable Y)] with tau htau\n"
        "  exact Set.indicator_of_mem htau _",
        1, (27910,), (27917, 27918, 27919, 27920), "direct_api_replacement",
        "Replaces the nonexistent namespaced helper with the already-used ae_restrict_mem fact and Set.indicator_of_mem.",
    ),
    ExactRule(
        "eta_section_smooth_explicit_namespace",
        "  exact g.smooth.div₀ EtaHalfWeight.etaValue_contMDiff",
        "  exact (SmoothInvariantScalar.smooth g).div₀ EtaHalfWeight.etaValue_contMDiff",
        1, (28172,), (28180,), "explicit_namespace_method",
        "Dot projection searches Subtype.smooth; the theorem lives under the explicit SmoothInvariantScalar namespace.",
    ),
    ExactRule(
        "eta_section_invariant_explicit_namespace",
        "  rw [etaSection, etaSection, g.invariant γ τ, EtaHalfWeight.etaRatio]",
        "  rw [etaSection, etaSection, SmoothInvariantScalar.invariant g γ τ, EtaHalfWeight.etaRatio]",
        1, (28180,), (28188,), "explicit_namespace_method",
        "Avoids the failed Subtype.invariant field projection at the covariance producer.",
    ),
    ExactRule(
        "eta_section_linear_map_smul_reduce_ringhom_id",
        "    simp only [etaSection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]\n"
        "    ring",
        "    simp only [etaSection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,\n"
        "      RingHom.id_apply]\n"
        "    ring",
        1, (28201,), (28212, 28213), "direct_api_replacement",
        "The logged residual differs only by the unreduced `(RingHom.id ℂ) c` scalar.",
    ),
    ExactRule(
        "eta_trivialization_smooth_explicit_namespace",
        "  exact EtaHalfWeight.etaValue_contMDiff.mul f.smooth",
        "  exact EtaHalfWeight.etaValue_contMDiff.mul (SmoothEtaCovariantSection.smooth f)",
        1, (28214,), (28222,), "explicit_namespace_method",
        "Avoids the failed Subtype.smooth field projection.",
    ),
    ExactRule(
        "eta_trivialization_covariant_explicit_namespace",
        "  rw [etaTrivialization, etaTrivialization, f.covariant γ τ,\n"
        "    EtaHalfWeight.etaRatio]",
        "  rw [etaTrivialization, etaTrivialization,\n"
        "    SmoothEtaCovariantSection.covariant f γ τ, EtaHalfWeight.etaRatio]",
        1, (28219,), (28227, 28228), "explicit_namespace_method",
        "Avoids the failed Subtype.covariant field projection at the trivialization producer.",
    ),
    ExactRule(
        "eta_trivialization_linear_map_smul_reduce_ringhom_id",
        "    simp only [etaTrivialization, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]\n"
        "    ring",
        "    simp only [etaTrivialization, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,\n"
        "      RingHom.id_apply]\n"
        "    ring",
        1, (28235,), (28246, 28247), "direct_api_replacement",
        "Reduces the exact RingHom.id scalar displayed by the residual goal.",
    ),
    ExactRule(
        "manifold_deck_map_smooth_explicit_target",
        "  simpa only [manifoldDeckMap] using deckAction_contMDiff γ",
        "  change ContMDiff \U0001d4d8(ℂ) \U0001d4d8(ℂ) ∞ (fun τ : H => γ • τ)\n"
        "  exact deckAction_contMDiff γ",
        1, (28282,), (28290,), "explicit_target_bridge",
        "Pins the exact function shown in the actual theorem type instead of relying on alias simplification.",
    ),
    ExactRule(
        "raw_differential_deck_explicit_methods_and_top_degree",
        "  have hgAt : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) g.1 (γ • τ) :=\n"
        "    (g.smooth.mdifferentiable one_ne_zero) (γ • τ)\n"
        "  have hdeckAt :\n"
        "      MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) (manifoldDeckMap γ) τ :=\n"
        "    (manifoldDeckMap_smooth γ).mdifferentiable one_ne_zero τ\n"
        "  have hfun : g.1 ∘ manifoldDeckMap γ = g.1 := by\n"
        "    funext σ\n"
        "    exact g.invariant γ σ",
        "  have hgAt : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) g.1 (γ • τ) :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) (γ • τ)\n"
        "  have hdeckAt :\n"
        "      MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) (manifoldDeckMap γ) τ :=\n"
        "    (manifoldDeckMap_smooth γ).mdifferentiable (by simp) τ\n"
        "  have hfun : g.1 ∘ manifoldDeckMap γ = g.1 := by\n"
        "    funext σ\n"
        "    exact SmoothInvariantScalar.invariant g γ σ",
        1, (28301, 28304), (28308, 28309, 28310, 28311, 28312, 28313, 28314, 28315),
        "explicit_namespace_and_degree",
        "Fixes the invalid field lookup and supplies the required infinity-ne-zero proof instead of one-ne-zero.",
    ),
    ExactRule(
        "raw_differential_add_explicit_methods_and_top_degree",
        "  have hg : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) g.1 τ :=\n"
        "    (g.smooth.mdifferentiable one_ne_zero) τ\n"
        "  have hh : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) h.1 τ :=\n"
        "    (h.smooth.mdifferentiable one_ne_zero) τ",
        "  have hg : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) g.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ\n"
        "  have hh : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) h.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth h).mdifferentiable (by simp)) τ",
        1, (28323, 28325), (28330, 28331, 28332, 28333), "explicit_namespace_and_degree",
        "Repairs both hidden derivative hypotheses before the additive mfderiv API call.",
    ),
    ExactRule(
        "raw_differential_smul_explicit_method_and_top_degree",
        "theorem rawDifferential_smul\n"
        "    (c : ℂ) (g : SmoothInvariantScalar) (τ : H) :\n"
        "    rawDifferential (c • g) τ = c • rawDifferential g τ := by\n"
        "  have hg : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) g.1 τ :=\n"
        "    (g.smooth.mdifferentiable one_ne_zero) τ",
        "theorem rawDifferential_smul\n"
        "    (c : ℂ) (g : SmoothInvariantScalar) (τ : H) :\n"
        "    rawDifferential (c • g) τ = c • rawDifferential g τ := by\n"
        "  have hg : MDifferentiableAt \U0001d4d8(ℂ) \U0001d4d8(ℂ) g.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ",
        1, (28332,), (28339, 28340), "explicit_namespace_and_degree",
        "Repairs the scalar derivative hypothesis with the actual namespace theorem and smoothness degree.",
    ),
    ExactRule(
        "constant_one_invariant_explicit_coeFn",
        "    constantOneInvariant tau = 1 := by",
        "    (constantOneInvariant : H → ℂ) tau = 1 := by",
        1, (28674,), (28682,), "explicit_subtype_function_coercion",
        "Fixes the H1 producer's first function-expected header; its dependent simp proof can then use the lemma.",
    ),
    ExactRule(
        "inverse_eta_h1_element_explicit_nested_coeFn",
        "    (inverseEtaH1CoreElement Y : SmoothInvariantScalar) tau = 1 := by",
        "    ((inverseEtaH1CoreElement Y : SmoothInvariantScalar) : H → ℂ) tau = 1 := by",
        1, (28712,), (28720,), "explicit_subtype_function_coercion",
        "Makes both layers of Submodule subtype coercion explicit.",
    ),
    ExactRule(
        "eta_h1_scalar_l2_map_smul_reduce_ringhom_id",
        "    simpa only [etaH1CoreScalarToL2, Submodule.coe_smul, etaSection_smul] using\n"
        "      (MemLp.toLp_const_smul c g.property.1)",
        "    simpa only [etaH1CoreScalarToL2, Submodule.coe_smul, etaSection_smul,\n"
        "      RingHom.id_apply] using\n"
        "      (MemLp.toLp_const_smul c g.property.1)",
        1, (28748,), (28756, 28757), "direct_api_replacement",
        "The actual and expected terms differ only by the unreduced identity ring homomorphism.",
    ),
    ExactRule(
        "eta_h1_oneform_l2_map_smul_reduce_ringhom_id",
        "    simpa only [etaH1CoreOneFormToL2, Submodule.coe_smul,\n"
        "      etaGaugeOneFormCoefficient_smul] using\n"
        "      (MemLp.toLp_const_smul c g.property.2)",
        "    simpa only [etaH1CoreOneFormToL2, Submodule.coe_smul,\n"
        "      etaGaugeOneFormCoefficient_smul, RingHom.id_apply] using\n"
        "      (MemLp.toLp_const_smul c g.property.2)",
        1, (28780,), (28788, 28789, 28790), "direct_api_replacement",
        "Reduces the identity ring homomorphism shown verbatim by the second L2 coordinate residual.",
    ),
    ExactRule(
        "eta_trivialized_scalar_explicit_coeFn",
        "noncomputable def etaTrivializedScalar (Y : ℝ)\n"
        "    (f : etaSmoothAutomorphicCore Y) (tau : H) : ℂ :=\n"
        "  Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * f tau",
        "noncomputable def etaTrivializedScalar (Y : ℝ)\n"
        "    (f : etaSmoothAutomorphicCore Y) (tau : H) : ℂ :=\n"
        "  Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * (f : H → ℂ) tau",
        1, (29264,), (29272,), "explicit_subtype_function_coercion",
        "Fixes the downstream quotient scalar producer rather than its later MemLp cascades.",
    ),
    ExactRule(
        "eta_trivialized_invariance_explicit_coeFns",
        "    Mock2.Definition15Geometry.EtaHalfWeight.etaValue (gamma • tau) *\n"
        "        f (gamma • tau) =\n"
        "      Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * f tau",
        "    Mock2.Definition15Geometry.EtaHalfWeight.etaValue (gamma • tau) *\n"
        "        (f : H → ℂ) (gamma • tau) =\n"
        "      Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * (f : H → ℂ) tau",
        1, (29287, 29288), (29294, 29295, 29296), "explicit_subtype_function_coercion",
        "Fixes both function-expected sites in the exact covariance cancellation proof.",
    ),
    ExactRule(
        "eta_core_bundle_measurable_explicit_coeFn",
        "      (Quotient.mk' (tau, f tau) : EtaAutomorphicLineBundle.Total))",
        "      (Quotient.mk' (tau, (f : H → ℂ) tau) : EtaAutomorphicLineBundle.Total))",
        1, (29467,), (29475,), "explicit_subtype_function_coercion",
        "Pins the pointwise function at the measurable associated-bundle lift producer.",
    ),
    ExactRule(
        "type_final_quotient_measure_infinity",
        "      truncatedQuotientMeasure Y Set.univ < ∞ ∧",
        "      truncatedQuotientMeasure Y Set.univ < (∞ : ℝ≥0∞) ∧",
        1, (29525,), (29533,), "explicit_type_annotation",
        "The actual diagnostic lists exactly ℕ∞ω and ℝ≥0∞; the measure codomain fixes the latter.",
    ),
    ExactRule(
        "gauge_deck_submodule_explicit_record_binders",
        "  add_mem' a b ha hb := by\n"
        "    intro gamma\n"
        "    rw [(deckPullback gamma).map_add, ha gamma, hb gamma]\n"
        "  smul_mem' c a ha := by\n"
        "    intro gamma\n"
        "    rw [(deckPullback gamma).map_smul, ha gamma]",
        "  add_mem' := by\n"
        "    intro a b ha hb gamma\n"
        "    rw [(deckPullback gamma).map_add, ha gamma, hb gamma]\n"
        "  smul_mem' := by\n"
        "    intro c a ha gamma\n"
        "    rw [(deckPullback gamma).map_smul, ha gamma]",
        1, (30840, 30841, 30860), (30848, 30849, 30850, 30851, 30852, 30853),
        "cascade_producer_record_binders",
        "The log explicitly says the element variables were already introduced by implicit lambdas; this repairs the declaration owner.",
    ),
    ExactRule(
        "pmap_eigenspace_membership_namespace_join",
        "  obtain ⟨hxMem, _⟩ := hx\n"
        "  obtain ⟨hxDomain, hxEq⟩ :=\n"
        "    QYM.UnboundedCompactSpectralMappingExtension.\n"
        "      mem_operatorEigenspace_iff.mp hxMem",
        "  obtain ⟨hxMem, _⟩ := hx\n"
        "  obtain ⟨hxDomain, hxEq⟩ :=\n"
        "    QYM.UnboundedCompactSpectralMappingExtension.mem_operatorEigenspace_iff.mp hxMem",
        1, (30088, 30088), (30096, 30097), "trailing_dot_namespace_join",
        "The exact Probe5 source contains one split qualified identifier and the authority reports the matching unknown-namespace plus invalid-field pair.",
    ),
    ExactRule(
        "eta_covariant_lift_module_explicit_record_binders",
        "  add_mem' f g hf hg := by\n"
        "    intro gamma tau\n"
        "    change\n"
        "      f (gamma • tau) + g (gamma • tau) =\n"
        "        QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.etaAutomorphyFactor gamma tau * (f tau + g tau)\n"
        "    rw [hf gamma tau, hg gamma tau, mul_add]\n"
        "  smul_mem' c f hf := by\n"
        "    intro gamma tau",
        "  add_mem' := by\n"
        "    intro f g hf hg gamma tau\n"
        "    change\n"
        "      f (gamma • tau) + g (gamma • tau) =\n"
        "        QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.etaAutomorphyFactor gamma tau * (f tau + g tau)\n"
        "    rw [hf gamma tau, hg gamma tau, mul_add]\n"
        "  smul_mem' := by\n"
        "    intro c f hf gamma tau",
        1, (47986,), (48019, 48020, 48021, 48022, 48023, 48024, 48025, 48026),
        "cascade_producer_record_binders",
        "Repairs the second surviving implicit-lambda Submodule owner before its quotient-section cascade.",
    ),
    ExactRule(
        "conditional_manifold_instance_remove_spurious_argument",
        "local instance conditionalIsManifold :\n"
        "    IsManifold \U0001d4d8(ℂ) ∞ GammaTwoQuotient :=\n"
        "  gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth",
        "local instance conditionalIsManifold :\n"
        "    IsManifold \U0001d4d8(ℂ) ∞ GammaTwoQuotient :=\n"
        "  gammaTwoQuotient_isManifold_of_smoothTransitionResidual",
        1, (44992,), (45007,), "direct_api_replacement",
        "The observed theorem already has the target IsManifold type and takes no argument.",
    ),
    ExactRule(
        "idempotent_positive_field_projection_parenthesized",
        "  (actualInverseEtaProjectionHamiltonian_isIdempotent hY)\n"
        "    .isPositive_iff_isSelfAdjoint.mpr\n"
        "    (actualInverseEtaProjectionHamiltonian_isSelfAdjoint hY)",
        "  (actualInverseEtaProjectionHamiltonian_isIdempotent hY).isPositive_iff_isSelfAdjoint.mpr\n"
        "    (actualInverseEtaProjectionHamiltonian_isSelfAdjoint hY)",
        1, (56132,), (56166, 56167, 56168), "direct_api_replacement",
        "Keeps the field projection attached to the idempotence proof instead of parsing it as a function argument.",
    ),
    ExactRule(
        "physical_raise_closable_remove_obsolete_green_argument",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise n).IsClosable :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise_isClosable n\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual n)",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise n).IsClosable :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise_isClosable n",
        1, (57670,), (57704, 57705, 57706), "direct_api_replacement",
        "The actual API theorem already has the complete target IsClosable type.",
    ),
    ExactRule(
        "physical_lower_closable_remove_obsolete_green_argument",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc n).IsClosable :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc_isClosable n\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual n)",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc n).IsClosable :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc_isClosable n",
        1, (57680,), (57714, 57715, 57716), "direct_api_replacement",
        "The actual API theorem already has the complete target IsClosable type.",
    ),
    ExactRule(
        "physical_joint_closable_remove_obsolete_green_arguments",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc n).IsClosable :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc_isClosable n\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual n)\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual (n + 1))",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc n).IsClosable :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc_isClosable n",
        1, (57690,), (57724, 57725, 57726, 57727, 57728), "direct_api_replacement",
        "The joint API theorem is already unconditional at the current FA authority.",
    ),
    ExactRule(
        "closed_raise_remove_obsolete_green_argument",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise n).IsClosed :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise_isClosed n\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual n)",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise n).IsClosed :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise_isClosed n",
        1, (57702,), (57736, 57737, 57738), "direct_api_replacement",
        "The actual API theorem already has the complete target IsClosed type.",
    ),
    ExactRule(
        "closed_lower_remove_obsolete_green_argument",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc n).IsClosed :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc_isClosed n\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual n)",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc n).IsClosed :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc_isClosed n",
        1, (57712,), (57746, 57747, 57748), "direct_api_replacement",
        "The actual API theorem already has the complete target IsClosed type.",
    ),
    ExactRule(
        "closed_joint_remove_obsolete_green_arguments",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc n).IsClosed :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc_isClosed n\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual n)\n"
        "    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n"
        "      hResidual (n + 1))",
        "    (n : ℤ) : (Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc n).IsClosed :=\n"
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc_isClosed n",
        1, (57722,), (57756, 57757, 57758, 57759, 57760), "direct_api_replacement",
        "The joint API theorem is already unconditional at the current FA authority.",
    ),
)


TRUST_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"\baxiom\b"),
    "declaration_ax": re.compile(r"\bAx\b"),
    "classical_choice": re.compile(r"\bClassical\.choice\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "false_elim": re.compile(r"\bFalse\.elim\b"),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def identity(data: bytes) -> dict[str, object]:
    return {
        "sha256": sha256(data),
        "git_blob": git_blob(data),
        "bytes": len(data),
        "lf": data.count(b"\n"),
        "cr": data.count(b"\r"),
        "nul": data.count(b"\0"),
        "bom": data.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": data.endswith(b"\n"),
    }


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def require_identity(actual: dict[str, object], expected: dict[str, object], label: str) -> None:
    for key, value in expected.items():
        if actual[key] != value:
            raise SystemExit(f"{label} {key} mismatch: expected {value!r}, got {actual[key]!r}")


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    ordered = tuple(reversed(RULES)) if inverse else RULES
    details: list[dict[str, object]] = []
    for rule in ordered:
        before = rule.new if inverse else rule.old
        after = rule.old if inverse else rule.new
        count = text.count(before)
        if count != rule.occurrences:
            raise SystemExit(
                f"{rule.label}: expected {rule.occurrences} active occurrence(s), got {count}"
            )
        opposite = text.count(after)
        embedded_opposite = before.count(after) * count
        if opposite != embedded_opposite:
            raise SystemExit(
                f"{rule.label}: unexpected opposite-form count {opposite}; "
                f"only {embedded_opposite} embedded occurrence(s) are allowed"
            )
        text = text.replace(before, after)
        details.append({
            "label": rule.label,
            "occurrences": count,
            "probe4_error_lines": list(rule.probe4_error_lines),
            "probe5_anchor_lines": list(rule.probe5_anchor_lines),
            "class": rule.class_name,
            "rationale": rule.rationale,
        })
    return text, details


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    parser.add_argument("--inverse", action="store_true")
    args = parser.parse_args()

    source = args.input.read_bytes()
    source_id = identity(source)
    expected_source = (
        {
            "sha256": EXPECTED_OUTPUT_SHA256,
            "git_blob": EXPECTED_OUTPUT_GIT_BLOB,
            "bytes": EXPECTED_OUTPUT_BYTES,
            "lf": EXPECTED_OUTPUT_LF,
            "cr": 0,
            "nul": 0,
            "bom": False,
            "terminal_lf": True,
        }
        if args.inverse
        else {
            "sha256": EXPECTED_INPUT_SHA256,
            "git_blob": EXPECTED_INPUT_GIT_BLOB,
            "bytes": EXPECTED_INPUT_BYTES,
            "lf": EXPECTED_INPUT_LF,
            "cr": 0,
            "nul": 0,
            "bom": False,
            "terminal_lf": True,
        }
    )
    require_identity(source_id, expected_source, "input")
    source_text = source.decode("utf-8")
    projected_text, details = transform(source_text, inverse=args.inverse)
    projected = projected_text.encode("utf-8")
    result_id = identity(projected)

    expected_result = (
        {
            "sha256": EXPECTED_INPUT_SHA256,
            "git_blob": EXPECTED_INPUT_GIT_BLOB,
            "bytes": EXPECTED_INPUT_BYTES,
            "lf": EXPECTED_INPUT_LF,
            "cr": 0,
            "nul": 0,
            "bom": False,
            "terminal_lf": True,
        }
        if args.inverse
        else {
            "sha256": EXPECTED_OUTPUT_SHA256,
            "git_blob": EXPECTED_OUTPUT_GIT_BLOB,
            "bytes": EXPECTED_OUTPUT_BYTES,
            "lf": EXPECTED_OUTPUT_LF,
            "cr": 0,
            "nul": 0,
            "bom": False,
            "terminal_lf": True,
        }
    )
    if EXPECTED_OUTPUT_SHA256 != "__PROBE6_OUTPUT_SHA256__":
        require_identity(result_id, expected_result, "output")

    before_trust = trust_counts(source_text)
    after_trust = trust_counts(projected_text)
    if before_trust != after_trust:
        raise SystemExit(f"trust-token counts changed: {before_trust!r} -> {after_trust!r}")

    args.output.write_bytes(projected)
    audit = {
        "schema": "qym-probe6-conditional-transform-v1",
        "status": "STATIC_FORWARD_PASS" if not args.inverse else "STATIC_INVERSE_PASS",
        "conditional": True,
        "promotion_authorized": False,
        "lean_executed": False,
        "lake_executed": False,
        "remote_accessed": False,
        "mode": "inverse" if args.inverse else "forward",
        "authority": {
            "probe5_candidate_sha256": EXPECTED_INPUT_SHA256,
            "probe5_candidate_git_blob": EXPECTED_INPUT_GIT_BLOB,
            "probe4_log_sha256": PROBE4_LOG_SHA256,
            "probe4_error_headers_sha256": PROBE4_HEADERS_SHA256,
        },
        "source": source_id,
        "result": result_id,
        "rules": details,
        "active_occurrences": sum(item["occurrences"] for item in details),
        "probe4_header_coordinates": sorted(
            line for item in details for line in item["probe4_error_lines"]
        ),
        "trust_counts_before": before_trust,
        "trust_counts_after": after_trust,
        "trust_delta_zero": True,
    }
    args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(audit, sort_keys=True))


if __name__ == "__main__":
    main()
