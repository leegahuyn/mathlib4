#!/usr/bin/env python3
"""Deterministic static probe-4 repairs for direct QYM roots on lines 20k--40k.

This transformer is deliberately tied to the immutable probe-3 candidate.  It
does not invoke Lean, Lake, GitHub, or Git.  Every rewrite is exact-count
guarded, the reverse transform is checked byte-for-byte, and trust-sensitive
token counts must be unchanged.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


EXPECTED_INPUT_SHA256 = "9e82073bdaf6339feb1ca09d70ab371947c6e07294ae01895a33c75f978bd780"
EXPECTED_LOG_SHA256 = "501029e514ba6bc875527e1bc96fb9f571afda222e53e633078736dccaa71f56"
EXPECTED_OUTPUT_SHA256 = "ba7726ac749bed9d19a20e313d2b651b8f80b14abbad363e2c879660d94cf885"


@dataclass(frozen=True)
class ExactRule:
    label: str
    old: str
    new: str
    expected: int = 1


def _zeros(arity: int) -> str:
    return ".{" + ", ".join("0" for _ in range(arity)) + "}"


# Each tuple is (label, namespace start, fully qualified statement, universe arity).
# Replacements are region-scoped to the relevant EvidenceStatement match only.
REGISTRY_UNIVERSE_RULES: tuple[tuple[str, str, tuple[tuple[str, int], ...]], ...] = (
    (
        "form_resolvent_spectral_registry",
        "namespace QYM.FullCertification.TypedEvidenceFormResolventSpectralExtension",
        (
            ("lemma4_13_realFormDomainRealizationStatement", 2),
            ("lemma4_13_realFormSymmetryPositivityStatement", 2),
            ("lemma4_16_realFormDenseClosableStatement", 2),
            ("lemma4_16_realFormSelfAdjointBoundaryStatement", 2),
            ("lemma4_18_linearPMapResolventBoundaryStatement", 2),
            ("lemma4_18_linearPMapResolventUniquenessStatement", 2),
            ("lemma4_18_linearPMapFirstResolventIdentityStatement", 2),
            ("lemma4_18_linearPMapCompactResolventTransferStatement", 2),
            ("prop4_23_linearPMapCompactResolventBoundedShiftBoundaryStatement", 2),
            ("prop4_23_infiniteDimensionalLinearPMapUnboundednessStatement", 2),
            ("hyp4_24_linearPMapCompactnessSupplierBoundaryStatement", 2),
            ("hyp4_24_bottomDomainNoResolventBoundaryStatement", 2),
            ("prop4_23_compactSelfAdjointSpectralPackageStatement", 2),
            ("prop4_23_groundComplementCoerciveGapStatement", 2),
            ("prop4_23_finiteDimensionalFirstOffGroundStatement", 2),
            ("prop4_23_compactInjectiveGroundGapNoGoStatement", 2),
            ("cor4_25_uniformGroundComplementGapStatement", 3),
        ),
    ),
    (
        "coercive_friedrichs_registry",
        "namespace QYM.FullCertification.TypedEvidenceCoerciveFriedrichsExtension",
        (
            ("lemma4_13_coerciveFriedrichsRealizationStatement", 2),
            ("lemma4_16_coerciveShiftUniqueSolutionStatement", 2),
            ("lemma4_18_coerciveFriedrichsResolventStatement", 2),
            ("prop4_23_coerciveFormCompactResolventStatement", 2),
        ),
    ),
    (
        "unconditional_fa_registry",
        "namespace QYM.FullCertification.TypedEvidenceUnconditionalFunctionalAnalysisExtension",
        (
            ("lemma4_30_boundedLinearPMapPerturbationB1ComponentStatement", 2),
            ("lemma4_30_boundedLinearPMapLowerBoundB1ComponentStatement", 1),
            ("def4_8_operatorRelativeFormSmallB2ComponentStatement", 2),
            ("lemma4_30_operatorRelativeResidualCoercivityB2ComponentStatement", 2),
            ("lemma4_30_operatorDirectResidualPrerequisiteStatement", 2),
            ("lemma4_30_operatorFormSmallFriedrichsB2ComponentStatement", 2),
            ("theorem4_31_operatorPrerequisiteLowerBoundStatement", 2),
            ("cor4_32_operatorPrerequisiteCompactResolventStatement", 2),
            ("lemma4_13_rclikeRealificationPrerequisiteStatement", 3),
            ("lemma4_13_rclikeCoerciveFriedrichsPrerequisiteStatement", 3),
            ("lemma4_16_rclikeShiftSolvabilityPrerequisiteStatement", 3),
            ("lemma4_18_rclikeResolventPrerequisiteStatement", 3),
            ("prop4_23_rclikeCompactResolventPrerequisiteStatement", 3),
            ("prop4_23_unboundedResolventEigenspaceMappingStatement", 2),
            ("prop4_23_unboundedResolventEigenpairCorrespondenceStatement", 2),
            ("prop4_23_unboundedKernelResolventCorrespondenceStatement", 2),
            ("prop4_23_unboundedCompactResolventFiniteMultiplicityStatement", 2),
            ("prop4_23_unboundedCompactSelfAdjointResolventPackageStatement", 2),
            ("prop4_23_unboundedOperatorEigenspacesCompleteStatement", 2),
            ("prop4_23_unboundedSelfAdjointEigenvaluesRealStatement", 2),
            ("theoremA_7_unboundedMultiplicitySafeLeastGapStatement", 1),
            ("theoremA_7_negativeResolventLocalFinitenessBoundaryStatement", 1),
            ("cor4_25_unboundedUniformMultiplicitySafeGapStatement", 2),
            ("theoremA_7_compactSelfAdjointPointSpectrumAwayFromZeroFinitePrerequisiteStatement", 2),
            ("theoremA_7_compactSelfAdjointAwayFromZeroSupplierConstructedStatement", 2),
            ("theoremA_7_negativeResolventLocalFinitenessWithoutSupplierStatement", 1),
            ("theoremA_7_unboundedMultiplicitySafeLeastGapWithoutSupplierStatement", 1),
            ("cor4_25_unboundedUniformMultiplicitySafeGapWithoutSupplierStatement", 2),
        ),
    ),
    (
        "closed_pure_discrete_gap_registry",
        "namespace QYM.FullCertification.TypedEvidenceClosedPureDiscreteGapExtension",
        (
            ("lemma4_13_closedDenseNonnegativeEnergyFormComponentStatement", 3),
            ("lemma4_13_closedGraphCoordinateLimitComponentStatement", 3),
            ("lemma4_18_compactResolventPurePointHilbertBasisComponentStatement", 2),
            ("lemma4_18_compactResolventPointSpectrumLocallyFiniteComponentStatement", 2),
            ("lemma4_18_compactResolventPointSpectrumCountableComponentStatement", 2),
            ("lemma4_18_nonnegativeFiniteFiberPointEigenvalueSequenceDivergesComponentStatement", 1),
            ("theoremA_7_constructedMultiplicitySafeGapWitnessStatement", 1),
            ("theoremA_7_pureDiscreteMultiplicitySafeGapPackageStatement", 1),
            ("theoremA_7_adjacentIndexGapBoundaryStatement", 1),
            ("theoremA_7_firstOffGroundIndexGapStatement", 1),
            ("cor4_25_constructedMultiplicitySafeGapFamilyLiminfStatement", 1),
        ),
    ),
)


RULES: tuple[ExactRule, ...] = (
    ExactRule(
        "pin_theoremA7_ground_gap_universes",
        "def theoremA_7_groundComplementCoerciveGapStatement : Prop :=\n"
        "  prop4_23_groundComplementCoerciveGapStatement\n",
        "def theoremA_7_groundComplementCoerciveGapStatement : Prop :=\n"
        "  prop4_23_groundComplementCoerciveGapStatement.{0, 0}\n",
    ),
    ExactRule(
        "close_shifted_form_associativity",
        "    _ = shiftedForm B j μ u u := by\n"
        "      simp only [shiftedForm_apply, real_inner_self_eq_norm_sq, pow_two]\n",
        "    _ = shiftedForm B j μ u u := by\n"
        "      simp only [shiftedForm_apply, real_inner_self_eq_norm_sq, pow_two] <;> ring\n",
    ),
    ExactRule(
        "expose_dense_range_lambda",
        "  simpa only [solutionMap, e, ContinuousLinearMap.coe_comp', Function.comp_def]\n"
        "    using hcomp\n",
        "  change DenseRange (fun h : H => e.symm (j.adjoint h))\n"
        "  change DenseRange (fun h : H => e.symm (j.adjoint h)) at hcomp\n"
        "  exact hcomp\n",
    ),
    ExactRule(
        "transport_domain_membership_by_equality",
        "    rw [← hxy]\n"
        "    exact x.property\n",
        "    exact hxy ▸ x.property\n",
        2,
    ),
    ExactRule(
        "remove_finished_negative_shift_simp",
        "  rw [coe_negativeShiftResolventDomainLift,\n"
        "    negativeShiftResolventInverse_apply,\n"
        "    unboundedShift_neg_eq_neg_positiveShift, map_neg]\n"
        "  simp only [neg_neg]\n"
        "  exact positiveInverse_positiveShift B j hj hjDense μ c hShift x\n",
        "  rw [coe_negativeShiftResolventDomainLift,\n"
        "    negativeShiftResolventInverse_apply,\n"
        "    unboundedShift_neg_eq_neg_positiveShift, map_neg]\n"
        "  exact positiveInverse_positiveShift B j hj hjDense μ c hShift x\n",
        2,
    ),
    ExactRule(
        "pin_rclike_I_scalar",
        "  have hIv := hRe (RCLike.I • v)\n",
        "  have hIv := hRe ((RCLike.I : 𝕜) • v)\n",
    ),
    ExactRule(
        "correct_shift_cancellation_side",
        "  exact sub_left_inj.mp hshift\n",
        "  exact sub_right_inj.mp hshift\n",
    ),
    ExactRule(
        "normalize_resolvent_difference_two_proofs",
        "  have hz : z ≠ z - ν⁻¹ := by\n"
        "    apply sub_ne_zero.mp\n"
        "    simpa only [sub_sub_cancel_left] using inv_ne_zero hν\n"
        "  have hscalar : (z - (z - ν⁻¹))⁻¹ = ν := by\n"
        "    rw [sub_sub_cancel_left, inv_inv]\n",
        "  have hdiff : z - (z - ν⁻¹) = ν⁻¹ := by ring\n"
        "  have hz : z ≠ z - ν⁻¹ := by\n"
        "    apply sub_ne_zero.mp\n"
        "    rw [hdiff]\n"
        "    exact inv_ne_zero hν\n"
        "  have hscalar : (z - (z - ν⁻¹))⁻¹ = ν := by\n"
        "    rw [hdiff, inv_inv]\n",
        2,
    ),
    ExactRule(
        "normalize_resolvent_difference_completion",
        "    · have hzν : z ≠ z - ν⁻¹ := by\n"
        "        apply sub_ne_zero.mp\n"
        "        simpa only [sub_sub_cancel_left] using inv_ne_zero hν\n"
        "      have heq :\n"
        "          operatorEigenspace T (z - ν⁻¹) =\n"
        "            eigenspace (ρ.inverse : Module.End 𝕜 H) ν := by\n"
        "        simpa only [sub_sub_cancel_left, inv_inv] using\n"
        "          operatorEigenspace_eq_resolventEigenspace ρ hzν\n",
        "    · have hdiff : z - (z - ν⁻¹) = ν⁻¹ := by ring\n"
        "      have hzν : z ≠ z - ν⁻¹ := by\n"
        "        apply sub_ne_zero.mp\n"
        "        rw [hdiff]\n"
        "        exact inv_ne_zero hν\n"
        "      have heq :\n"
        "          operatorEigenspace T (z - ν⁻¹) =\n"
        "            eigenspace (ρ.inverse : Module.End 𝕜 H) ν := by\n"
        "        simpa only [hdiff, inv_inv] using\n"
        "          operatorEigenspace_eq_resolventEigenspace ρ hzν\n",
    ),
    ExactRule(
        "expose_starRingEnd_on_resolvent_parameter",
        "  have hsymm := pmap_isFormalAdjoint_of_selfAdjoint hT\n"
        "  intro x y\n",
        "  have hsymm := pmap_isFormalAdjoint_of_selfAdjoint hT\n"
        "  change (starRingEnd 𝕜) z = z at hz\n"
        "  intro x y\n",
    ),
    ExactRule(
        "cancel_nonzero_self_inner_product",
        "  let xd : T.domain := ⟨x, hxDomain⟩\n"
        "  simpa [hxne, inner_smul_left, inner_smul_right, hxEq] using hsymm xd xd\n",
        "  let xd : T.domain := ⟨x, hxDomain⟩\n"
        "  have hinner : inner 𝕜 x x ≠ 0 := inner_self_ne_zero.mpr hxne\n"
        "  apply mul_right_cancel₀ hinner\n"
        "  simpa only [hxEq, inner_smul_left, inner_smul_right] using hsymm xd xd\n",
    ),
    ExactRule(
        "rebuild_consumed_pmap_eigenvector",
        "  obtain ⟨hxMem, hxne⟩ := hx\n"
        "  obtain ⟨hxDomain, hxEq⟩ := mem_operatorEigenspace_iff.mp hxMem\n"
        "  let xd : T.domain := ⟨x, hxDomain⟩\n"
        "  have hxorth : x ∈ (operatorEigenspace T 0)ᗮ :=\n"
        "    pmap_eigenvector_mem_ground_orthogonal hsymm hx (by exact_mod_cast hlambda)\n",
        "  obtain ⟨hxMem, hxne⟩ := hx\n"
        "  obtain ⟨hxDomain, hxEq⟩ := mem_operatorEigenspace_iff.mp hxMem\n"
        "  let xd : T.domain := ⟨x, hxDomain⟩\n"
        "  have hlambdaK : (lambda : 𝕜) ≠ 0 := by exact_mod_cast hlambda\n"
        "  have hxorth : x ∈ (operatorEigenspace T 0)ᗮ :=\n"
        "    pmap_eigenvector_mem_ground_orthogonal hsymm ⟨hxMem, hxne⟩ hlambdaK\n",
    ),
    ExactRule(
        "pin_operator_in_eigenvalue_real_wrapper",
        "  apply QYM.UnboundedCompactSpectralMappingExtension.pmap_eigenvalue_is_real\n"
        "  · exact\n"
        "      QYM.UnboundedCompactSpectralMappingExtension.pmap_isFormalAdjoint_of_selfAdjoint hT\n"
        "  · exact hlambda\n",
        "  exact QYM.UnboundedCompactSpectralMappingExtension.pmap_eigenvalue_is_real\n"
        "    (T := T)\n"
        "    (QYM.UnboundedCompactSpectralMappingExtension.\n"
        "      pmap_isFormalAdjoint_of_selfAdjoint hT)\n"
        "    hlambda\n",
    ),
    ExactRule(
        "use_LinearPMap_map_add",
        "  map_add' x y := by\n"
        "    apply Subtype.ext\n"
        "    ext <;> simp\n",
        "  map_add' x y := by\n"
        "    apply Subtype.ext\n"
        "    ext <;> simp only [Submodule.coe_add, LinearPMap.map_add]\n",
    ),
    ExactRule(
        "use_LinearPMap_map_smul",
        "  map_smul' a x := by\n"
        "    apply Subtype.ext\n"
        "    ext <;> simp\n",
        "  map_smul' a x := by\n"
        "    apply Subtype.ext\n"
        "    ext <;> simp only [Submodule.coe_smul, LinearPMap.map_smul]\n",
    ),
    ExactRule(
        "expose_energy_form_starRingEnd",
        "  intro u v\n"
        "  simpa only [energyForm_apply] using\n"
        "    (inner_conj_symm\n"
        "      (operatorCoordinate D u) (operatorCoordinate D v)).symm\n",
        "  intro u v\n"
        "  change inner 𝕜 (operatorCoordinate D u) (operatorCoordinate D v) =\n"
        "    (starRingEnd 𝕜)\n"
        "      (inner 𝕜 (operatorCoordinate D v) (operatorCoordinate D u))\n"
        "  exact (inner_conj_symm\n"
        "    (operatorCoordinate D u) (operatorCoordinate D v)).symm\n",
    ),
    ExactRule(
        "expose_graph_first_coordinate_membership",
        "  · rintro ⟨u, rfl⟩\n"
        "    simpa only [formEmbedding_apply] using\n"
        "      LinearPMap.mem_domain_of_mem_graph u.property\n",
        "  · rintro ⟨u, rfl⟩\n"
        "    change (u : H × K).1 ∈ D.domain\n"
        "    exact LinearPMap.mem_domain_of_mem_graph u.property\n",
    ),
    ExactRule(
        "type_hyperbolic_measure_infinity",
        "    truncatedHyperbolicMeasure Y Set.univ < ∞ := by\n",
        "    truncatedHyperbolicMeasure Y Set.univ < (∞ : ℝ≥0∞) := by\n",
    ),
    ExactRule(
        "fix_eta_smooth_core_record_binders",
        "  add_mem' f g hf hg := by\n"
        "    rcases hf with ⟨hfSmooth, hfCovariant, hfLp⟩\n",
        "  add_mem' := by\n"
        "    intro f g hf hg\n"
        "    rcases hf with ⟨hfSmooth, hfCovariant, hfLp⟩\n",
    ),
    ExactRule(
        "fix_eta_smooth_core_smul_binders",
        "  smul_mem' c f hf := by\n"
        "    rcases hf with ⟨hfSmooth, hfCovariant, hfLp⟩\n",
        "  smul_mem' := by\n"
        "    intro c f hf\n"
        "    rcases hf with ⟨hfSmooth, hfCovariant, hfLp⟩\n",
    ),
    ExactRule(
        "type_petersson_presentation_infinity",
        "      truncatedHyperbolicMeasure Y Set.univ < ∞ ∧\n",
        "      truncatedHyperbolicMeasure Y Set.univ < (∞ : ℝ≥0∞) ∧\n",
    ),
    ExactRule(
        "expose_invariant_scalar_pointwise_smul",
        "    · simpa only [Pi.smul_apply] using\n"
        "        (contMDiff_const.smul (I := 𝓘(ℂ)) hg.1)\n",
        "    · change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (fun tau : H => c * g tau)\n"
        "      exact contMDiff_const.mul hg.1\n",
    ),
    ExactRule(
        "expose_eta_covariant_pointwise_smul",
        "    · simpa only [Pi.smul_apply] using\n"
        "        (contMDiff_const.smul (I := 𝓘(ℂ)) hf.1)\n",
        "    · change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (fun tau : H => c * f tau)\n"
        "      exact contMDiff_const.mul hf.1\n",
    ),
    ExactRule(
        "direct_scalar_one_form_extensionality_calc",
        "  apply ContinuousLinearMap.ext\n"
        "  intro z\n"
        "  rw [scalarOneFormValue_apply_eq_mul_evalOne,\n"
        "    scalarOneFormValue_apply_eq_mul_evalOne, h]\n",
        "  apply ContinuousLinearMap.ext\n"
        "  intro z\n"
        "  calc\n"
        "    A z = z * A 1 := scalarOneFormValue_apply_eq_mul_evalOne A z\n"
        "    _ = z * B 1 := by rw [h]\n"
        "    _ = B z := (scalarOneFormValue_apply_eq_mul_evalOne B z).symm\n",
    ),
    ExactRule(
        "fix_eta_H1_core_record_binders",
        "  add_mem' g h hg hh := by\n"
        "    constructor\n"
        "    · rw [etaSection_add]\n"
        "      exact hg.1.add hh.1\n"
        "    · rw [etaGaugeOneFormCoefficient_add]\n"
        "      exact hg.2.add hh.2\n",
        "  add_mem' := by\n"
        "    intro g h hg hh\n"
        "    constructor\n"
        "    · rw [etaSection_add]\n"
        "      exact hg.1.add hh.1\n"
        "    · rw [etaGaugeOneFormCoefficient_add]\n"
        "      exact hg.2.add hh.2\n",
    ),
    ExactRule(
        "fix_eta_H1_core_smul_binders",
        "  smul_mem' c g hg := by\n"
        "    constructor\n"
        "    · rw [etaSection_smul]\n"
        "      exact hg.1.const_smul c\n"
        "    · rw [etaGaugeOneFormCoefficient_smul]\n"
        "      exact hg.2.const_smul c\n",
        "  smul_mem' := by\n"
        "    intro c g hg\n"
        "    constructor\n"
        "    · rw [etaSection_smul]\n"
        "      exact hg.1.const_smul c\n"
        "    · rw [etaGaugeOneFormCoefficient_smul]\n"
        "      exact hg.2.const_smul c\n",
    ),
    ExactRule(
        "type_quotient_measure_infinity",
        "    truncatedQuotientMeasure Y Set.univ < ∞ := by\n",
        "    truncatedQuotientMeasure Y Set.univ < (∞ : ℝ≥0∞) := by\n",
    ),
    ExactRule(
        "correct_ground_orthogonal_pairwise_orientation",
        "  exact hsymm.orthogonalFamily_eigenspaces.pairwise\n"
        "    hmuK.symm hy x hx.1\n",
        "  exact hsymm.orthogonalFamily_eigenspaces.pairwise\n"
        "    hmuK hx.1 y hy\n",
    ),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8")
    return {
        "bytes": len(data),
        "sha256": sha256(data),
        "git_blob": git_blob(data),
        "lf": data.count(b"\n"),
        "cr": b"\r" in data,
        "nul": b"\0" in data,
        "bom": data.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": data.endswith(b"\n"),
        "utf8": True,
    }


def trust_counts(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def _registry_transform(text: str, *, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    for label, namespace_marker, entries in REGISTRY_UNIVERSE_RULES:
        start = text.count(namespace_marker)
        if start != 1:
            raise RuntimeError(f"{label}: namespace marker count {start}, expected 1")
        begin = text.index(namespace_marker)
        end_marker = "\ntheorem evidenceSound (evidence : EvidenceId) : EvidenceStatement evidence := by"
        end = text.find(end_marker, begin)
        if end < 0:
            raise RuntimeError(f"{label}: evidenceSound boundary not found")
        region = text[begin:end]
        applied: list[dict[str, object]] = []
        for short_name, arity in entries:
            plain = "QYM.FullCertification.PaperNormalized." + short_name
            sealed = plain + _zeros(arity)
            old, new = (sealed, plain) if inverse else (plain, sealed)
            # Registry branches put the constant alone at end of line.  This
            # prevents the plain token from matching inside an annotated token.
            old_line = old + "\n"
            new_line = new + "\n"
            count = region.count(old_line)
            if count != 1:
                raise RuntimeError(
                    f"{label}/{short_name}: exact region occurrence count {count}, expected 1"
                )
            region = region.replace(old_line, new_line, 1)
            applied.append({"statement": short_name, "universe_arity": arity, "occurrences": 1})
        text = text[:begin] + region + text[end:]
        audits.append({"label": label, "entries": applied, "occurrences": len(applied)})
    return text, audits


def transform(text: str, *, inverse: bool) -> tuple[str, dict[str, object]]:
    ordered = tuple(reversed(RULES)) if inverse else RULES
    applied: list[dict[str, object]] = []
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.expected:
            raise RuntimeError(
                f"{rule.label}: exact occurrence count {count}, expected {rule.expected}"
            )
        text = text.replace(old, new)
        applied.append({"label": rule.label, "occurrences": count})

    # Registry annotations are independent of ordinary repairs.  Applying them
    # last in both directions is safe because none of the exact rules touch the
    # four registry regions.
    text, registry_audit = _registry_transform(text, inverse=inverse)
    return text, {
        "exact_rules": applied,
        "registry_rules": registry_audit,
        "exact_rule_occurrences": sum(item["occurrences"] for item in applied),
        "registry_occurrences": sum(item["occurrences"] for item in registry_audit),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    args = parser.parse_args()

    source = args.input.read_bytes()
    source_hash = sha256(source)
    inverse = args.mode == "inverse"
    expected_source_hash = EXPECTED_OUTPUT_SHA256 if inverse else EXPECTED_INPUT_SHA256
    if expected_source_hash is not None and source_hash != expected_source_hash:
        raise RuntimeError(
            f"input SHA256 {source_hash}, expected {expected_source_hash} for {args.mode}"
        )

    source_text = source.decode("utf-8")
    before_trust = trust_counts(source_text)
    result_text, rule_audit = transform(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    after_trust = trust_counts(result_text)
    if after_trust != before_trust:
        raise RuntimeError(f"trust counts changed: {before_trust} -> {after_trust}")

    expected_result_hash = EXPECTED_INPUT_SHA256 if inverse else EXPECTED_OUTPUT_SHA256
    result_hash = sha256(result)
    if expected_result_hash is not None and result_hash != expected_result_hash:
        raise RuntimeError(
            f"output SHA256 {result_hash}, expected {expected_result_hash} for {args.mode}"
        )

    # Prove the active transform is exactly reversible in memory.
    restored_text, _ = transform(result_text, inverse=not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore the exact input bytes")

    args.output.write_bytes(result)
    audit = {
        "schema": "qym-probe4-mid-static-transform-v1",
        "status": "STATIC_COMPOSITION_PASS_NOT_LEAN_EXECUTED",
        "mode": args.mode,
        "authority": {
            "probe3_candidate_sha256": EXPECTED_INPUT_SHA256,
            "probe3_log_sha256": EXPECTED_LOG_SHA256,
            "probe3_error_headers": 777,
            "scope_lines": [20297, 40000],
        },
        "source": shape(source),
        "result": shape(result),
        "rules": rule_audit,
        "inverse_byte_equal": True,
        "trust_counts": after_trust,
        "cascade_policy": {
            "downstream_symptoms_activated": False,
            "excluded_clusters": [
                "realPartForm_232xx",
                "normalize_unitEigenvector_25093_25255",
                "late_namespace_and_failed_declaration_cascades_26363_27426",
                "etaSmoothAutomorphicCore_projection_and_function_cascades",
                "etaH1Core_projection_and_function_cascades",
                "stored_trace_36515_37112",
            ],
        },
        "lean_executed": False,
        "lake_executed": False,
        "remote_accessed": False,
    }
    args.audit.write_text(json.dumps(audit, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(audit, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
