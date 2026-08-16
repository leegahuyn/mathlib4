#!/usr/bin/env python3
"""Conditional static Probe9 projection for exact Probe8 QYM lines 55000--61671.

The transform is byte-locked to the terminal Probe8 candidate and diagnostic
artifacts.  It activates no promotion: the generated tranche remains
conditional until a terminal Probe9 execution validates the projection.
Only direct producer roots are changed.  No Lean, Lake, Git, network, remote,
or canonical-source operation is invoked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import runpy
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe9-55k-static-transform-v2-exact-probe8"
INPUT_SHA256 = "63baae8766e3208ac1d8dfa66946ac5ae3cf4a4264d21218a1ccb17aed3c4fd8"
INPUT_GIT_BLOB = "a2d3f4f60018fc2bfebd904db17aa13025c39ed6"
INPUT_BYTES = 2_916_737
INPUT_LF = 61_671
LOG_SHA256 = "4408bf46825d32a935de970904c711510b774ef93026fbee3e20dbc18392beea"
ERROR_HEADERS_SHA256 = "9f0d91787942db9470e307c5a44d8523b2b362ad31f737da0eb48b3f9f2d181f"
HEADER_LINE_SHIFT = 78

# Filled from a deterministic --bootstrap-seal projection, then enforced.
OUTPUT_SHA256 = "5fb8300a3fdca11da31577c5c6a176c7d4fa5fcc13fd4b8dca951f521be3f66f"
OUTPUT_GIT_BLOB = "c65404f34b9219963c314126e9d85aaa5ba4e25c"
OUTPUT_BYTES = 2_920_718
OUTPUT_LF = 61_727

FOREIGN_HELPER_SHA256 = {
    "qym_probe7_reanchored.py":
        "1919650925df78ea6b87a742937ba4c57cd1e3eeb123d5a2111131189a4fa53a",
    "qym_probe8_early_independent.py":
        "67843a8608038295f570bb15feb8f08cbb6d90f9c166d078fecde9e1ba215cf4",
    "qym_probe8_mid_static.py":
        "b529f1df682a1e9b1588399f3a951914452d1d9afb049dd7be22cef1d8570dbf",
    "qym_probe8_late_static.py":
        "4b3470fa2296d61002460e6f8532402f0509ae8c3385f36b512a732ad55c8f9f",
    "qym_probe9_50k_static.py":
        "44b17336ea2cfa089c461e8c23cf25d2de95987e106e8473f2765cb2bf5faab4",
}


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str

    def __post_init__(self) -> None:
        # All surviving direct headers moved uniformly by the exact Probe8
        # composition.  Normalize the Probe7-authored table at construction.
        object.__setattr__(self, "line", self.line + HEADER_LINE_SHIFT)


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
        "discriminant_resolvent_bundle_before_function_coercion",
        "      (resolvent\n"
        "        ((QYM.FullCertification.P6ActualStageDiscriminantPotentialExtension.actualStageDiscriminantPotentialOperator Y).restrictScalars ℝ)\n"
        "        r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        "      ((resolvent\n"
        "        ((QYM.FullCertification.P6ActualStageDiscriminantPotentialExtension.actualStageDiscriminantPotentialOperator Y).restrictScalars ℝ)\n"
        "        r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →L[ℝ]\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) :\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        (Header(55011, 7, "failed to synthesize instance of type class"),),
        rationale="Resolve the algebra-valued resolvent before coercing it to a function.",
    ),
    Rule(
        "stage_certificate_resolvent_bundle_before_function_coercion",
        "          ¬ IsCompactOperator\n"
        "            (resolvent T r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "              QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        "          ¬ IsCompactOperator\n"
        "            ((resolvent T r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →L[ℝ]\n"
        "                QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) :\n"
        "              QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "                QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        (Header(55035, 13, "failed to synthesize instance of type class"),),
        rationale="Pin the ContinuousLinearMap resolvent before its function coercion.",
    ),
    Rule(
        "test_operator_inner_self_use_complex_normsq",
        "  rw [actualInverseEtaAnalysisFunctional_apply]\n"
        "  exact star_mul' (actualInverseEtaAnalysisFunctional Y u)\n",
        "  rw [actualInverseEtaAnalysisFunctional_apply, Complex.star_def,\n"
        "    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]\n",
        (Header(55212, 2, "Type mismatch"),),
        rationale="The current star_mul' theorem rewrites star of a product; use the Complex conjugate norm-square identity.",
    ),
    Rule(
        "test_operator_range_expose_bundled_application",
        "    refine ⟨(c / inner ℂ (actualInverseEtaTestVector Y)\n"
        "      (actualInverseEtaTestVector Y)) • actualInverseEtaTestVector Y, ?_⟩\n"
        "    rw [actualInverseEtaTestOperator_apply,\n",
        "    refine ⟨(c / inner ℂ (actualInverseEtaTestVector Y)\n"
        "      (actualInverseEtaTestVector Y)) • actualInverseEtaTestVector Y, ?_⟩\n"
        "    change actualInverseEtaTestOperator Y\n"
        "      ((c / inner ℂ (actualInverseEtaTestVector Y)\n"
        "        (actualInverseEtaTestVector Y)) • actualInverseEtaTestVector Y) =\n"
        "        c • actualInverseEtaTestVector Y\n"
        "    rw [actualInverseEtaTestOperator_apply,\n",
        (Header(55327, 8, "Tactic `rewrite` failed"),),
        rationale="Expose the bundled rank-one application hidden by the range coercion.",
    ),
    Rule(
        "normalized_projection_range_expose_bundled_application",
        "  · rintro u ⟨v, rfl⟩\n"
        "    rw [actualNormalizedInverseEtaProjection_apply]\n",
        "  · rintro u ⟨v, rfl⟩\n"
        "    change actualNormalizedInverseEtaProjection hY v ∈\n"
        "      ℂ ∙ actualNormalizedInverseEtaTestVector hY\n"
        "    rw [actualNormalizedInverseEtaProjection_apply]\n",
        (Header(55495, 8, "Tactic `rewrite` failed"),),
        rationale="Expose the ContinuousLinearMap application before rewriting the range witness.",
    ),
    Rule(
        "normalized_projection_ker_expose_bundled_application",
        "  ext u\n"
        "  rw [LinearMap.mem_ker,\n"
        "    actualNormalizedInverseEtaProjection_apply,\n",
        "  ext u\n"
        "  change actualNormalizedInverseEtaProjection hY u = 0 ↔\n"
        "    u ∈ (ℂ ∙ actualNormalizedInverseEtaTestVector hY)ᗮ\n"
        "  rw [actualNormalizedInverseEtaProjection_apply,\n",
        (Header(55520, 4, "Tactic `rewrite` failed"),),
        rationale="State the kernel equality at the bundled map level.",
    ),
    Rule(
        "normalized_projection_iscompl_fully_qualified",
        "  have hCompl :=\n"
        "    (ContinuousLinearMap.IsIdempotentElem.toLinearMap\n"
        "      (actualNormalizedInverseEtaProjection_isIdempotent hY)).isCompl\n",
        "  have hCompl :=\n"
        "    LinearMap.IsIdempotentElem.isCompl\n"
        "      (ContinuousLinearMap.IsIdempotentElem.toLinearMap\n"
        "        (actualNormalizedInverseEtaProjection_isIdempotent hY))\n",
        (Header(55542, 62, "Invalid field `isCompl`"),),
        rationale="Qualify both the CLM-to-linear-map transport and the linear idempotent complement theorem.",
    ),
    Rule(
        "projection_hamiltonian_symmetry_expose_bundled_applications",
        "    (actualInverseEtaProjectionHamiltonian hY).IsSymmetric := by\n"
        "  intro u v\n"
        "  rw [actualInverseEtaProjectionHamiltonian_apply,\n",
        "    (actualInverseEtaProjectionHamiltonian hY).IsSymmetric := by\n"
        "  intro u v\n"
        "  change inner ℂ (actualInverseEtaProjectionHamiltonian hY u) v =\n"
        "    inner ℂ u (actualInverseEtaProjectionHamiltonian hY v)\n"
        "  rw [actualInverseEtaProjectionHamiltonian_apply,\n",
        (Header(56183, 6, "Tactic `rewrite` failed"),),
        rationale="Expose both CLM applications before expanding the complementary projection.",
    ),
    Rule(
        "projection_hamiltonian_inner_self_change_hmove",
        "  have hMove := hSymm u (actualInverseEtaProjectionHamiltonian hY u)\n"
        "  rw [actualInverseEtaProjectionHamiltonian_apply_apply] at hMove\n",
        "  have hMove := hSymm u (actualInverseEtaProjectionHamiltonian hY u)\n"
        "  change inner ℂ (actualInverseEtaProjectionHamiltonian hY u)\n"
        "      (actualInverseEtaProjectionHamiltonian hY u) =\n"
        "    inner ℂ u (actualInverseEtaProjectionHamiltonian hY\n"
        "      (actualInverseEtaProjectionHamiltonian hY u)) at hMove\n"
        "  rw [actualInverseEtaProjectionHamiltonian_apply_apply] at hMove\n",
        (Header(56229, 6, "Tactic `rewrite` failed"),),
        rationale="Expose the coerced outer application in the local symmetric equality.",
    ),
    Rule(
        "projection_hamiltonian_offtest_normalize_ofreal_power",
        "  rw [actualInverseEtaProjectionHamiltonian_eq_self_of_mem_offTest hY hu,\n"
        "    inner_self_eq_norm_sq_to_K]\n",
        "  rw [actualInverseEtaProjectionHamiltonian_eq_self_of_mem_offTest hY hu,\n"
        "    inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]\n",
        (Header(56262, 29, "unsolved goals"),),
        rationale="Normalize the remaining real-to-complex coercion across the square.",
    ),
    Rule(
        "projection_resolvent_bundle_before_function_coercion",
        "      (resolvent\n"
        "        ((actualInverseEtaProjectionHamiltonian hY).restrictScalars ℝ) r :\n"
        "          QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "            QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) := by\n",
        "      ((resolvent\n"
        "        ((actualInverseEtaProjectionHamiltonian hY).restrictScalars ℝ) r :\n"
        "          QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →L[ℝ]\n"
        "            QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) :\n"
        "          QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "            QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) := by\n",
        (Header(56446, 7, "failed to synthesize instance of type class"),),
        rationale="Resolve the projection resolvent in the endomorphism algebra first.",
    ),
    Rule(
        "projection_uniform_resolvent_bundle_before_function_coercion",
        "          (resolvent\n"
        "            ((actualInverseEtaProjectionHamiltonian hY).restrictScalars ℝ) r :\n"
        "              QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "                QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) := by\n",
        "          ((resolvent\n"
        "            ((actualInverseEtaProjectionHamiltonian hY).restrictScalars ℝ) r :\n"
        "              QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →L[ℝ]\n"
        "                QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) :\n"
        "              QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "                QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) := by\n",
        (Header(56460, 11, "failed to synthesize instance of type class"),),
        rationale="Pin the algebra-valued uniform resolvent before coercion.",
    ),
    Rule(
        "arbitrary_operator_resolvent_bundle_before_function_coercion",
        "    (hCompact : IsCompactOperator\n"
        "      (resolvent (T.restrictScalars ℝ) r :\n"
        "        QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "          QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y)) :\n",
        "    (hCompact : IsCompactOperator\n"
        "      ((resolvent (T.restrictScalars ℝ) r :\n"
        "          QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →L[ℝ]\n"
        "            QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) :\n"
        "        QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "          QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y)) :\n",
        (Header(56476, 7, "failed to synthesize instance of type class"),),
        rationale="Pin the arbitrary operator resolvent as a real CLM before compactness coercion.",
    ),
    Rule(
        "projection_certificate_resolvent_bundle_before_function_coercion",
        "          ¬ IsCompactOperator\n"
        "            (resolvent\n"
        "              ((actualInverseEtaProjectionHamiltonian hY).restrictScalars ℝ) r :\n"
        "                QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "                  QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) := by\n",
        "          ¬ IsCompactOperator\n"
        "            ((resolvent\n"
        "              ((actualInverseEtaProjectionHamiltonian hY).restrictScalars ℝ) r :\n"
        "                QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →L[ℝ]\n"
        "                  QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) :\n"
        "                QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y →\n"
        "                  QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.ActualInverseEtaTestSpace Y) := by\n",
        (Header(56512, 13, "failed to synthesize instance of type class"),),
        rationale="Pin the aggregate certificate resolvent in the CLM algebra.",
    ),
    Rule(
        "natural_stage_cutoff_monotone_remove_reversing_simp",
        "  unfold naturalStageCutoff\n"
        "  simpa [add_comm] using add_le_add_right (Nat.cast_le.mpr hmn) 2\n",
        "  unfold naturalStageCutoff\n"
        "  exact add_le_add_right (Nat.cast_le.mpr hmn) 2\n",
        (Header(56674, 2, "Type mismatch: After simplification"),),
        rationale="The direct right-add inequality already has the target orientation.",
    ),
    Rule(
        "global_projection_add_reorder_ae_rewrites",
        "    with x hsum hu hv huv hout\n"
        "  rw [hsum, hu, hv, huv, hout]\n",
        "    with x hsum hu hv huv hout\n"
        "  rw [hsum, hout, hu, hv, huv]\n",
        (Header(56807, 12, "Tactic `rewrite` failed"),),
        rationale="Expose the coeFn of the output sum before rewriting its two projected summands.",
    ),
    Rule(
        "global_projection_smul_reorder_ae_rewrites",
        "    with x hleft hu hcu hright\n"
        "  rw [hleft, hu, hcu, hright]\n",
        "    with x hleft hu hcu hright\n"
        "  rw [hleft, hright, hu, hcu]\n",
        (Header(56826, 13, "Tactic `rewrite` failed"),),
        rationale="Expose the coeFn of the output scalar multiple before its projected factor.",
    ),
    Rule(
        "global_projection_clm_constructor_expose_linear_map_apply",
        "  (globalStageProjectionLinearMap n).mkContinuous 1 (fun u => by\n"
        "    simpa only [one_mul] using globalStageProjection_norm_le n u)\n",
        "  (globalStageProjectionLinearMap n).mkContinuous 1 (fun u => by\n"
        "    simpa only [one_mul, globalStageProjectionLinearMap_apply] using\n"
        "      globalStageProjection_norm_le n u)\n",
        (Header(56853, 4, "Type mismatch: After simplification"),),
        rationale="Expose the underlying linear-map application in the mkContinuous bound.",
    ),
    Rule(
        "global_projection_clm_norm_expose_linear_map_apply",
        "  exact LinearMap.mkContinuous_norm_le _ zero_le_one (fun u => by\n"
        "    simpa only [one_mul] using globalStageProjection_norm_le n u)\n",
        "  exact LinearMap.mkContinuous_norm_le _ zero_le_one (fun u => by\n"
        "    simpa only [one_mul, globalStageProjectionLinearMap_apply] using\n"
        "      globalStageProjection_norm_le n u)\n",
        (Header(56865, 4, "Type mismatch: After simplification"),),
        rationale="Expose the underlying linear-map application in the operator-norm bound.",
    ),
    Rule(
        "global_projection_idempotent_rewrite_inner_only_off_stage",
        "    with x houter hinner\n"
        "  rw [houter, hinner]\n"
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp only [globalStageProjectionRepresentative, hx,\n"
        "      Set.indicator_of_mem]\n"
        "  · simp only [globalStageProjectionRepresentative, hx,\n"
        "      Set.indicator_of_notMem]\n",
        "    with x houter hinner\n"
        "  rw [houter]\n"
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hx]\n"
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hx, hinner,\n"
        "      globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hx]\n",
        (
            Header(56881, 2, "unsolved goals"),
            Header(56883, 2, "unsolved goals"),
        ),
        rationale="The inner representative equality is needed only in the off-stage branch.",
    ),
    Rule(
        "global_projection_clm_comp_remove_third_stale_apply",
        "  rw [ContinuousLinearMap.comp_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjection_idempotent]\n",
        "  rw [ContinuousLinearMap.comp_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjection_idempotent]\n",
        (Header(56895, 4, "Tactic `rewrite` failed"),),
        rationale="Two CLM apply rewrites already expose both levels of the raw idempotence theorem.",
    ),
    Rule(
        "global_projection_symmetry_offstage_use_explicit_indicator",
        "  · simp only [globalStageProjectionRepresentative, hx,\n"
        "      Set.indicator_of_notMem, inner_zero_left, inner_zero_right]\n",
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,\n"
        "      inner_zero_left, inner_zero_right]\n",
        (Header(56915, 2, "unsolved goals"),),
        rationale="Use the negative membership proof directly for both indicator factors.",
    ),
    Rule(
        "closed_graph_single_valued_use_calc",
        "  apply Prod.ext\n"
        "  · exact hBase\n"
        "  · rw [← hT u, ← hT v, hBase]\n",
        "  apply Prod.ext\n"
        "  · exact hBase\n"
        "  · change etaClosedGraphDerivativeCoordinate Y u =\n"
        "      etaClosedGraphDerivativeCoordinate Y v\n"
        "    calc\n"
        "      etaClosedGraphDerivativeCoordinate Y u =\n"
        "          T (etaClosedGraphBaseCoordinate Y u) := (hT u).symm\n"
        "      _ = T (etaClosedGraphBaseCoordinate Y v) := congrArg T hBase\n"
        "      _ = etaClosedGraphDerivativeCoordinate Y v := hT v\n",
        (Header(58058, 8, "Tactic `rewrite` failed"),),
        rationale="Prove derivative-coordinate equality through T after beta-reducing the product projection.",
    ),
    Rule(
        "ground_projection_range_expose_bundled_application",
        "  · rintro u ⟨v, rfl⟩\n"
        "    rw [groundProjection_apply]\n",
        "  · rintro u ⟨v, rfl⟩\n"
        "    change groundProjection v ∈ GroundBlock\n"
        "    rw [groundProjection_apply]\n",
        (Header(58220, 8, "Tactic `rewrite` failed"),),
        rationale="Expose the ground projection application hidden by LinearMap.range coercion.",
    ),
    Rule(
        "ground_projection_range_reverse_expose_bundled_application",
        "    refine ⟨c • groundVector, ?_⟩\n"
        "    rw [groundProjection_apply, inner_smul_right,\n",
        "    refine ⟨c • groundVector, ?_⟩\n"
        "    change groundProjection (c • groundVector) = c • groundVector\n"
        "    rw [groundProjection_apply, inner_smul_right,\n",
        (Header(58226, 8, "Tactic `rewrite` failed"),),
        rationale="Expose the bundled projection application in the reverse range inclusion.",
    ),
    Rule(
        "ground_projection_ker_expose_bundled_application",
        "  ext u\n"
        "  rw [LinearMap.mem_ker, groundProjection_apply,\n",
        "  ext u\n"
        "  change groundProjection u = 0 ↔ u ∈ OffGroundBlock\n"
        "  rw [groundProjection_apply,\n",
        (Header(58233, 25, "Tactic `rewrite` failed"),),
        rationale="State the kernel equality at the ContinuousLinearMap application level.",
    ),
    Rule(
        "ground_projection_iscompl_fully_qualified",
        "  have h :=\n"
        "    (ContinuousLinearMap.IsIdempotentElem.toLinearMap\n"
        "      groundProjection_isIdempotent).isCompl\n",
        "  have h :=\n"
        "    LinearMap.IsIdempotentElem.isCompl\n"
        "      (ContinuousLinearMap.IsIdempotentElem.toLinearMap\n"
        "        groundProjection_isIdempotent)\n",
        (Header(58242, 37, "Invalid field `isCompl`"),),
        rationale="Qualify the linear-map complement theorem instead of projecting it from Eq.",
    ),
    Rule(
        "covariant_derivative_symmetry_expose_bundled_applications",
        "    covariantDerivative.IsSymmetric := by\n"
        "  intro u v\n"
        "  rw [covariantDerivative_apply, covariantDerivative_apply,\n",
        "    covariantDerivative.IsSymmetric := by\n"
        "  intro u v\n"
        "  change inner ℂ (covariantDerivative u) v =\n"
        "    inner ℂ u (covariantDerivative v)\n"
        "  rw [covariantDerivative_apply, covariantDerivative_apply,\n",
        (Header(58266, 6, "Tactic `rewrite` failed"),),
        rationale="Expose both coerced covariant-derivative applications before expansion.",
    ),
    Rule(
        "potential_symmetry_expose_bundled_applications",
        "theorem potential_isSymmetric : potential.IsSymmetric := by\n"
        "  intro u v\n"
        "  simp only [potential_apply, inner_smul_left, inner_smul_right,\n"
        "    RCLike.conj_ofReal]\n"
        "  rw [groundProjection_isSymmetric u v]\n",
        "theorem potential_isSymmetric : potential.IsSymmetric := by\n"
        "  intro u v\n"
        "  change inner ℂ ((((1 : ℝ) / 4 : ℝ) : ℂ) • groundProjection u) v =\n"
        "    inner ℂ u ((((1 : ℝ) / 4 : ℝ) : ℂ) • groundProjection v)\n"
        "  rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "    RCLike.star_def, RCLike.conj_ofReal,\n"
        "    groundProjection_isSymmetric u v]\n",
        (Header(58360, 2, "`simp` made no progress"),),
        rationale="Expose the potential applications before normalizing the real scalar and symmetric projection.",
    ),
    Rule(
        "coordinate_hamiltonian_symmetry_expose_bundled_applications",
        "    coordinateHamiltonian.IsSymmetric := by\n"
        "  intro u v\n"
        "  rw [coordinateHamiltonian_apply, coordinateHamiltonian_apply,\n",
        "    coordinateHamiltonian.IsSymmetric := by\n"
        "  intro u v\n"
        "  change inner ℂ (coordinateHamiltonian u) v =\n"
        "    inner ℂ u (coordinateHamiltonian v)\n"
        "  rw [coordinateHamiltonian_apply, coordinateHamiltonian_apply,\n",
        (Header(58382, 6, "Tactic `rewrite` failed"),),
        rationale="Expose both coerced Hamiltonian applications before distributing the inner product.",
    ),
    Rule(
        "ground_projection_zero_change_to_kernel_membership",
        "    groundProjection u = 0 := by\n"
        "  rw [← LinearMap.mem_ker, groundProjection_ker]\n"
        "  exact hu\n",
        "    groundProjection u = 0 := by\n"
        "  change u ∈ groundProjection.toLinearMap.ker\n"
        "  rw [groundProjection_ker]\n"
        "  exact hu\n",
        (Header(58401, 6, "Tactic `rewrite` failed"),),
        rationale="Change the equality directly to membership in the exact bundled map kernel.",
    ),
    Rule(
        "coordinate_form_hermitian_expose_starring_end",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    coordinateHamiltonianForm_apply, RCLike.star_def, map_add, map_mul,\n"
        "    RCLike.conj_ofReal]\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    coordinateHamiltonianForm_apply, RCLike.star_def, map_add, map_mul,\n"
        "    starRingEnd_apply, RCLike.star_def, RCLike.conj_ofReal]\n",
        (Header(58510, 4, "Tactic `rewrite` failed"),),
        rationale="Expose starRingEnd applications produced by map_add/map_mul before conj_ofReal.",
    ),
    Rule(
        "coordinate_form_hamiltonian_expose_starring_end",
        "  rw [coordinateHamiltonianForm_apply, coordinateHamiltonian_apply,\n"
        "    inner_add_left, potential_apply, inner_smul_left,\n"
        "    RCLike.star_def, RCLike.conj_ofReal]\n",
        "  rw [coordinateHamiltonianForm_apply, coordinateHamiltonian_apply,\n"
        "    inner_add_left, potential_apply, inner_smul_left,\n"
        "    starRingEnd_apply, RCLike.star_def, RCLike.conj_ofReal]\n",
        (Header(58524, 4, "Tactic `rewrite` failed"),),
        rationale="Convert the scalar starRingEnd application to star before conj_ofReal.",
    ),
    Rule(
        "coordinate_form_re_self_reduce_ofreal_parts",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n"
        "  simp only [Complex.ofReal_re]\n",
        (Header(58542, 78, "unsolved goals"),),
        rationale="Reduce the two remaining real parts of embedded real norm squares explicitly.",
    ),
    Rule(
        "bounded_resolvent_bundle_before_function_coercion_two_sites",
        "    ¬ IsCompactOperator\n"
        "      (resolvent T r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        "    ¬ IsCompactOperator\n"
        "      ((resolvent T r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →L[ℝ]\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) :\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        (
            Header(54982, 7, "failed to synthesize instance of type class"),
            Header(58689, 7, "failed to synthesize instance of type class"),
        ),
        occurrences=2,
        rationale="Pin both identical bounded-resolvent statements in the CLM algebra.",
    ),
    Rule(
        "coordinate_firewall_uniform_resolvent_bundle_before_function_coercion",
        "        ¬ IsCompactOperator\n"
        "          (resolvent T r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "            QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        "        ¬ IsCompactOperator\n"
        "          ((resolvent T r : QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →L[ℝ]\n"
        "              QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) :\n"
        "            QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "              QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        (Header(58703, 11, "failed to synthesize instance of type class"),),
        rationale="Pin the uniformly quantified coordinate-firewall resolvent.",
    ),
    Rule(
        "paper_rs_domination_use_add_le_add",
        "    _ ≤ alpha * massEnergy u + beta * ‖u‖ ^ 2 :=\n"
        "      add_le_add_right\n"
        "        (mul_le_mul_of_nonneg_left (hMass u hu) hAlpha) _\n",
        "    _ ≤ alpha * massEnergy u + beta * ‖u‖ ^ 2 :=\n"
        "      add_le_add\n"
        "        (mul_le_mul_of_nonneg_left (hMass u hu) hAlpha) (le_refl _)\n",
        (Header(58840, 6, "Type mismatch"),),
        rationale="Prove both summands with add_le_add instead of the changed add_le_add_right orientation.",
    ),
    Rule(
        "energy_limit_use_ge_of_tendsto",
        "  exact le_of_tendsto (hEnergyLimit u hu)\n"
        "    (Eventually.of_forall fun n => hStage n u hu)\n",
        "  exact ge_of_tendsto (hEnergyLimit u hu)\n"
        "    (Eventually.of_forall fun n => hStage n u hu)\n",
        (Header(58907, 35, "Type mismatch"),),
        rationale="The hypotheses are eventual lower bounds, so use the limit-from-below theorem.",
    ),
    Rule(
        "cutoff_energy_fix_complex_inner_scalar",
        "    (inner ℂ (actualCutoffEscapeHamiltonian n u) u).re = ‖u‖ ^ 2 := by\n"
        "  rw [hu, real_inner_self_eq_norm_sq]\n",
        "    (inner ℂ (actualCutoffEscapeHamiltonian n u) u).re = ‖u‖ ^ 2 := by\n"
        "  rw [hu]\n"
        "  exact (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm\n",
        (Header(59207, 10, "Tactic `rewrite` failed"),),
        rationale="Use the Complex real-part inner-product identity, not the real-inner theorem.",
    ),
    Rule(
        "cutoff_strong_tendsto_pin_constant_sequence",
        "  have hProjection :=\n"
        "    QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_tendsto_strong u\n"
        "  simpa only [actualCutoffEscapeHamiltonian_apply, sub_self] using\n"
        "    tendsto_const_nhds.sub hProjection\n",
        "  have hProjection :=\n"
        "    QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_tendsto_strong u\n"
        "  have hConst : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) :=\n"
        "    tendsto_const_nhds\n"
        "  simpa only [actualCutoffEscapeHamiltonian_apply, sub_self] using\n"
        "    hConst.sub hProjection\n",
        (Header(59254, 2, "Type mismatch: After simplification"),),
        rationale="Pin the constant sequence value and index type before subtracting the projection limit.",
    ),
    Rule(
        "negative_one_shift_remove_stale_id_apply",
        "    actualCutoffNegativeOneResolvent_apply,\n"
        "    actualCutoffEscapeHamiltonian_apply, map_smul, map_add,\n"
        "    ContinuousLinearMap.id_apply,\n",
        "    actualCutoffNegativeOneResolvent_apply,\n"
        "    actualCutoffEscapeHamiltonian_apply, map_smul, map_add,\n",
        (Header(59295, 4, "Tactic `rewrite` failed"),),
        rationale="The preceding definitions have already beta-reduced the identity CLM application.",
    ),
    Rule(
        "resolvent_strong_tendsto_reduce_function_comp",
        "  simpa only [actualCutoffNegativeOneResolvent_apply,\n"
        "    actualCutoffLimitNegativeOneResolvent_apply,\n"
        "    hScaleLimit] using hScaled\n",
        "  simpa only [Function.comp_apply, actualCutoffNegativeOneResolvent_apply,\n"
        "    actualCutoffLimitNegativeOneResolvent_apply,\n"
        "    hScaleLimit] using hScaled\n",
        (Header(59406, 2, "Type mismatch: After simplification"),),
        rationale="Reduce the composition introduced by Continuous.tendsto before matching the lambda target.",
    ),
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


def verify_authority(log: bytes, error_headers: bytes) -> list[dict[str, object]]:
    if sha256(log) != LOG_SHA256:
        raise RuntimeError(f"Probe8 log sha256 {sha256(log)} != {LOG_SHA256}")
    if sha256(error_headers) != ERROR_HEADERS_SHA256:
        raise RuntimeError(
            f"Probe8 error-header sha256 {sha256(error_headers)} != "
            f"{ERROR_HEADERS_SHA256}"
        )
    log_text = log.decode("utf-8")
    log_error_lines = [
        line for line in log_text.splitlines()
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if log_error_lines != error_headers.decode("utf-8").splitlines():
        raise RuntimeError("Probe8 error-header artifact differs from the log")
    if len(log_error_lines) != 344:
        raise RuntimeError(f"Probe8 error count {len(log_error_lines)} != 344")
    warning_count = len(
        re.findall(
            r"(?m)^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"warning(?:\([^)]*\))?: ",
            log_text,
        )
    )
    if warning_count != 374:
        raise RuntimeError(f"Probe8 warning count {warning_count} != 374")

    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = re.compile(
                rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
            )
            count = len(pattern.findall(log_text))
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
                "headers": [
                    {"line": h.line, "column": h.column, "message": h.message}
                    for h in rule.headers
                ],
                "rationale": rule.rationale,
            }
        )
    return text, audit


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        index = text.find(needle, start)
        if index < 0:
            return found
        found.append((index, index + len(needle)))
        start = index + 1


def collision_audit(base_text: str, helper_paths: list[Path]) -> dict[str, object]:
    if {path.name for path in helper_paths} != set(FOREIGN_HELPER_SHA256):
        raise RuntimeError(
            "foreign helper set is not exactly Probe7, Probe8 early/mid/late, and Probe9 50k"
        )

    own_spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        matches = spans(base_text, rule.old)
        if len(matches) != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: collision audit count {len(matches)} != {rule.occurrences}"
            )
        own_spans.extend((start, end, rule.label) for start, end in matches)

    foreign_spans: list[tuple[int, int, str, str]] = []
    identities: dict[str, str] = {}
    exact_anchor_equalities = 0
    consumed_foreign_rules: list[str] = []
    own_anchors = {anchor for rule in RULES for anchor in (rule.old, rule.new)}
    for path in helper_paths:
        data = path.read_bytes()
        digest = sha256(data)
        expected_digest = FOREIGN_HELPER_SHA256[path.name]
        if digest != expected_digest:
            raise RuntimeError(f"foreign helper {path.name} sha256 {digest} != {expected_digest}")
        identities[path.name] = digest
        module = runpy.run_path(str(path))
        foreign_rules = module.get("RULES") or module.get("REPAIRS")
        if not isinstance(foreign_rules, tuple):
            raise RuntimeError(f"foreign helper {path.name} has no tuple rule table")
        active_new = path.name in {
            "qym_probe7_reanchored.py",
            "qym_probe8_early_independent.py",
            "qym_probe8_mid_static.py",
            "qym_probe8_late_static.py",
        }
        for foreign_rule in foreign_rules:
            old = getattr(foreign_rule, "old")
            new = getattr(foreign_rule, "new")
            exact_anchor_equalities += int(old in own_anchors) + int(new in own_anchors)
            active_anchor = new if active_new else old
            expected_count = int(getattr(foreign_rule, "occurrences", 1))
            matches = spans(base_text, active_anchor)
            if len(matches) != expected_count:
                alternate = old if active_new else new
                alternate_matches = spans(base_text, alternate)
                if not matches and len(alternate_matches) == expected_count:
                    matches = alternate_matches
                elif not matches and not alternate_matches:
                    consumed_foreign_rules.append(
                        f"{path.name}:{getattr(foreign_rule, 'label')}"
                    )
                    continue
                else:
                    raise RuntimeError(
                        f"foreign {path.name}:{getattr(foreign_rule, 'label')} "
                        f"active/alternate counts {len(matches)}/{len(alternate_matches)} "
                        f"!= {expected_count}"
                    )
            foreign_spans.extend(
                (start, end, path.name, getattr(foreign_rule, "label"))
                for start, end in matches
            )
    if exact_anchor_equalities:
        raise RuntimeError(f"foreign exact-anchor equality count {exact_anchor_equalities}")

    overlaps: list[dict[str, object]] = []
    for own_start, own_end, own_label in own_spans:
        for foreign_start, foreign_end, helper_name, foreign_label in foreign_spans:
            if own_start < foreign_end and foreign_start < own_end:
                overlaps.append(
                    {
                        "own": own_label,
                        "foreign_helper": helper_name,
                        "foreign_rule": foreign_label,
                    }
                )
    if overlaps:
        raise RuntimeError(f"foreign anchor-span overlaps: {overlaps}")
    return {
        "foreign_helper_sha256": identities,
        "foreign_rule_spans_checked": len(foreign_spans),
        "own_rule_spans_checked": len(own_spans),
        "foreign_rules_consumed_by_downstream": consumed_foreign_rules,
        "exact_anchor_equalities": exact_anchor_equalities,
        "span_overlaps": overlaps,
        "pass": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe8-log", type=Path, required=True)
    parser.add_argument("--probe8-error-headers", type=Path, required=True)
    parser.add_argument("--foreign-helper", action="append", type=Path, required=True)
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
    diagnostic_map = verify_authority(
        args.probe8_log.read_bytes(),
        args.probe8_error_headers.read_bytes(),
    )
    source_text = source.decode("utf-8")
    foreign_audit = None
    if not inverse:
        foreign_audit = collision_audit(source_text, args.foreign_helper)

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
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust inventory failure: {before_trust} -> {after_trust}")
    restored_text, _ = transform(result_text, not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    selected_coordinates = {
        (header.line, header.column)
        for rule in RULES for header in rule.headers
    }
    header_pattern = re.compile(
        r"^PrimalitySheafVerification/QYM\.lean:(\d+):(\d+): "
        r"error(?:\(([^\n)]*)\))?: (.*)$",
        re.MULTILINE,
    )
    all_scope_headers = [
        {
            "line": int(line),
            "column": int(column),
            "code": code or None,
            "message": message,
        }
        for line, column, code, message in header_pattern.findall(
            args.probe8_log.read_text(encoding="utf-8")
        )
        if 55_000 <= int(line) <= 61_671
    ]
    unselected = [
        header for header in all_scope_headers
        if (int(header["line"]), int(header["column"])) not in selected_coordinates
    ]
    record = {
        "schema": SCHEMA,
        "status": "CONDITIONAL_STATIC_PASS_EXACT_PROBE8_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "activation_gate": "TERMINAL_PROBE9_EXECUTION_REQUIRED",
        "mode": args.mode,
        "authority": {
            "probe8_run_id": 31969310662,
            "probe8_candidate_sha256": INPUT_SHA256,
            "probe8_candidate_git_blob": INPUT_GIT_BLOB,
            "probe8_log_sha256": LOG_SHA256,
            "probe8_error_headers_sha256": ERROR_HEADERS_SHA256,
            "probe8_error_headers": 344,
            "probe8_warning_headers": 374,
            "probe8_exit": 1,
            "probe8_panic": 0,
        },
        "scope": {
            "candidate_lines": [55000, 61671],
            "direct_producer_roots_only": True,
            "existing_probe7_probe8_probe9_50k_anchor_overlap": False,
            "heartbeat_or_upstream_owned_cascades_patched": False,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "active_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_headers_verified": len(diagnostic_map),
        "rules": rule_audit,
        "selected_exact_probe8_diagnostics": diagnostic_map,
        "scope_error_headers": len(all_scope_headers),
        "deliberate_unselected_scope_error_headers": unselected,
        "foreign_anchor_collision_audit": foreign_audit,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
