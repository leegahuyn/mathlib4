#!/usr/bin/env python3
"""Exact, reversible Probe8 late projection over authoritative Probe7 bytes.

This helper is deliberately static: it performs exact-count text replacements,
checks the exact Probe7 compiler log headers which motivated them, and records
seven trust-pattern counts.  It never invokes Lean, Lake, Git, or the network,
and it never edits the canonical repository source.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe8-late-static-transform-v1"
INPUT_SHA256 = "342eb7aab3d5e71fc242706188abdb7cb1804cd04c79ed254e1715fe0876f3eb"
INPUT_GIT_BLOB = "9b53049115afcc674fac88f998b6716abddb0162"
INPUT_BYTES = 2_913_545
INPUT_LF = 61_593
LOG_SHA256 = "c31e12c9b5a47358a5128295f9c05d90783e9c5af79f63576c22f2e0a30120ee"

# Filled after the deterministic bootstrap projection, then enforced in both
# directions.  The bootstrap flag accepts only these explicit placeholders.
OUTPUT_SHA256 = "af8938858fd710f486601994f31a215bf718c894b44e4c867a3d959d02b4dbb7"
OUTPUT_GIT_BLOB = "a7810f1c70078f9977443296f9737a30263e0b4d"
OUTPUT_BYTES = 2_913_846
OUTPUT_LF = 61_615


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
        "eta_continuousAt_comp_supply_point",
        "      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp\n"
        "          hcoe.continuousAt\n",
        "      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp x\n"
        "          hcoe.continuousAt\n",
        (Header(41145, 10, "Application type mismatch"),),
        rationale="ContinuousAt.comp requires the intermediate point before the inner continuity proof.",
    ),
    Rule(
        "inverse_eta_product_expose_pi_mul",
        "  simpa only [inverseEtaPaperOrbitMultiplier_factor] using\n"
        "    hinverseEta.mul hdenPow\n",
        "  simpa only [inverseEtaPaperOrbitMultiplier_factor, Pi.mul_apply] using\n"
        "    hinverseEta.mul hdenPow\n",
        (Header(41193, 2, "Type mismatch: After simplification"),),
        rationale="Normalize multiplication of functions to the pointwise lambda expected by Continuous.",
    ),
    Rule(
        "lipschitz_constant_use_nnreal",
        "    ∃ K : ℝ≥0,\n",
        "    ∃ K : NNReal,\n",
        """
        placeholder
        """,
    ),
    Rule(
        "difference_quotient_zero_statement_pi_zero",
        "    widthTwoTwistedDifferenceQuotient tau (fun _ => 0) = 0 := by\n",
        "    widthTwoTwistedDifferenceQuotient tau (0 : ℝ → ℂ) = 0 := by\n",
        (Header(41401, 6, "Tactic `rewrite` failed"),),
        rationale="State the producer theorem in the same Pi-zero form used by its MemLp consumer.",
    ),
    Rule(
        "difference_quotient_add_statement_pi_add",
        "    widthTwoTwistedDifferenceQuotient tau (fun t => f t + g t) =\n"
        "      widthTwoTwistedDifferenceQuotient tau f +\n",
        "    widthTwoTwistedDifferenceQuotient tau (f + g) =\n"
        "      widthTwoTwistedDifferenceQuotient tau f +\n",
        (Header(41406, 6, "Tactic `rewrite` failed"),),
        rationale="State the producer theorem with Pi addition so rewrite sees the consumer expression.",
    ),
    Rule(
        "difference_quotient_smul_statement_pi_smul",
        "    widthTwoTwistedDifferenceQuotient tau (fun t => c * f t) =\n"
        "      c • widthTwoTwistedDifferenceQuotient tau f := by\n",
        "    widthTwoTwistedDifferenceQuotient tau (c • f) =\n"
        "      c • widthTwoTwistedDifferenceQuotient tau f := by\n",
        (Header(41411, 6, "Tactic `rewrite` failed"),),
        rationale="State the producer theorem with Pi scalar multiplication used by the submodule consumer.",
    ),
    Rule(
        "withlp_norm_snd_supply_first_type",
        "  exact WithLp.norm_snd_le\n"
        "    (u : ActualFixedPhaseHhalfTraceAmbient n Y)\n",
        "  exact WithLp.norm_snd_le (GraphSobolevCompletion n)\n"
        "    (u : ActualFixedPhaseHhalfTraceAmbient n Y)\n",
        (Header(41778, 4, "Application type mismatch"),),
        rationale="The current WithLp API takes the first product factor explicitly.",
    ),
    Rule(
        "named_cusp_segment_expose_composition",
        "  simpa only [actualFixedPhaseNamedCuspSegment] using\n"
        "    (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint_continuous kappa Y).comp\n"
        "      continuous_subtype_val\n",
        "  change Continuous\n"
        "    (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y ∘\n"
        "      Subtype.val)\n"
        "  exact\n"
        "    (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint_continuous kappa Y).comp\n"
        "      continuous_subtype_val\n",
        (Header(42130, 2, "Type mismatch: After simplification"),),
        rationale="Expose the definitionally equal composition instead of simplifying a named wrapper.",
    ),
    Rule(
        "modular_T_horizontal_add_comm",
        "      QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHeight, UpperHalfPlane.coe_vadd]\n",
        "      QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHeight, UpperHalfPlane.coe_vadd, add_comm]\n",
        (Header(42564, 124, "unsolved goals"),),
        rationale="Close the sole residual arithmetic goal 1 + t = t + 1.",
    ),
    Rule(
        "effective_gamma_action_change_native",
        "  have hgammaZ : (gamma : SL(2, ℤ)) • z = u := by\n"
        "    simpa only [u] using (hgamma z).symm\n",
        "  have hgammaZ : (gamma : SL(2, ℤ)) • z = u := by\n"
        "    change gamma • z = u\n"
        "    simpa only [u] using (hgamma z).symm\n",
        (Header(42829, 4, "Type mismatch: After simplification"),),
        rationale="Check the equality in GammaTwo's native action before it is coerced to SL(2,Z).",
    ),
    Rule(
        "selected_cusp_loop_remove_closed_rfl",
        "        rw [selectedHorocycleParam_eq_traceHorizontal]\n"
        "        rfl\n",
        "        rw [selectedHorocycleParam_eq_traceHorizontal]\n",
        (Header(42890, 8, "No goals to be solved"),),
        rationale="The rewrite already closes the branch; the following rfl is unreachable.",
    ),
    Rule(
        "zero_limit_expose_pi_zero_apply",
        "    simpa only [hzero] using hx\n",
        "    simpa only [hzero, Pi.zero_apply] using hx\n",
        (Header(43094, 4, "Type mismatch: After simplification"),),
        rationale="Normalize the function zero evaluated at x to the scalar zero.",
    ),
    Rule(
        "graph_closure_use_subtype_property",
        "    simpa only [← Submodule.topologicalClosure_coe] using z.property\n",
        "    exact z.property\n",
        (Header(43187, 4, "Type mismatch: After simplification"),),
        rationale="The completion subtype property is definitionally the required graph-closure membership.",
    ),
    Rule(
        "linear_range_destructure_membership",
        "    intro n\n"
        "    simpa only [QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoHhalfGraphRange, LinearMap.mem_range] using\n"
        "      hwRange n\n",
        "    intro n\n"
        "    rcases hwRange n with ⟨f, hf⟩\n"
        "    exact ⟨f, hf⟩\n",
        (Header(43195, 4, "Type mismatch: After simplification"),),
        rationale="Destructure range membership directly instead of relying on a mismatched mem_range simp shape.",
    ),
    Rule(
        "range_equiv_coe_close_defeq",
        "  simp only [widthTwoHhalfToL2RangeEquiv,\n"
        "    LinearEquiv.ofInjective_apply]\n",
        "  simp only [widthTwoHhalfToL2RangeEquiv,\n"
        "    LinearEquiv.ofInjective_apply]\n"
        "  rfl\n",
        (Header(43292, 88, "unsolved goals"),),
        rationale="After unfolding, only coercion of the continuous linear map remains, which is reflexive.",
    ),
    Rule(
        "dense_range_witness_close_subtype_coe",
        "  exact ⟨QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoHhalfCoreMap tau f, by simp⟩\n",
        "  refine ⟨QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoHhalfCoreMap tau f, ?_⟩\n"
        "  change (f : QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2) = x\n"
        "  rfl\n",
        (Header(43337, 90, "unsolved goals"),),
        rationale="Expose the subtype coercion equality and discharge it definitionally.",
    ),
    Rule(
        "regular_edge_neighborhood_use_strict_hypotheses",
        "  | circularArc =>\n"
        "      have ht' :\n"
        "          ((-1 : ℝ) ≤ t ∧ t ≤ 1) ∧ t ≠ -1 ∧ t ≠ 1 := by\n"
        "        simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet, QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n"
        "      exact Icc_mem_nhds\n"
        "        (lt_of_le_of_ne ht'.1.1 (Ne.symm ht'.2.1))\n"
        "        (lt_of_le_of_ne ht'.1.2 ht'.2.2)\n"
        "  | leftVerticalSegment =>\n"
        "      have ht' : (0 : ℝ) ≤ t ∧ t ≠ 0 := by\n"
        "        simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet, QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n"
        "      exact Ici_mem_nhds (lt_of_le_of_ne ht'.1 (Ne.symm ht'.2))\n"
        "  | rightVerticalSegment =>\n"
        "      have ht' : (0 : ℝ) ≤ t ∧ t ≠ 0 := by\n"
        "        simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet, QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n"
        "      exact Ici_mem_nhds (lt_of_le_of_ne ht'.1 (Ne.symm ht'.2))\n",
        "  | circularArc =>\n"
        "      have ht' : (-1 : ℝ) < t ∧ t < 1 := by\n"
        "        simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n"
        "      exact Icc_mem_nhds ht'.1 ht'.2\n"
        "  | leftVerticalSegment =>\n"
        "      have ht' : (0 : ℝ) < t := by\n"
        "        simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n"
        "      exact Ici_mem_nhds ht'\n"
        "  | rightVerticalSegment =>\n"
        "      have ht' : (0 : ℝ) < t := by\n"
        "        simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "          QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "          Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n"
        "      exact Ici_mem_nhds ht'\n",
        (
            Header(43448, 8, "Type mismatch: After simplification"),
            Header(43456, 8, "Type mismatch: After simplification"),
            Header(43462, 8, "Type mismatch: After simplification"),
        ),
        rationale="The regular-set simplification already yields strict inequalities; use those directly.",
    ),
    Rule(
        "circular_arc_bounds_use_strict_hypothesis",
        "  have ht' :\n"
        "      ((-1 : ℝ) ≤ t ∧ t ≤ 1) ∧ t ≠ -1 ∧ t ≠ 1 := by\n"
        "    simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet, QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "      QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n"
        "  exact ⟨lt_of_le_of_ne ht'.1.1 (Ne.symm ht'.2.1),\n"
        "    lt_of_le_of_ne ht'.1.2 ht'.2.2⟩\n",
        "  simpa [QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet,\n"
        "    QYM.FullCertification.P2NormalGreenExtension.edgeParameterSet,\n"
        "    QYM.FullCertification.P2NormalGreenExtension.edgeEndpointSet,\n"
        "    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet,\n"
        "    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints] using ht\n",
        (Header(43475, 4, "Type mismatch: After simplification"),),
        rationale="The hypothesis simplifies exactly to the theorem's strict-bound conclusion.",
    ),
    Rule(
        "circular_radicand_derivative_unfold_id",
        "  convert (hasDerivAt_const t (1 : ℝ)).sub\n"
        "    (((hasDerivAt_id t).div_const 2).pow 2) using 1 <;> ring\n",
        "  convert (hasDerivAt_const t (1 : ℝ)).sub\n"
        "    (((hasDerivAt_id t).div_const 2).pow 2) using 1 <;>\n"
        "      simp only [id_eq] <;> ring\n",
        (Header(43498, 60, "unsolved goals"),),
        rationale="Beta-normalize id t before the arithmetic normalization.",
    ),
    Rule(
        "edge_derivative_transport_outer_point",
        "  have hOuter :=\n"
        "    (selectedRepresentativeChart_hasStrictDerivAt e.1 z).hasDerivAt.complexToReal_fderiv\n"
        "  have hBase := baseEdgeCoordinate_hasDerivAt e ht\n",
        "  have hOuter :=\n"
        "    (selectedRepresentativeChart_hasStrictDerivAt e.1 z).hasDerivAt.complexToReal_fderiv\n"
        "  rw [hz] at hOuter\n"
        "  have hBase := baseEdgeCoordinate_hasDerivAt e ht\n",
        (Header(43632, 16, "Application type mismatch"),),
        rationale="Transport the outer derivative base point along the already proved coordinate equality.",
    ),
    Rule(
        "hyperbolic_normal_remove_stale_star_mul",
        "          (star w * w) by ring,\n"
        "    star_mul']\n",
        "          (star w * w) by ring]\n",
        (
            Header(44253, 4, "Tactic `rewrite` failed"),
            Header(44275, 4, "Tactic `rewrite` failed"),
        ),
        occurrences=2,
        rationale="The preceding show rewrite already exposes star w * w; no star-of-product remains.",
    ),
    Rule(
        "d1_action_coordinate_expose_moebius",
        "  simpa [Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate, gammaTwoMoebiusCoordinate] using\n"
        "    (d1_gammaTwoMoebiusCoordinate γ z ξ)\n",
        "  change d1 (gammaTwoMoebiusCoordinate γ) z ξ =\n"
        "    ξ / inverseEtaPaperOrbitDenom γ z ^ 2\n"
        "  exact d1_gammaTwoMoebiusCoordinate γ z ξ\n",
        (Header(44335, 2, "Type mismatch: After simplification"),),
        rationale="Expose the action-coordinate definition before applying the exact d1 theorem.",
    ),
    Rule(
        "selected_cusp_circle_expose_lift_composition",
        "  simpa only [Function.comp_apply, selectedCuspCircle_coe] using\n"
        "    QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop_continuous q Y\n",
        "  have hfun : selectedCuspCircle q Y ∘ Quotient.mk' =\n"
        "      QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop q Y := by\n"
        "    funext t\n"
        "    exact selectedCuspCircle_coe q Y t\n"
        "  rw [hfun]\n"
        "  exact\n"
        "    QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop_continuous q Y\n",
        (Header(44735, 2, "Type mismatch: After simplification"),),
        rationale="After quotient continuity reduction, expose the selected loop itself.",
    ),
    Rule(
        "smooth_pregroupoid_unfold_property",
        "  simpa only [OpenPartialHomeomorph.symm_symm] using hSmooth z w\n",
        "  simpa only [upperHalfPlaneSmoothPregroupoid,\n"
        "    OpenPartialHomeomorph.symm_symm] using hSmooth z w\n",
        (Header(45003, 2, "Type mismatch: After simplification"),),
        rationale="Unfold the pregroupoid property wrapper to the ContMDiffOn residual.",
    ),
    Rule(
        "manifold_derivative_join_field_chain",
        "    (gammaTwoMoebiusChart_hasStrictDerivAt γ z).hasDerivAt.\n"
        "      hasFDerivAt.fderiv\n",
        "    (gammaTwoMoebiusChart_hasStrictDerivAt γ z).hasDerivAt.hasFDerivAt.fderiv\n",
        (Header(45197, 58, "Invalid field notation"),),
        rationale="A field-notation chain cannot end a line immediately after the dot token.",
    ),
    Rule(
        "collar_scale_tendsto_expose_definition",
        "  simpa only [widthTwoCollarScale] using\n"
        "    (tendsto_one_div_add_atTop_nhds_zero_nat :\n"
        "      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))\n",
        "  change Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))\n"
        "    atTop (𝓝 (0 : ℝ))\n"
        "  exact tendsto_one_div_add_atTop_nhds_zero_nat\n",
        (Header(45362, 2, "Type mismatch: After simplification"),),
        rationale="Expose the definitionally equal sequence instead of simplifying the named function under Tendsto.",
    ),
    Rule(
        "collar_cutoff_limit_expose_pi_div",
        "  simpa only [widthTwoCollarCutoff, add_zero, div_self hbump.ne'] using hquot\n",
        "  simpa only [widthTwoCollarCutoff, Pi.div_apply, add_zero,\n"
        "    div_self hbump.ne'] using hquot\n",
        (Header(45429, 2, "Type mismatch: After simplification"),),
        rationale="Normalize division of function-valued limits to pointwise division.",
    ),
    Rule(
        "collar_complex_limit_expose_comp_apply",
        "    simpa using\n"
        "      (Complex.ofRealCLM.continuous.tendsto (1 : ℝ)).comp hreal\n",
        "    change Tendsto\n"
        "      (Complex.ofRealCLM ∘ fun n : ℕ => widthTwoCollarCutoff n x)\n"
        "      atTop (𝓝 (1 : ℂ))\n"
        "    exact\n"
        "      (Complex.ofRealCLM.continuous.tendsto (1 : ℝ)).comp hreal\n",
        (Header(45483, 4, "Type mismatch: After simplification"),),
        rationale="Normalize the continuous linear map composition to the expected pointwise coercion.",
    ),
    Rule(
        "indicator_absent_branch_close_zero_le_zero",
        "  · simp only [Set.indicator_of_notMem hxs, norm_zero]\n",
        "  · simp only [Set.indicator_of_notMem hxs, norm_zero]\n"
        "    exact le_rfl\n",
        (Header(45523, 2, "unsolved goals"),),
        rationale="The absent-indicator branch reduces exactly to 0 ≤ 0.",
    ),
    Rule(
        "covering_transition_expose_composition",
        "  simpa only [Function.comp_apply] using\n"
        "    (coveringSheetTransition z w).continuousOn.comp_continuous\n"
        "      continuous_subtype_val (fun x ↦ x.2)\n",
        "  change Continuous ((coveringSheetTransition z w) ∘ Subtype.val)\n"
        "  exact\n"
        "    (coveringSheetTransition z w).continuousOn.comp_continuous\n"
        "      continuous_subtype_val (fun x ↦ x.2)\n",
        (Header(45730, 2, "Type mismatch: After simplification"),),
        rationale="Expose the restriction as the composition returned by comp_continuous.",
    ),
    Rule(
        "raw_high_cusp_periodic_beta_reduce",
        "  intro t\n"
        "  unfold rawHighCuspMap\n"
        "  rw [selectedHighPoint_eq_selectedHorocycleParam,\n",
        "  intro t\n"
        "  unfold rawHighCuspMap\n"
        "  change gammaTwoQuotientMk (selectedHighPoint q (t + 2, h)) =\n"
        "    gammaTwoQuotientMk (selectedHighPoint q (t, h))\n"
        "  rw [selectedHighPoint_eq_selectedHorocycleParam,\n",
        (Header(46113, 6, "Tactic `rewrite` failed"),),
        rationale="Beta-reduce the periodicity lambda before rewriting selectedHighPoint.",
    ),
    Rule(
        "inner_self_supply_coordinate_argument",
        "  unfold inverseEtaFibreHermitian\n"
        "  exact inner_self_eq_norm_sq (𝕜 := ℂ) _\n",
        "  unfold inverseEtaFibreHermitian\n"
        "  exact inner_self_eq_norm_sq (𝕜 := ℂ)\n"
        "    (inverseEtaFibreCoordinate u)\n",
        (Header(48009, 8, "typeclass instance problem is stuck"),),
        rationale="Fix the vector type before InnerProductSpace synthesis begins.",
    ),
)


# Repair the generated placeholder above in a syntax-visible way kept close to
# the rule table; doing this after construction preserves immutable dataclasses.
RULES = tuple(
    Rule(
        r.label,
        r.old,
        r.new,
        (
            Header(41288, 10, "failed to synthesize instance of type class"),
            Header(41288, 12, "failed to synthesize instance of type class"),
            Header(43988, 10, "failed to synthesize instance of type class"),
            Header(43988, 12, "failed to synthesize instance of type class"),
        ) if r.label == "lipschitz_constant_use_nnreal" else r.headers,
        2 if r.label == "lipschitz_constant_use_nnreal" else r.occurrences,
        "Use the canonical NNReal type name; ℝ≥0 is parsed here as a relation on Type."
        if r.label == "lipschitz_constant_use_nnreal" else r.rationale,
    )
    for r in RULES
)


DELIBERATE_EXCLUSIONS = (
    41198, 41263, 41280, 41802, 41998, 42000, 42019, 42189,
    42573, 42579, 42691, 42699, 42702, 42710, 42723, 42727,
    43148, 43215, 43234, 43266, 43267, 43534, 43541, 43549,
    43585, 43751, 43759, 43772, 43789, 43944, 43971, 43973,
    44261, 44322, 44507, 45013, 45025, 45026, 45605, 46039,
    46074, 46075, 46145, 46464, 46846, 46886, 47765, 47850,
    47864, 47869, 47872, 47876, 47881, 47922, 47939, 47948,
    47956, 47999,
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
    actual_sha = sha256(log)
    if actual_sha != LOG_SHA256:
        raise RuntimeError(f"Probe7 log sha256 {actual_sha} != {LOG_SHA256}")
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
    parser.add_argument("--probe7-log", type=Path, required=True)
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
    log_headers = verify_log(args.probe7_log.read_bytes())

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
        "status": "STATIC_PASS_EXACT_PROBE7_REANCHORED_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe7_run_id": 31967530559,
            "probe7_job_id": 95214871166,
            "probe7_candidate_sha256": INPUT_SHA256,
            "probe7_candidate_git_blob": INPUT_GIT_BLOB,
            "probe7_log_sha256": LOG_SHA256,
            "probe7_error_headers": 414,
            "probe7_warning_headers": 378,
            "probe7_panic": 0,
            "probe7_exit": 1,
        },
        "source": source_shape,
        "result": result_shape,
        "scope": {"candidate_line_min": 40000, "candidate_line_max": 49999},
        "repair_families": len(RULES),
        "active_occurrences": sum(r["occurrences"] for r in rule_audit),
        "direct_headers_verified": len(log_headers),
        "rules": rule_audit,
        "selected_exact_probe7_lines": sorted(
            {h.line for rule in RULES for h in rule.headers}
        ),
        "deliberate_exclusions": list(DELIBERATE_EXCLUSIONS),
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
