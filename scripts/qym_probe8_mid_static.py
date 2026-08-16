#!/usr/bin/env python3
"""Static, byte-locked Probe8 repair projection for QYM lines 30000--39999.

The helper consumes only the terminal authoritative Probe7 candidate and log.
It does not invoke Lean, Lake, Git, the network, or mutate repository source.
Only rules whose direct producer diagnostics survived Probe7 are active; known
heartbeat/unknown-constant cascades around the classical trace extension and
rules whose direct headers disappeared are deliberately excluded.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass, replace
from pathlib import Path


SCHEMA = "qym-probe8-mid-reanchored-transform-v1"
INPUT_SHA256 = "342eb7aab3d5e71fc242706188abdb7cb1804cd04c79ed254e1715fe0876f3eb"
INPUT_GIT_BLOB = "9b53049115afcc674fac88f998b6716abddb0162"
INPUT_BYTES = 2_913_545
INPUT_LF = 61_593
LOG_SHA256 = "c31e12c9b5a47358a5128295f9c05d90783e9c5af79f63576c22f2e0a30120ee"
ERROR_HEADERS_SHA256 = "9384ab9fc971ade6ec6f5817c560f87b01fa9ddc1603630dae85199e79962a10"

# Filled after deterministic bootstrap generation, then enforced both ways.
OUTPUT_SHA256 = "40f7f1712acafa095860bd28194cc8e239a6165b2810cbf38b9a1887c173000a"
OUTPUT_GIT_BLOB = "8604c02366dd4114b4500f787f75449f63e3774a"
OUTPUT_BYTES = 2_915_922
OUTPUT_LF = 61_641


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
    direct_headers: tuple[Header, ...]
    cascade_headers: tuple[Header, ...] = ()
    occurrences: int = 1
    rationale: str = ""


RULES_BEFORE_PROBE7_REANCHOR: tuple[Rule, ...] = (
    Rule(
        "standard_hermitian_nonneg_fix_complex_scalar",
        "theorem standardHermitianMetricData_self_nonneg (tau : H) (z : ℂ) :\n"
        "    0 ≤ (standardHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg\n",
        "theorem standardHermitianMetricData_self_nonneg (tau : H) (z : ℂ) :\n"
        "    0 ≤ (standardHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg (𝕜 := ℂ)\n",
        (Header(31852, 8, "typeclass instance problem is stuck"),),
        rationale="Fix the inner-product scalar to Complex.",
    ),
    Rule(
        "standard_hermitian_norm_sq_fix_complex_scalar",
        "theorem standardHermitianMetricData_self_eq_norm_sq (tau : H) (z : ℂ) :\n"
        "    (standardHermitianMetricData.pairing tau z z).re = ‖z‖ ^ 2 := by\n"
        "  exact inner_self_eq_norm_sq z\n",
        "theorem standardHermitianMetricData_self_eq_norm_sq (tau : H) (z : ℂ) :\n"
        "    (standardHermitianMetricData.pairing tau z z).re = ‖z‖ ^ 2 := by\n"
        "  exact inner_self_eq_norm_sq (𝕜 := ℂ) z\n",
        (Header(31856, 8, "typeclass instance problem is stuck"),),
        rationale="Fix the inner-product scalar to Complex.",
    ),
    Rule(
        "inverse_eta_hermitian_nonneg_fix_complex_scalar",
        "theorem inverseEtaHermitianMetricData_self_nonneg\n"
        "    (tau : H) (z : ℂ) :\n"
        "    0 ≤ (inverseEtaHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg\n",
        "theorem inverseEtaHermitianMetricData_self_nonneg\n"
        "    (tau : H) (z : ℂ) :\n"
        "    0 ≤ (inverseEtaHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg (𝕜 := ℂ)\n",
        (Header(31883, 8, "typeclass instance problem is stuck"),),
        rationale="Fix the inner-product scalar to Complex.",
    ),
    Rule(
        "inverse_eta_hermitian_pos_fix_complex_scalar",
        "  rw [re_inner_self_pos]\n"
        "  exact mul_ne_zero\n"
        "    (Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero tau) hz\n",
        "  rw [re_inner_self_pos (𝕜 := ℂ)]\n"
        "  exact mul_ne_zero\n"
        "    (Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero tau) hz\n",
        (Header(31892, 6, "Tactic `rewrite` failed"),),
        rationale="Select the Complex re_inner_self_pos theorem explicitly.",
    ),
    Rule(
        "safe_matter_potential_inner_fix_complex_scalar",
        "  rw [safeMatterPotential_apply, inner_smul_right]\n",
        "  rw [safeMatterPotential_apply, inner_smul_right (𝕜 := ℂ)]\n",
        (Header(32064, 33, "Tactic `rewrite` failed"),),
        rationale="Fix the inner-product scalar before rewriting the right scalar action.",
    ),
    Rule(
        "preimage_xset_use_exact_quotient_mk_api",
        "  simpa only [XSet, gammaTwoQuotientMk, Quotient.mk''_eq_mk] using\n"
        "    (MulAction.quotient_preimage_image_eq_union_mul\n"
        "      (gammaTwoThreeCuspTruncation Y) (G := GammaTwoEffective))\n",
        "  change\n"
        "    (Quotient.mk'' : ℍ → GammaTwoQuotient) ⁻¹'\n"
        "        ((Quotient.mk'' : ℍ → GammaTwoQuotient) ''\n"
        "          gammaTwoThreeCuspTruncation Y) =\n"
        "      ⋃ g : GammaTwoEffective,\n"
        "        (g • ·) '' gammaTwoThreeCuspTruncation Y\n"
        "  exact MulAction.quotient_preimage_image_eq_union_mul\n"
        "    (gammaTwoThreeCuspTruncation Y) (G := GammaTwoEffective)\n",
        (Header(33595, 2, "Type mismatch: After simplification"),),
        rationale="State the exact Quotient.mk'' form consumed by the MulAction theorem.",
    ),
    Rule(
        "quotient_interior_image_subset_reduce_preimage_membership",
        "      rintro x ⟨w, hw, rfl⟩\n"
        "      exact interior_subset hw\n",
        "      rintro x ⟨w, hw, rfl⟩\n"
        "      change w ∈ gammaTwoQuotientMk ⁻¹' XSet Y\n"
        "      exact interior_subset hw\n",
        (Header(33620, 28, "Application type mismatch"),),
        rationale="The witness lies in the interior of the preimage, not the quotient interior.",
    ),
    Rule(
        "polygon_edge_range_change_dependent_aliases",
        "theorem polygonEdgeParam_range (e : PolygonEdge) :\n"
        "    Set.range (polygonEdgeParam e) = polygonEdgeSet e := by\n"
        "  simpa only [polygonEdgeParam, polygonEdgeSet] using\n"
        "    (gammaTwoActualPolygonEdgeParam_range e)\n",
        "theorem polygonEdgeParam_range (e : PolygonEdge) :\n"
        "    Set.range (polygonEdgeParam e) = polygonEdgeSet e := by\n"
        "  change Set.range (gammaTwoActualPolygonEdgeParam e) =\n"
        "    gammaTwoActualPolygonEdgeSet e\n"
        "  exact gammaTwoActualPolygonEdgeParam_range e\n",
        (Header(33999, 2, "Type mismatch: After simplification"),),
        rationale="Expose both dependent aliases with change before applying the exact range theorem.",
    ),
    Rule(
        "eta_section_polygon_pairing_qualify_scalar",
        "theorem etaSection_polygonPairing\n"
        "    (g : SmoothInvariantScalar) (e : PolygonEdge)\n",
        "theorem etaSection_polygonPairing\n"
        "    (g : QYM.Mock2EtaCovariantDerivativeExtension.Geometry.SmoothInvariantScalar)\n"
        "    (e : PolygonEdge)\n",
        (Header(34117, 9, "Ambiguous term"),),
        rationale="Disambiguate the original eta-gauge scalar from the graph facade alias.",
    ),
    Rule(
        "eta_gauge_polygon_pairing_qualify_scalar",
        "theorem etaGaugeDifferential_polygonPairing_eval\n"
        "    (g : SmoothInvariantScalar) (e : PolygonEdge)\n",
        "theorem etaGaugeDifferential_polygonPairing_eval\n"
        "    (g : QYM.Mock2EtaCovariantDerivativeExtension.Geometry.SmoothInvariantScalar)\n"
        "    (e : PolygonEdge)\n",
        (Header(34170, 9, "Ambiguous term"),),
        rationale="Disambiguate the original eta-gauge scalar from the graph facade alias.",
    ),
    Rule(
        "twisted_one_form_pairing_expose_matrix_coercion",
        "    A.1 (e.pairingElement • polygonEdgeParam e t)\n"
        "        (manifoldDeckDerivative e.pairingElement\n",
        "    A.1 ((e.pairingElement : SL(2, ℤ)) • polygonEdgeParam e t)\n"
        "        (manifoldDeckDerivative e.pairingElement\n",
        (Header(34164, 6, "Tactic `rewrite` failed"),),
        rationale="Match polygonEdge_pairing_param's explicit SL(2,Z) action in the changed hypothesis.",
    ),
    Rule(
        "horizontal_curve_derivative_use_ofreal_clm",
        "theorem hasDerivAt_horizontalHorocycleAmbientCurve\n"
        "    (H x : ℝ) :\n"
        "    HasDerivAt (horizontalHorocycleAmbientCurve H) 1 x := by\n"
        "  simpa [horizontalHorocycleAmbientCurve] using\n"
        "    (((hasDerivAt_id (x : ℂ)).comp_ofReal).add_const\n"
        "      ((H : ℂ) * Complex.I))\n",
        "theorem hasDerivAt_horizontalHorocycleAmbientCurve\n"
        "    (H x : ℝ) :\n"
        "    HasDerivAt (horizontalHorocycleAmbientCurve H) 1 x := by\n"
        "  have hreal : HasDerivAt (⇑Complex.ofRealCLM) 1 x :=\n"
        "    (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt\n"
        "  have hfun : (⇑Complex.ofRealCLM : ℝ → ℂ) =\n"
        "      (fun t : ℝ => (t : ℂ)) := by\n"
        "    funext t\n"
        "    rfl\n"
        "  rw [hfun] at hreal\n"
        "  change HasDerivAt\n"
        "    (fun t : ℝ => (t : ℂ) + (H : ℂ) * Complex.I) 1 x\n"
        "  exact hreal.add_const ((H : ℂ) * Complex.I)\n",
        (Header(34355, 2, "Type mismatch: After simplification"),),
        rationale="Use the already validated Complex.ofRealCLM derivative bridge.",
    ),
    Rule(
        "horizontal_curve_contdiff_use_ofreal_clm",
        "theorem contDiff_horizontalHorocycleAmbientCurve (H : ℝ) :\n"
        "    ContDiff ℝ ∞ (horizontalHorocycleAmbientCurve H) := by\n"
        "  unfold horizontalHorocycleAmbientCurve\n"
        "  fun_prop\n",
        "theorem contDiff_horizontalHorocycleAmbientCurve (H : ℝ) :\n"
        "    ContDiff ℝ ∞ (horizontalHorocycleAmbientCurve H) := by\n"
        "  change ContDiff ℝ (↑(⊤ : ℕ∞))\n"
        "    (fun x : ℝ => (x : ℂ) + (H : ℂ) * Complex.I)\n"
        "  simpa [Complex.ofRealCLM_apply] using\n"
        "    Complex.ofRealCLM.contDiff.add contDiff_const\n",
        (Header(34363, 2, "`fun_prop` was unable to prove"),),
        rationale="Use Mathlib's explicit real-to-complex continuous linear map smoothness.",
    ),
    Rule(
        "width_two_measure_infinity_annotate_ennreal",
        "    (volume : Measure ℝ) (Set.Icc 0 2) < ∞).ne\n",
        "    (volume : Measure ℝ) (Set.Icc 0 2) < (∞ : ℝ≥0∞)).ne\n",
        (
            Header(34476, 41, "Ambiguous term"),
            Header(34922, 41, "Ambiguous term"),
        ),
        occurrences=2,
        rationale="Measure values live in ENNReal; disambiguate infinity.",
    ),
    Rule(
        "horizontal_horocycle_subtype_continuity_change",
        "theorem horizontalHorocyclePoint_continuous\n"
        "    (H : ℝ) (hH : 0 < H) :\n"
        "    Continuous (horizontalHorocyclePoint H hH) := by\n"
        "  have hambient : Continuous\n"
        "      (fun x : ℝ => (x : ℂ) + (H : ℂ) * Complex.I) :=\n"
        "    Complex.continuous_ofReal.add continuous_const\n"
        "  exact hambient.subtype_mk _\n",
        "theorem horizontalHorocyclePoint_continuous\n"
        "    (H : ℝ) (hH : 0 < H) :\n"
        "    Continuous (horizontalHorocyclePoint H hH) := by\n"
        "  have hambient : Continuous\n"
        "      (fun x : ℝ => (x : ℂ) + (H : ℂ) * Complex.I) :=\n"
        "    Complex.continuous_ofReal.add continuous_const\n"
        "  change Continuous (fun x : ℝ =>\n"
        "    (⟨(x : ℂ) + (H : ℂ) * Complex.I, by simpa using hH⟩ : ℍ))\n"
        "  exact hambient.subtype_mk _\n",
        (Header(34510, 2, "Type mismatch"),),
        rationale="Expose the dependent UpperHalfPlane subtype constructor before subtype_mk.",
    ),
    Rule(
        "actual_horizontal_horocycle_subtype_continuity_change",
        "theorem actualFixedPhaseHorizontalHorocyclePoint_continuous\n"
        "    (Y : ℝ) :\n"
        "    Continuous (actualFixedPhaseHorizontalHorocyclePoint Y) := by\n"
        "  have hambient : Continuous\n"
        "      (fun x : ℝ =>\n"
        "        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=\n"
        "    Complex.continuous_ofReal.add continuous_const\n"
        "  exact hambient.subtype_mk _\n",
        "theorem actualFixedPhaseHorizontalHorocyclePoint_continuous\n"
        "    (Y : ℝ) :\n"
        "    Continuous (actualFixedPhaseHorizontalHorocyclePoint Y) := by\n"
        "  have hambient : Continuous\n"
        "      (fun x : ℝ =>\n"
        "        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=\n"
        "    Complex.continuous_ofReal.add continuous_const\n"
        "  change Continuous (fun x : ℝ =>\n"
        "    (⟨(x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I,\n"
        "      by simpa using actualFixedPhaseCuspHeight_pos Y⟩ : ℍ))\n"
        "  exact hambient.subtype_mk _\n",
        (Header(34909, 2, "Type mismatch"),),
        rationale="Expose the dependent UpperHalfPlane subtype constructor before subtype_mk.",
    ),
    Rule(
        "eta_trace_projection_supply_withlp_first_factor",
        "  exact WithLp.norm_snd_le (u : EtaTraceGraphAmbient Y)\n",
        "  exact WithLp.norm_snd_le (EtaH1GraphAmbient Y)\n"
        "    (u : EtaTraceGraphAmbient Y)\n",
        (Header(34746, 27, "Application type mismatch"),),
        rationale="The current WithLp.norm_snd_le API takes the first product factor explicitly.",
    ),
    Rule(
        "actual_trace_projection_supply_withlp_first_factor",
        "  exact WithLp.norm_snd_le (u : ActualFixedPhaseCuspTraceAmbient n)\n",
        "  exact WithLp.norm_snd_le (GraphSobolevCompletion n)\n"
        "    (u : ActualFixedPhaseCuspTraceAmbient n)\n",
        (Header(35472, 27, "Application type mismatch"),),
        rationale="The current WithLp.norm_snd_le API takes the first product factor explicitly.",
    ),
    Rule(
        "regular_preimage_beta_reduce_orbit_witness",
        "    rcases hrel with ⟨g, hgz⟩\n"
        "    have hreg : g • z ∈ regularUpstairs := by\n"
        "      rw [hgz]\n",
        "    rcases hrel with ⟨g, hgz⟩\n"
        "    change g • z = w at hgz\n"
        "    have hreg : g • z ∈ regularUpstairs := by\n"
        "      rw [hgz]\n",
        (Header(37430, 10, "Tactic `rewrite` failed"),),
        rationale="Beta-reduce the orbit witness function before rewriting the action.",
    ),
    Rule(
        "effective_action_free_unfold_abbrev_before_api",
        "  · intro hFree\n"
        "    rw [isCancelSMul_iff_stabilizer_eq_bot] at hFree\n"
        "    apply Set.eq_univ_of_forall\n"
        "    intro z\n"
        "    exact hFree z\n"
        "  · intro hRegular\n"
        "    rw [isCancelSMul_iff_stabilizer_eq_bot]\n",
        "  · intro hFree\n"
        "    change IsCancelSMul EffectiveGroup ℍ at hFree\n"
        "    rw [isCancelSMul_iff_stabilizer_eq_bot] at hFree\n"
        "    apply Set.eq_univ_of_forall\n"
        "    intro z\n"
        "    exact hFree z\n"
        "  · intro hRegular\n"
        "    change IsCancelSMul EffectiveGroup ℍ\n"
        "    rw [isCancelSMul_iff_stabilizer_eq_bot]\n",
        (
            Header(37489, 8, "Tactic `rewrite` failed"),
            Header(37494, 8, "Tactic `rewrite` failed"),
        ),
        rationale="Delta-reduce the Prop abbreviation before rewriting the IsCancelSMul API.",
    ),
    Rule(
        "quotient_chart_center_expose_inverse_application",
        "  · rw [(upstairsLocalHomeomorphAt (quotientLift x)).right_inv\n"
        "        (mem_quotientChartAtH_source x)]\n",
        "  · change\n"
        "      (upstairsLocalHomeomorphAt (quotientLift x))\n"
        "          ((upstairsLocalHomeomorphAt (quotientLift x)).symm x) =\n"
        "        (upstairsLocalHomeomorphAt (quotientLift x)) (quotientLift x)\n"
        "    rw [(upstairsLocalHomeomorphAt (quotientLift x)).right_inv\n"
        "        (mem_quotientChartAtH_source x)]\n",
        (Header(37771, 8, "Tactic `rewrite` failed"),),
        rationale="Expose quotientChartAtH as the inverse local homeomorphism before right_inv.",
    ),
    Rule(
        "open_map_apply_to_source_interior",
        "  have hUOpen : IsOpen U := hf U isOpen_interior\n",
        "  have hUOpen : IsOpen U := hf (interior S) isOpen_interior\n",
        (Header(38292, 31, "Application type mismatch"),),
        rationale="IsOpenMap consumes the source set; U is already its image.",
    ),
    Rule(
        "literal_cusp_membership_rewrite_set_equalities",
        "  have hz' :=\n"
        "    (literalCuspFrontierPart_eq_truncation_inter_horocycle\n"
        "      Y kappa).mp hz\n"
        "  have hw' :=\n"
        "    (literalCuspFrontierPart_eq_truncation_inter_horocycle\n"
        "      Y lambda).mp hw\n",
        "  have hz' := hz\n"
        "  rw [literalCuspFrontierPart_eq_truncation_inter_horocycle\n"
        "    Y kappa] at hz'\n"
        "  have hw' := hw\n"
        "  rw [literalCuspFrontierPart_eq_truncation_inter_horocycle\n"
        "    Y lambda] at hw'\n",
        (Header(38692, 4, "Application type mismatch"),),
        rationale="Rewrite membership with a Set equality instead of applying Eq.mp as an iff.",
    ),
    Rule(
        "saturation_neighborhood_beta_reduce_membership",
        "    exact mem_saturatedXStage_of_tileEnvelope_lt q\n"
        "      (by simpa only [U] using hx)\n",
        "    change\n"
        "      gammaTwoModularHeightEnvelope\n"
        "          ((gammaTwoCosetRep q)⁻¹ • x) <\n"
        "        gammaTwoCuspLevel Y at hx\n"
        "    exact mem_saturatedXStage_of_tileEnvelope_lt q hx\n",
        (Header(38995, 10, "Type mismatch: After simplification"),),
        rationale="Beta-reduce membership in the local set explicitly.",
    ),
    Rule(
        "cusp_saturation_bridge_named_stage_and_union",
        "    exact (mem_frontier_iff_notMem_interior hzSat).2\n"
        "      (h kappa z hz)\n"
        "  · intro h kappa z hz\n"
        "    exact (mem_frontier_iff_notMem_interior\n"
        "      ((saturatedXStage_isClosed Y).frontier_subset (h kappa hz))).1\n"
        "      (h kappa hz)\n",
        "    apply (mem_frontier_iff_notMem_interior hzSat).2\n"
        "    rw [saturatedXStage_eq_iUnion_translates]\n"
        "    exact h kappa z hz\n"
        "  · intro h kappa z hz\n"
        "    rw [← saturatedXStage_eq_iUnion_translates]\n"
        "    exact (mem_frontier_iff_notMem_interior\n"
        "      ((saturatedXStage_isClosed Y).frontier_subset (h kappa hz))).1\n"
        "      (h kappa hz)\n",
        (
            Header(39074, 6, "Application type mismatch"),
            Header(39076, 4, "Type mismatch"),
        ),
        rationale="Convert explicitly between the named saturation and its union-of-translates form.",
    ),
    Rule(
        "edge_transport_membership_destructure_dependent_pair",
        "      t ∈ edgeParameterSet e := by\n"
        "  cases e.2 with\n",
        "      t ∈ edgeParameterSet e := by\n"
        "  rcases e with ⟨q, e⟩\n"
        "  cases e with\n",
        (
            Header(39396, 15, "Tactic `rcases` failed"),
            Header(39398, 15, "Tactic `rcases` failed"),
            Header(39400, 24, "unsolved goals"),
            Header(39406, 25, "unsolved goals"),
        ),
        rationale="Eliminate the product and edge constructor together so dependent matches reduce.",
    ),
    Rule(
        "edge_endpoint_membership_destructure_dependent_pair",
        "      t ∈ edgeEndpointSet e := by\n"
        "  cases e.2 <;>\n"
        "    simp [edgeParameterTransport, edgeEndpointSet,\n",
        "      t ∈ edgeEndpointSet e := by\n"
        "  rcases e with ⟨q, e⟩\n"
        "  cases e <;>\n"
        "    simp [edgeParameterTransport, edgeEndpointSet,\n",
        (Header(39418, 31, "unsolved goals"),),
        rationale="Eliminate the product and edge constructor together so endpoint matches reduce.",
    ),
    Rule(
        "edge_parameter_set_measurable_destructure_dependent_pair",
        "theorem edgeParameterSet_measurable (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) :\n"
        "    MeasurableSet (edgeParameterSet e) := by\n"
        "  cases e.2 <;>\n"
        "    simp [edgeParameterSet, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet]\n",
        "theorem edgeParameterSet_measurable (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) :\n"
        "    MeasurableSet (edgeParameterSet e) := by\n"
        "  rcases e with ⟨q, e⟩\n"
        "  cases e <;>\n"
        "    simp [edgeParameterSet, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeParameterSet]\n",
        (Header(39436, 42, "unsolved goals"),),
        rationale="Eliminate the product and edge constructor together so measurable-set matches reduce.",
    ),
    Rule(
        "edge_integral_neg_change_homeomorph_coercion",
        "      have h :=\n"
        "        (Homeomorph.neg ℝ).measurableEmbedding.setIntegral_map\n"
        "          (μ := (volume : Measure ℝ)) f (Set.Icc (-1 : ℝ) 1)\n"
        "      rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h\n",
        "      have h :=\n"
        "        (Homeomorph.neg ℝ).measurableEmbedding.setIntegral_map\n"
        "          (μ := (volume : Measure ℝ)) f (Set.Icc (-1 : ℝ) 1)\n"
        "      change\n"
        "        (∫ y in Set.Icc (-1 : ℝ) 1, f y\n"
        "            ∂Measure.map Neg.neg (volume : Measure ℝ)) = _ at h\n"
        "      rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h\n",
        (Header(39458, 10, "Tactic `rewrite` failed"),),
        rationale="Expose Homeomorph.neg's coercion as Neg.neg before rewriting the mapped measure.",
    ),
    Rule(
        "normal_derivative_pairing_expose_matrix_coercion_forward",
        "    A.1 (e.pairingElement • actualEdgePoint e t)\n"
        "        (manifoldDeckDerivative e.pairingElement\n",
        "    A.1 ((e.pairingElement : SL(2, ℤ)) • actualEdgePoint e t)\n"
        "        (manifoldDeckDerivative e.pairingElement\n",
        (Header(39678, 6, "Tactic `rewrite` failed"),),
        rationale="Match actualEdgePoint_pairing's explicit SL(2,Z) action in the first changed hypothesis.",
    ),
    Rule(
        "normal_derivative_pairing_expose_matrix_coercion_reverse",
        "      A.1 (e.pairingElement • actualEdgePoint e t)\n"
        "          (manifoldDeckDerivative e.pairingElement\n",
        "      A.1 ((e.pairingElement : SL(2, ℤ)) • actualEdgePoint e t)\n"
        "          (manifoldDeckDerivative e.pairingElement\n",
        (Header(39731, 8, "Tactic `rewrite` failed"),),
        rationale="Match actualEdgePoint_pairing's explicit SL(2,Z) action in the second changed hypothesis.",
    ),
    Rule(
        "paired_flux_integral_unfold_after_integral_neg",
        "    _ = -orientedEdgeFluxIntegral X Y e := by\n"
        "      rw [integral_neg]\n",
        "    _ = -orientedEdgeFluxIntegral X Y e := by\n"
        "      rw [integral_neg, orientedEdgeFluxIntegral]\n",
        (Header(39911, 43, "unsolved goals"),),
        rationale="After integral_neg, unfold the named edge integral on the right.",
    ),
)


CODED_HEADER_RULES_BEFORE_PROBE7_REANCHOR: tuple[Rule, ...] = (
    Rule(
        "partial_operator_install_complete_space",
        "section PartialOperator\n\n"
        "variable {H : Type*} [NormedAddCommGroup H]\n"
        "variable [InnerProductSpace ℝ H]\n",
        "section PartialOperator\n\n"
        "variable {H : Type*} [NormedAddCommGroup H]\n"
        "variable [InnerProductSpace ℝ H] [CompleteSpace H]\n",
        (
            Header(30180, 27, "failed to synthesize instance of type class"),
            Header(30186, 5, "failed to synthesize instance of type class"),
        ),
        (Header(30184, 70, "unsolved goals"),),
        rationale="The LinearPMap adjoint and self-adjoint Star structure require completeness.",
    ),
    Rule(
        "coupled_state_matter_reduce_dependent_carrier",
        "    u.fst ∈ (⊤ : Submodule ℂ (MatterField Y)) := by\n"
        "  exact Submodule.mem_top\n",
        "    u.fst ∈ (⊤ : Submodule ℂ (MatterField Y)) := by\n"
        "  change (u.fst : MatterField Y) ∈\n"
        "    (⊤ : Submodule ℂ (MatterField Y))\n"
        "  exact Submodule.mem_top\n",
        (Header(30970, 8, "failed to synthesize instance of type class"),),
        rationale="Reduce FieldCarrier at the matter tag before elaborating Submodule.mem_top.",
    ),
    Rule(
        "coupled_state_gauge_reduce_dependent_carrier",
        "    u.snd ∈ (⊤ : Submodule ℂ (CoulombGaugeSlice Y divergence)) := by\n"
        "  exact Submodule.mem_top\n",
        "    u.snd ∈ (⊤ : Submodule ℂ (CoulombGaugeSlice Y divergence)) := by\n"
        "  change (u.snd : CoulombGaugeSlice Y divergence) ∈\n"
        "    (⊤ : Submodule ℂ (CoulombGaugeSlice Y divergence))\n"
        "  exact Submodule.mem_top\n",
        (Header(30976, 8, "failed to synthesize instance of type class"),),
        rationale="Reduce FieldCarrier at the gauge tag before elaborating Submodule.mem_top.",
    ),
    Rule(
        "arithmetic_group_preserve_subgroup_value",
        "abbrev ArithmeticGroup : Type := GammaTwo\n",
        "abbrev ArithmeticGroup := GammaTwo\n",
        (
            Header(33101, 4, "failed to synthesize instance of type class"),
            Header(33107, 4, "failed to synthesize instance of type class"),
            Header(33368, 6, "failed to synthesize instance of type class"),
            Header(33371, 26, "failed to synthesize instance of type class"),
        ),
        rationale="Do not coerce the subgroup value to its carrier Type in the public alias.",
    ),
    Rule(
        "smooth_compact_weight_core_qualify_namespace",
        "theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace\n"
        "    {k : ℤ} {M : HalfIntegralMultiplier GammaTwo k}\n"
        "    (u : SmoothCompactWeightCore M) :\n",
        "theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace\n"
        "    {k : ℤ} {M : HalfIntegralMultiplier GammaTwo k}\n"
        "    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore M) :\n",
        (Header(34100, 9, "Unknown identifier `SmoothCompactWeightCore`"),),
        rationale="The core lives in the nested SmoothCompactCoreGeometry namespace.",
    ),
    Rule(
        "inverse_eta_smooth_compact_weight_core_qualify_namespace",
        "theorem inverseEtaCore_hasMultiplierMatchedPolygonTrace\n"
        "    (u : SmoothCompactWeightCore\n"
        "      (inverseEtaMultiplier GammaTwo)) :\n",
        "theorem inverseEtaCore_hasMultiplierMatchedPolygonTrace\n"
        "    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore\n"
        "      (inverseEtaMultiplier GammaTwo)) :\n",
        (Header(34108, 9, "Unknown identifier `SmoothCompactWeightCore`"),),
        rationale="The inverse-eta specialization uses the same nested core namespace.",
    ),
    Rule(
        "named_cusp_curve_use_action_homeomorph_continuity",
        "  (continuous_const_smul (gammaTwoCuspScaling kappa)).comp\n"
        "    (actualFixedPhaseHorizontalHorocyclePoint_continuous Y)\n",
        "  (Homeomorph.smul (gammaTwoCuspScaling kappa)).continuous.comp\n"
        "    (actualFixedPhaseHorizontalHorocyclePoint_continuous Y)\n",
        (Header(35044, 3, "failed to synthesize instance of type class"),),
        rationale="Use the concrete modular-action homeomorphism instead of a missing generic ContinuousConstSMul instance.",
    ),
    Rule(
        "tile_height_open_map_use_action_homeomorph",
        "  exact UpperHalfPlane.isOpenMap_im.comp\n"
        "    (isOpenMap_smul (gammaTwoCosetRep q)⁻¹)\n",
        "  exact UpperHalfPlane.isOpenMap_im.comp\n"
        "    (Homeomorph.smul (gammaTwoCosetRep q)⁻¹).isOpenMap\n",
        (Header(38278, 5, "failed to synthesize instance of type class"),),
        rationale="Use the concrete action homeomorphism instead of a missing generic ContinuousConstSMul instance.",
    ),
    Rule(
        "saturation_neighborhood_use_action_homeomorph_continuity",
        "      (gammaTwoModularHeightEnvelope_continuous.comp\n"
        "        (continuous_const_smul (gammaTwoCosetRep q)⁻¹))\n"
        "      continuous_const\n"
        "  have hUSubset : U ⊆ saturatedXStage Y := by\n",
        "      (gammaTwoModularHeightEnvelope_continuous.comp\n"
        "        (Homeomorph.smul (gammaTwoCosetRep q)⁻¹).continuous)\n"
        "      continuous_const\n"
        "  have hUSubset : U ⊆ saturatedXStage Y := by\n",
        (Header(38990, 9, "failed to synthesize instance of type class"),),
        rationale="Use the concrete action homeomorphism for continuity.",
    ),
    Rule(
        "actual_edge_point_install_classical_decidable",
        "noncomputable def actualEdgePoint\n"
        "    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) : ℍ :=\n"
        "  if ht : t ∈ edgeParameterSet e then\n"
        "    QYM.FullCertification.PolygonTraceExtension.polygonEdgeParam e ⟨t, ht⟩\n"
        "  else UpperHalfPlane.I\n",
        "noncomputable def actualEdgePoint\n"
        "    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) : ℍ := by\n"
        "  classical\n"
        "  exact if ht : t ∈ edgeParameterSet e then\n"
        "    QYM.FullCertification.PolygonTraceExtension.polygonEdgeParam e ⟨t, ht⟩\n"
        "  else UpperHalfPlane.I\n",
        (Header(39485, 2, "failed to synthesize instance of type class"),),
        (
            Header(39492, 100, "unsolved goals"),
            Header(39501, 2, "Tactic `rfl` failed"),
        ),
        rationale="A dependent if over set membership needs a local classical Decidable instance.",
    ),
)


PROBE7_LINE_SHIFT = 10
RULES: tuple[Rule, ...] = tuple(
    replace(
        rule,
        direct_headers=tuple(
            replace(header, line=header.line + PROBE7_LINE_SHIFT)
            for header in rule.direct_headers
        ),
        cascade_headers=tuple(
            replace(header, line=header.line + PROBE7_LINE_SHIFT)
            for header in rule.cascade_headers
        ),
    )
    for rule in sorted(
        RULES_BEFORE_PROBE7_REANCHOR
        + CODED_HEADER_RULES_BEFORE_PROBE7_REANCHOR,
        key=lambda item: min(header.line for header in item.direct_headers),
    )
)

DELIBERATE_HEARTBEAT_CASCADE_WINDOW = (36_587, 37_186)


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
        raise RuntimeError(f"Probe7 log sha256 {sha256(log)} != {LOG_SHA256}")
    text = log.decode("utf-8")
    verified: list[dict[str, object]] = []
    for rule in RULES:
        for kind, headers in (
            ("direct", rule.direct_headers),
            ("cascade", rule.cascade_headers),
        ):
            for header in headers:
                pattern = re.compile(
                    rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                    rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
                )
                count = len(pattern.findall(text))
                if count != 1:
                    raise RuntimeError(
                        f"{rule.label}: {kind} diagnostic {header.line}:{header.column} "
                        f"{header.message!r} count {count}, expected 1"
                    )
                verified.append(
                    {
                        "rule": rule.label,
                        "kind": kind,
                        "line": header.line,
                        "column": header.column,
                        "message": header.message,
                        "count": count,
                    }
                )
    return verified


ERROR_HEADER_RE = re.compile(
    r"^PrimalitySheafVerification/QYM\.lean:(\d+):(\d+): "
    r"error(?:\(([^\n)]*)\))?: (.*)$",
    re.MULTILINE,
)
WARNING_HEADER_RE = re.compile(
    r"^PrimalitySheafVerification/QYM\.lean:(\d+):(\d+): "
    r"warning(?:\(([^\n)]*)\))?: (.*)$",
    re.MULTILINE,
)


def diagnostic_headers(text: str, severity: str) -> list[dict[str, object]]:
    pattern = ERROR_HEADER_RE if severity == "error" else WARNING_HEADER_RE
    return [
        {
            "line": int(line),
            "column": int(column),
            "code": code or None,
            "message": message,
        }
        for line, column, code, message in pattern.findall(text)
    ]


def verify_header_artifact(log: bytes, header_artifact: bytes) -> None:
    if sha256(header_artifact) != ERROR_HEADERS_SHA256:
        raise RuntimeError(
            "Probe7 error-header sha256 "
            f"{sha256(header_artifact)} != {ERROR_HEADERS_SHA256}"
        )
    log_lines = [
        line
        for line in log.decode("utf-8").splitlines()
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: error(?:\([^)]*\))?: ",
            line,
        )
    ]
    artifact_lines = header_artifact.decode("utf-8").splitlines()
    if log_lines != artifact_lines:
        raise RuntimeError("Probe7 error-header artifact does not match log headers")
    if len(artifact_lines) != 414:
        raise RuntimeError(
            f"Probe7 error-header count {len(artifact_lines)} != 414"
        )


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
                    for h in rule.direct_headers
                ],
                "cascade_headers": [
                    {"line": h.line, "column": h.column, "message": h.message}
                    for h in rule.cascade_headers
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
    parser.add_argument("--probe7-error-headers", type=Path, required=True)
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
    log_data = args.probe7_log.read_bytes()
    log_headers = verify_log(log_data)
    verify_header_artifact(
        log_data,
        args.probe7_error_headers.read_bytes(),
    )
    log_text = log_data.decode("utf-8")
    all_errors = diagnostic_headers(log_text, "error")
    all_warnings = diagnostic_headers(log_text, "warning")
    if len(all_errors) != 414 or len(all_warnings) != 378:
        raise RuntimeError(
            "Probe7 diagnostic counts "
            f"E{len(all_errors)}/W{len(all_warnings)} != E414/W378"
        )
    in_scope_errors = [
        header for header in all_errors
        if 30_000 <= int(header["line"]) <= 39_999
    ]
    selected_coordinates = {
        (header.line, header.column)
        for rule in RULES
        for header in rule.direct_headers + rule.cascade_headers
    }
    unpatched_in_scope_errors = [
        header for header in in_scope_errors
        if (int(header["line"]), int(header["column"]))
        not in selected_coordinates
    ]
    heartbeat_start, heartbeat_end = DELIBERATE_HEARTBEAT_CASCADE_WINDOW
    if any(
        heartbeat_start <= header.line <= heartbeat_end
        for rule in RULES
        for header in rule.direct_headers
    ):
        raise RuntimeError("active rule entered the excluded heartbeat cascade")

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
        "status": "STATIC_PASS_EXACT_PROBE7_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe7_run_id": 31967530559,
            "probe7_candidate_sha256": INPUT_SHA256,
            "probe7_candidate_git_blob": INPUT_GIT_BLOB,
            "probe7_log_sha256": LOG_SHA256,
            "probe7_error_headers_sha256": ERROR_HEADERS_SHA256,
            "probe7_error_headers": 414,
            "probe7_warning_headers": 378,
            "probe7_panic": 0,
            "probe7_exit": 1,
            "probe7_first_error_line": 25159,
        },
        "scope": {
            "candidate_lines": [30000, 39999],
            "heartbeat_cascade_patched": False,
            "probe7_rules_replayed": False,
            "probe7_is_exact_input": True,
            "probe7_line_reanchor_delta": PROBE7_LINE_SHIFT,
            "excluded_heartbeat_cascade_window": [
                heartbeat_start,
                heartbeat_end,
            ],
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "active_occurrences": sum(r["occurrences"] for r in rule_audit),
        "direct_headers_verified": sum(
            1 for h in log_headers if h["kind"] == "direct"
        ),
        "cascade_headers_verified": sum(
            1 for h in log_headers if h["kind"] == "cascade"
        ),
        "rules": rule_audit,
        "selected_exact_probe7_diagnostics": log_headers,
        "selected_exact_probe7_lines": sorted(
            {
                h.line
                for rule in RULES
                for h in rule.direct_headers + rule.cascade_headers
            }
        ),
        "probe7_in_scope_error_headers": len(in_scope_errors),
        "deliberate_unpatched_in_scope_error_headers": unpatched_in_scope_errors,
        "coded_header_rule_families": [
            rule.label for rule in CODED_HEADER_RULES_BEFORE_PROBE7_REANCHOR
        ],
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
