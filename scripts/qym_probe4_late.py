#!/usr/bin/env python3
"""Exact reversible late-frontier repairs for the terminal QYM probe-3 candidate.

This is a static transformer only: it never invokes Lean, Lake, Git, or the
network.  Every edit is an exact, guarded replacement anchored to an observed
probe-3 diagnostic at source line 40000 or later.  Larger quotient-domain,
topology, and bundled-coercion design roots are deliberately excluded.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe4-late-transform-v1"
EXPECTED_INPUT_SHA256 = "9e82073bdaf6339feb1ca09d70ab371947c6e07294ae01895a33c75f978bd780"
EXPECTED_INPUT_GIT_BLOB = "652a6b11899db967ec19c2f32ca7aa1ad2044c7a"
EXPECTED_INPUT_BYTES = 2_906_639
EXPECTED_INPUT_LF = 61_479
AUTHORITY_LOG_SHA256 = "501029e514ba6bc875527e1bc96fb9f571afda222e53e633078736dccaa71f56"

# Filled after independent in-memory materialization, then enforced on every run.
EXPECTED_OUTPUT_SHA256 = "dd3c969aed9721d5f0a08ce1f9df4a7cc123103f589df849b69e873437596b2d"
EXPECTED_OUTPUT_GIT_BLOB = "b8484566dd22fdfbe7f108a4ceb6e6d3ee7a1294"
EXPECTED_OUTPUT_BYTES = 2_908_470
EXPECTED_OUTPUT_LF = 61_491


@dataclass(frozen=True)
class Repair:
    label: str
    error_lines: tuple[int, ...]
    old: str
    new: str
    occurrences: int = 1


REPAIRS = (
    Repair(
        "minimum_nonnegative_current_order_api",
        (40327,),
        "  exact min_nonneg (abs_nonneg _) (abs_nonneg _)\n",
        "  exact le_min (abs_nonneg _) (abs_nonneg _)\n",
    ),
    Repair(
        "memLp_zero_namespace",
        (40719,),
        "  zero_mem' := by\n    apply (memLp_congr_ae\n      (widthTwoTwistedDifferenceQuotient_L2_zero_ae tau)).2\n    exact memLp_zero\n",
        "  zero_mem' := by\n    apply (memLp_congr_ae\n      (widthTwoTwistedDifferenceQuotient_L2_zero_ae tau)).2\n    exact MemLp.zero\n",
    ),
    Repair(
        "open_fixed_phase_graph_completion_for_hhalf_graph",
        (41499, 41509, 41518, 41645, 41647, 41658, 41668, 41912, 41916, 41923, 41931, 41932, 41942, 41943),
        "namespace QYM.FullCertification.P2ClassicalHhalfTraceExtension\n\nopen Mock2FA.PaperCorrections.AutomorphicSobolev\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.HalfIntegralMultiplier\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.DefinitionOneSobolev\nopen QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension\n",
        "namespace QYM.FullCertification.P2ClassicalHhalfTraceExtension\n\nopen Mock2FA.PaperCorrections.AutomorphicSobolev\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.HalfIntegralMultiplier\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.DefinitionOneSobolev\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.DefinitionOneSobolev.FixedPhaseGraphCompletion\nopen QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension\n",
    ),
    Repair(
        "upper_half_plane_exported_set_names",
        (43833, 43838),
        "  have hetaComplex : ContDiffOn ℂ ∞ ModularForm.eta ℍₒ := by\n    apply DifferentiableOn.contDiffOn\n    · intro z hz\n      exact\n        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt\n    · exact isOpen_upperHalfPlaneSet\n",
        "  have hetaComplex : ContDiffOn ℂ ∞ ModularForm.eta UpperHalfPlane.upperHalfPlaneSet := by\n    apply DifferentiableOn.contDiffOn\n    · intro z hz\n      exact\n        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt\n    · exact UpperHalfPlane.isOpen_upperHalfPlaneSet\n",
    ),
    Repair(
        "qualify_smooth_core_upperLift",
        (44345, 44346, 44354),
        "upperLift f",
        "Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.upperLift f",
        occurrences=4,
    ),
    Repair(
        "structure_groupoid_hasGroupoid_comp_namespace",
        (44942, 45786),
        "apply HasGroupoid.comp",
        "apply StructureGroupoid.HasGroupoid.comp",
        occurrences=2,
    ),
    Repair(
        "topological_opens_type_namespace",
        (44966,),
        "def interiorStage (Y : ℝ) : Opens GammaTwoQuotient :=\n",
        "def interiorStage (Y : ℝ) : TopologicalSpace.Opens GammaTwoQuotient :=\n",
    ),
    Repair(
        "topological_opens_inclusion_namespace",
        (44978,),
        "  Opens.inclusion (interiorStage_mono hYZ)\n",
        "  TopologicalSpace.Opens.inclusion (interiorStage_mono hYZ)\n",
    ),
    Repair(
        "open_gamma_two_cusp_for_collar_density",
        (45520,),
        "namespace QYM.FullCertification.P2HhalfCollarDensityExtension\n\nopen Mock2FA.PaperCorrections.AutomorphicSobolev\n",
        "namespace QYM.FullCertification.P2HhalfCollarDensityExtension\n\nopen Mock2FA.PaperCorrections.AutomorphicSobolev\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoCusp\n",
    ),
    Repair(
        "open_green_geometry_and_petersson_namespaces",
        (47219, 47220, 47238, 47238, 47330, 47335),
        "namespace QYM.FullCertification.P2GreenBoundaryStokesReductionExtension\n",
        "namespace QYM.FullCertification.P2GreenBoundaryStokesReductionExtension\n\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.DefinitionOneSobolev.WeightCorePetersson\n",
    ),
    Repair(
        "open_gamma_two_geometry_for_product_collar",
        (48503, 48504, 48509, 48511),
        "namespace QYM.FullCertification.P2CollarTraceExtension\n",
        "namespace QYM.FullCertification.P2CollarTraceExtension\n\nopen Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry\n",
    ),
    Repair(
        "qualify_final_bulk_half_weight_operators",
        (59860, 59860, 59860, 59903, 59903, 59903),
        "(fun z => Mock2FA.PaperCorrections.AutomorphicSobolev.heightC z ^ 2 * (Mock2FA.PaperCorrections.AutomorphicSobolev.dx X z + Mock2FA.PaperCorrections.AutomorphicSobolev.dy Y z))",
        "(fun z => Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.heightC z ^ 2 * (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.dx X z + Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.dy Y z))",
        occurrences=2,
    ),
    Repair(
        "edge_pairing_injective_explicit_congrArg",
        (40062,),
        "  · intro e f hef\n    rw [← hInvolutive e, ← hInvolutive f, hef]\n",
        "  · intro e f hef\n    calc\n      e = e.paired.paired := (hInvolutive e).symm\n      _ = f.paired.paired := congrArg (fun x => x.paired) hef\n      _ = f := hInvolutive f\n",
    ),
    Repair(
        "typed_sum_neg_rewrite",
        (40099,),
        "            exact Finset.sum_neg_distrib\n",
        "            rw [Finset.sum_neg_distrib]\n",
    ),
    Repair(
        "remove_three_closed_ring_tactics",
        (40442, 40445, 40447),
        "  by_cases hxy : 1 < x - y\n  · have hyx : ¬ 1 < y - x := by linarith\n    simp [hxy, hyx]\n    ring\n  · by_cases hyx : 1 < y - x\n    · simp [hxy, hyx]\n      ring\n    · simp [hxy, hyx]\n      ring\n",
        "  by_cases hxy : 1 < x - y\n  · have hyx : ¬ 1 < y - x := by linarith\n    simp [hxy, hyx]\n  · by_cases hyx : 1 < y - x\n    · simp [hxy, hyx]\n    · simp [hxy, hyx]\n",
    ),
    Repair(
        "width_two_energy_ennreal_top",
        (40746,),
        "    widthTwoGagliardoEnergy tau f < ∞ := by\n",
        "    widthTwoGagliardoEnergy tau f < (∞ : ℝ≥0∞) := by\n",
    ),
    Repair(
        "named_trace_energy_ennreal_top",
        (41248,),
        "        (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) < ∞ :=\n",
        "        (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) < (∞ : ℝ≥0∞) :=\n",
    ),
    Repair(
        "width_two_norm_fst_explicit_type",
        (40979,),
        "  exact WithLp.norm_fst_le (f : WidthTwoHhalfGraphAmbient)\n",
        "  exact WithLp.norm_fst_le ActualFixedPhaseWidthTwoL2 (f : WidthTwoHhalfGraphAmbient)\n",
    ),
    Repair(
        "width_two_norm_snd_explicit_type",
        (40986,),
        "  exact WithLp.norm_snd_le (f : WidthTwoHhalfGraphAmbient)\n",
        "  exact WithLp.norm_snd_le ActualFixedPhaseWidthTwoL2 (f : WidthTwoHhalfGraphAmbient)\n",
    ),
    Repair(
        "continuousAt_comp_current_signature",
        (41069,),
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp\n          x hcoe.continuousAt\n",
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp\n          hcoe.continuousAt\n",
    ),
    Repair(
        "convex_Icc_concrete_interval",
        (41213,),
        "    (actualFixedPhaseNamedCuspTraceRepresentative_contDiff\n      n kappa Y u).contDiffOn.exists_lipschitzOnWith\n        (by simp) convex_Icc isCompact_Icc\n",
        "    (actualFixedPhaseNamedCuspTraceRepresentative_contDiff\n      n kappa Y u).contDiffOn.exists_lipschitzOnWith\n        (by simp) (convex_Icc (0 : ℝ) 4) isCompact_Icc\n",
    ),
    Repair(
        "mdifferentiable_infinite_order_nonzero",
        (45108,),
        "    (manifoldDeckMap_smooth γ).mdifferentiable one_ne_zero z\n",
        "    (manifoldDeckMap_smooth γ).mdifferentiable (by simp) z\n",
    ),
    Repair(
        "product_collar_norm_fst_explicit_type",
        (48448,),
        "  exact WithLp.norm_fst_le x\n",
        "  exact WithLp.norm_fst_le ℂ x\n",
    ),
    Repair(
        "withLp_smul_projection_namespaces",
        (48700, 48700, 48700),
        "    simp only [smul_fst, smul_snd, map_smul, Submodule.coe_smul]\n",
        "    simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, Submodule.coe_smul]\n",
    ),
    Repair(
        "stage_measure_ennreal_top",
        (49712,),
        "    actualStageMeasure Y Set.univ < ∞ := by\n",
        "    actualStageMeasure Y Set.univ < (∞ : ℝ≥0∞) := by\n",
    ),
    Repair(
        "isOpen_measure_pos_explicit_measure",
        (49730,),
        "    (isOpen_interior.measure_pos hY)\n",
        "    (isOpen_interior.measure_pos actualQuotientHyperbolicMeasure hY)\n",
    ),
    Repair(
        "certificate_stage_measure_ennreal_top",
        (50179,),
        "    actualStageMeasure Y Set.univ < ∞ ∧\n",
        "    actualStageMeasure Y Set.univ < (∞ : ℝ≥0∞) ∧\n",
    ),
    Repair(
        "ambient_stage_measure_ennreal_top",
        (50340,),
        "  change ambientStageMeasure Y Set.univ < ∞\n",
        "  change ambientStageMeasure Y Set.univ < (∞ : ℝ≥0∞)\n",
    ),
    Repair(
        "continuousMap_toLp_coe_explicit_measure",
        (51599,),
        "  exact ContinuousMap.coeFn_toLp f\n",
        "  exact ContinuousMap.coeFn_toLp (QYM.FullCertification.P3ActualStageL2SectionsExtension.actualStageMeasure Y) f\n",
    ),
    Repair(
        "toLp_denseRange_explicit_ennreal_top",
        (51633, 51633),
        "    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)\n",
        "    (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))\n",
    ),
    Repair(
        "inner_smul_ofReal_core_namespaces",
        (52762, 53084, 53838, 54325),
        "inner_smul_ofReal_left, inner_smul_ofReal_right",
        "InnerProductSpace.Core.inner_smul_ofReal_left, InnerProductSpace.Core.inner_smul_ofReal_right",
        occurrences=4,
    ),
    Repair(
        "inner_self_norm_sq_explicit_scalar",
        (53932,),
        "  rw [actualStageDiscriminantForm_eq_sqrt_inner]\n  exact inner_self_eq_norm_sq _\n",
        "  rw [actualStageDiscriminantForm_eq_sqrt_inner]\n  exact inner_self_eq_norm_sq (𝕜 := ℂ) _\n",
    ),
    Repair(
        "innerSL_apply_norm_explicit_scalar",
        (55016,),
        "  exact innerSL_apply_norm (actualInverseEtaTestVector Y)\n",
        "  exact innerSL_apply_norm ℂ (actualInverseEtaTestVector Y)\n",
    ),
    Repair(
        "star_mul_explicit_functional",
        (55099,),
        "  exact star_mul' _\n",
        "  exact star_mul' (actualInverseEtaAnalysisFunctional Y u)\n",
    ),
    Repair(
        "natural_cutoff_strict_cast",
        (56552,),
        "  unfold naturalStageCutoff\n  positivity\n",
        "  unfold naturalStageCutoff\n  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n\n  linarith\n",
    ),
    Repair(
        "natural_cutoff_monotone_add_comm",
        (56558,),
        "  exact add_le_add_right (Nat.cast_le.mpr hmn) 2\n",
        "  simpa [add_comm] using add_le_add_right (Nat.cast_le.mpr hmn) 2\n",
    ),
    Repair(
        "global_dominating_lintegral_ennreal_top",
        (57048,),
        "      ∂actualGlobalQuotientMeasure) ≠ ∞ := by\n",
        "      ∂actualGlobalQuotientMeasure) ≠ (∞ : ℝ≥0∞) := by\n",
    ),
    Repair(
        "global_projection_limit_explicit_ennreal_top",
        (57116, 57116),
        "      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]\n",
        "      (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))]\n",
    ),
    Repair(
        "physical_raise_closable_explicit_n",
        (57631,),
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise_isClosable\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise_isClosable n\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
    ),
    Repair(
        "physical_lower_closable_explicit_n",
        (57641,),
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc_isClosable\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc_isClosable n\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
    ),
    Repair(
        "physical_joint_closable_explicit_n",
        (57651,),
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc_isClosable\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc_isClosable n\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
    ),
    Repair(
        "closed_raise_explicit_n",
        (57663,),
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise_isClosed\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise_isClosed n\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
    ),
    Repair(
        "closed_lower_explicit_n",
        (57673,),
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc_isClosed\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc_isClosed n\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
    ),
    Repair(
        "closed_joint_explicit_n",
        (57683,),
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc_isClosed\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
        "  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc_isClosed n\n    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual\n",
    ),
    Repair(
        "coordinate_form_expose_star_before_map",
        (58407,),
        "    coordinateHamiltonianForm_apply, map_add, map_mul,\n    RCLike.star_def, RCLike.conj_ofReal]\n",
        "    coordinateHamiltonianForm_apply, RCLike.star_def, map_add, map_mul,\n    RCLike.conj_ofReal]\n",
    ),
    Repair(
        "coordinate_form_expose_star_before_conj_real",
        (58422,),
        "    inner_add_left, potential_apply, inner_smul_left,\n    RCLike.conj_ofReal]\n",
        "    inner_add_left, potential_apply, inner_smul_left,\n    RCLike.star_def, RCLike.conj_ofReal]\n",
    ),
    Repair(
        "escape_open_set_cutoff_cast",
        (60746,),
        "    dsimp [Y0, QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.naturalStageCutoff]\n    positivity\n",
        "    dsimp [Y0, QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.naturalStageCutoff]\n    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n\n    linarith\n",
    ),
    Repair(
        "escape_open_set_high_height_goal",
        (60755,),
        "  let h : QYM.FullCertification.P2CuspCollarClosureExtension.HighHeight := ⟨Y0 + 1 / 2, by linarith⟩\n",
        "  let h : QYM.FullCertification.P2CuspCollarClosureExtension.HighHeight :=\n    ⟨Y0 + 1 / 2, by\n      change 1 < Y0 + (1 / 2 : ℝ)\n      linarith [hY0]⟩\n",
    ),
    Repair(
        "escape_open_set_measure_ennreal_top",
        (60784,),
        "        (actualCutoffEscapeOpenSet n) < ∞ := by\n",
        "        (actualCutoffEscapeOpenSet n) < (∞ : ℝ≥0∞) := by\n",
    ),
)


TRUST_PATTERNS = {
    "sorry": re.compile(r"(?<![\w.])sorry(?![\w])"),
    "admit": re.compile(r"(?<![\w.])admit(?![\w])"),
    "native_decide": re.compile(r"(?<![\w.])native_decide(?![\w])"),
    "Lean.ofReduceBool": re.compile(r"(?<![\w.])Lean\.ofReduceBool(?![\w])"),
    "axiom_declaration": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "unsafe_declaration": re.compile(r"^[ \t]*unsafe[ \t]+(?:def|theorem|abbrev|instance)\b", re.MULTILINE),
    "maxHeartbeats_zero": re.compile(r"^[ \t]*set_option[ \t]+maxHeartbeats[ \t]+0\b", re.MULTILINE),
}


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def hygiene(raw: bytes, label: str) -> dict[str, object]:
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw or b"\x00" in raw:
        raise AssertionError(f"{label}: BOM/CR/NUL invariant violated")
    if not raw.endswith(b"\n"):
        raise AssertionError(f"{label}: terminal LF required")
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw), "git_blob": git_blob(raw), "bytes": len(raw),
        "lf": raw.count(b"\n"), "utf8": True, "bom": False, "cr": False,
        "nul": False, "terminal_lf": True,
    }


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def transform(text: str, *, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    rows = list(REPAIRS)
    if inverse:
        rows.reverse()
    audit: list[dict[str, object]] = []
    for repair in rows:
        old = repair.new if inverse else repair.old
        new = repair.old if inverse else repair.new
        old_count = text.count(old)
        new_count = text.count(new)
        # The exact source count is the collision guard.  For pure insertion
        # repairs, the replacement intentionally contains the source anchor,
        # so the opposite-form count can be nonzero in the inverse direction.
        # A pre-existing full replacement is still caught because it raises
        # ``old_count`` above the sealed occurrence count on inversion.
        if old_count != repair.occurrences:
            raise AssertionError(
                f"{repair.label}: expected {repair.occurrences} exact source; "
                f"found {old_count}/{new_count}"
            )
        text = text.replace(old, new)
        audit.append({
            "label": repair.label,
            "error_lines": list(repair.error_lines),
            "occurrences": repair.occurrences,
            "direction": "inverse" if inverse else "forward",
        })
    return text, audit


def require_identity(info: dict[str, object], *, output: bool) -> None:
    expected = (
        (EXPECTED_OUTPUT_SHA256, EXPECTED_OUTPUT_GIT_BLOB, EXPECTED_OUTPUT_BYTES, EXPECTED_OUTPUT_LF)
        if output else
        (EXPECTED_INPUT_SHA256, EXPECTED_INPUT_GIT_BLOB, EXPECTED_INPUT_BYTES, EXPECTED_INPUT_LF)
    )
    if output and EXPECTED_OUTPUT_SHA256 == "__TO_BE_SEALED__":
        return
    actual = (info["sha256"], info["git_blob"], info["bytes"], info["lf"])
    if actual != expected:
        raise AssertionError(f"{'output' if output else 'input'} identity mismatch: {actual!r}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--audit", type=Path)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()

    source = args.input.read_bytes()
    source_info = hygiene(source, "source")
    require_identity(source_info, output=args.mode == "inverse")
    result_text, detail = transform(source.decode("utf-8"), inverse=args.mode == "inverse")
    result = result_text.encode("utf-8")
    result_info = hygiene(result, "result")
    require_identity(result_info, output=args.mode == "forward")
    restored_text, _ = transform(result_text, inverse=args.mode != "inverse")
    if restored_text.encode("utf-8") != source:
        raise AssertionError("byte-exact forward/inverse roundtrip failed")
    before = trust_counts(source.decode("utf-8"))
    after = trust_counts(result_text)
    if before != after or any(before.values()):
        raise AssertionError("trust-zero inventory changed or is nonzero")

    audit = {
        "schema": "qym-probe4-late-transform-audit-v1",
        "mode": args.mode,
        "source": source_info,
        "result": result_info,
        "repairs": detail,
        "repair_rules": len(detail),
        "error_headers_targeted": sum(len(r.error_lines) for r in REPAIRS),
        "inverse_byte_equal": True,
        "trust_counts": before,
        "lean_executed": False,
        "lake_executed": False,
        "remote_accessed": False,
    }
    if args.audit:
        args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    if args.output:
        args.output.write_bytes(result)
    if not args.check_only:
        print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
