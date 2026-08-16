#!/usr/bin/env python3
"""Conditional direct-root repairs for exact terminal-Probe11 lines 34000-42999.

This helper deliberately excludes the unresolved modular-arithmetic fan-out at
37725, the canonical-trace cascades in the early part of the window, and the
deep typeclass timeout at 41962.  Every selected rule is tied to an exact P11
diagnostic and an exact source anchor.  The transformer is byte-locked,
exact-counted, reversible, trust0, collision-audited against all seven active
Probe11 helpers with three declared downstream refinements, and activation-
disabled.  It never invokes Lean, Lake, Git,
the network, or a remote service.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe12-36k42k-p11-reanchored-v2-explicit-34k-owners"
INPUT_SHA256 = "d8290febb2b1c69cc8b911bcb672303beede1b87db290bd37c6608e39356cf25"
INPUT_GIT_BLOB = "9b5ba50acc8e2f3d6f55cf8cef6fc505926410cd"
INPUT_BYTES = 2_928_376
INPUT_LF = 61_891
LOG_SHA256 = "474f153278507d0ead7fe21675f326def15556281bd7b5cf67392836ea5ea97e"
HEADERS_SHA256 = "b0fe7508ba87fc324236cce71b74c59d042a0833ec1c101a1ae625a1f24dd4e6"
DIAGNOSTICS_SHA256 = "d9259b316d1c1317ea7e11f8f0370feaabacb3a2ae6066c3133ab748a2dee504"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "54c9a1ebff4bc2de215568b1e25e5b30ecfd17d0dee0ab8c1fc302603518eaf8"
OUTPUT_GIT_BLOB = "80cb3206d09e24bb7f168aa52746665a51d5c0c5"
OUTPUT_BYTES = 2_929_510
OUTPUT_LF = 61_924


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str
    code: str | None = None


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    rationale: str
    precedent: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "conjugation_bridge_normalize_gamma_action",
        "  have hDeltaFix : delta • (a • z) = a • z := by\n"
        "    simp [delta, mul_smul, hfix, mul_assoc]\n",
        "  have hfix' : (gamma : SL(2, ℤ)) • z = z := by\n"
        "    change gamma • z = z\n"
        "    exact hfix\n"
        "  have hDeltaFix : delta • (a • z) = a • z := by\n"
        "    simp [delta, mul_smul, hfix', mul_assoc]\n",
        (Header(37752, 46, "unsolved goals"),),
        "Normalize the subgroup action to the explicit SL(2,Z) action before simplifying the conjugate fixed-point equation.",
        "Exact P10 line 42919 uses the same change from an SL(2,Z) action to the GammaTwo representative action.",
    ),
    Rule(
        "tile_height_open_map_pin_action_homeomorph",
        "  exact UpperHalfPlane.isOpenMap_im.comp\n"
        "    (Homeomorph.smul (gammaTwoCosetRep q)⁻¹).isOpenMap\n",
        "  exact UpperHalfPlane.isOpenMap_im.comp\n"
        "    (Homeomorph.smul (gammaTwoCosetRep q)⁻¹ : ℍ ≃ₜ ℍ).isOpenMap\n",
        (
            Header(38419, 40, "unsolved goals"),
            Header(38422, 5, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        ),
        "Pin the upper-half-plane homeomorphism so instance search selects the certified action rather than seeking ContinuousConstSMul SL(2,Z) H.",
        "Exact P10 line 35117 already constructs the same typed action homeomorphism successfully.",
    ),
    Rule(
        "mod_two_negative_one_close_by_decide",
        "  have h00 : ((bridge 0 0 : ℤ) : ZMod 2) = 1 := by\n"
        "    rcases hdiag with hdiag | hdiag\n"
        "    · rw [hdiag.1]\n"
        "      simp\n"
        "    · rw [hdiag.1]\n"
        "      norm_num\n",
        "  have h00 : ((bridge 0 0 : ℤ) : ZMod 2) = 1 := by\n"
        "    rcases hdiag with hdiag | hdiag\n"
        "    · rw [hdiag.1]\n"
        "      simp\n"
        "    · rw [hdiag.1]\n"
        "      decide\n",
        (Header(38785, 4, "unsolved goals"),),
        "Close the fully concrete ZMod 2 equality by its decidable equality after rewriting the negative diagonal value.",
        "The exact residual goal is (-1 : ZMod 2) = 1; no algebraic assumption or cast is introduced.",
    ),
    Rule(
        "saturated_stage_beta_reduce_effective_action_witness",
        "  rcases effective_exists_gamma a with ⟨gamma, hgamma⟩\n"
        "  calc\n",
        "  rcases effective_exists_gamma a with ⟨gamma, hgamma⟩\n"
        "  change a • u = z at hau\n"
        "  calc\n",
        (Header(38992, 17, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Beta-reduce the image witness before the calc rewrite searches for a • u.",
        "The exact P10 target contains (fun x => a • x) u while hau is definitionally the desired a • u = z equality.",
    ),
    Rule(
        "tile_envelope_open_neighborhood_pin_action_homeomorph",
        "      (gammaTwoModularHeightEnvelope_continuous.comp\n"
        "        (Homeomorph.smul (gammaTwoCosetRep q)⁻¹).continuous)\n",
        "      (gammaTwoModularHeightEnvelope_continuous.comp\n"
        "        (Homeomorph.smul (gammaTwoCosetRep q)⁻¹ : ℍ ≃ₜ ℍ).continuous)\n",
        (Header(39138, 9, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),),
        "Pin the codomain of the action homeomorphism in the open-neighborhood continuity producer.",
        "This is the continuous counterpart of the exact typed homeomorphism used at P10 line 35117.",
    ),
    Rule(
        "cusp_transition_continuity_expose_pointwise_product",
        "  change Continuous\n"
        "    (fun x : ℝ =>\n"
        "      (inverseEtaPaperOrbitMultiplier GammaTwo n).factor\n"
        "        (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x))\n"
        "  simpa only [inverseEtaPaperOrbitMultiplier_factor, Pi.mul_apply] using\n"
        "    hinverseEta.mul hdenPow\n",
        "  change Continuous\n"
        "    (fun x : ℝ =>\n"
        "      (inverseEtaPaperOrbitMultiplier GammaTwo n).factor\n"
        "        (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x))\n"
        "  have hproduct := hinverseEta.mul hdenPow\n"
        "  change Continuous\n"
        "    (fun x : ℝ =>\n"
        "      (inverseEtaMultiplier GammaTwo).factor\n"
        "          (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x) *\n"
        "        UpperHalfPlane.denom\n"
        "          ((((actualFixedPhaseCuspDeckTranslation kappa : GammaTwo) :\n"
        "            SL(2, ℤ))) : GL (Fin 2) ℝ)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x) ^\n"
        "            ((2 : ℤ) * n)) at hproduct\n"
        "  simpa only [inverseEtaPaperOrbitMultiplier_factor] using hproduct\n",
        (Header(41353, 2, "Type mismatch: After simplification"),),
        "Expose Continuous.mul as a pointwise lambda before rewriting the paper-orbit factor theorem.",
        "The exact diagnostic differs only by function multiplication versus the beta-reduced pointwise product.",
    ),
    Rule(
        "cusp_trace_covariance_expose_sl2_action",
        "  rw [actualFixedPhaseNamedCuspTraceRepresentative,\n"
        "    actualFixedPhaseCuspHorocyclePoint_add_two]\n"
        "  simpa [actualFixedPhaseCuspBoundaryTransition] using\n"
        "    (u.2 FixedPhaseDifferentialWord.nil)\n"
        "      (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "      (actualFixedPhaseCuspHorocyclePoint kappa Y x)\n",
        "  rw [actualFixedPhaseNamedCuspTraceRepresentative,\n"
        "    actualFixedPhaseCuspHorocyclePoint_add_two]\n"
        "  change\n"
        "    ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)\n"
        "        ((((actualFixedPhaseCuspDeckTranslation kappa : GammaTwo) :\n"
        "          SL(2, ℤ))) •\n"
        "          actualFixedPhaseCuspHorocyclePoint kappa Y x) =\n"
        "      (inverseEtaPaperOrbitMultiplier GammaTwo n).factor\n"
        "          (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x) *\n"
        "        ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x)\n"
        "  simpa only [FixedPhaseDifferentialWord.targetIndex_nil,\n"
        "    FixedPhaseDifferentialWord.eval_nil_apply,\n"
        "    InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using\n"
        "    (u.2 FixedPhaseDifferentialWord.nil)\n"
        "      (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "      (actualFixedPhaseCuspHorocyclePoint kappa Y x)\n",
        (Header(41368, 2, "Type mismatch: After simplification"),),
        "Expose the exact SL(2,Z) action and zeroth-word covariance statement before applying the stored core property.",
        "The same three nil-word normalization lemmas are used by the FA covariance proof at its exact lines 17653-17672.",
    ),
    Rule(
        "cusp_curve_contdiff_apply_division_producer",
        "  simp only [actualFixedPhaseCuspHorocyclePoint,\n"
        "    actualFixedPhaseHorizontalHorocyclePoint,\n"
        "    UpperHalfPlane.coe_specialLinearGroup_apply]\n"
        "  fun_prop (disch := exact hden _)\n",
        "  simp only [actualFixedPhaseCuspHorocyclePoint,\n"
        "    actualFixedPhaseHorizontalHorocyclePoint,\n"
        "    UpperHalfPlane.coe_specialLinearGroup_apply]\n"
        "  apply ContDiff.div\n"
        "  · fun_prop\n"
        "  · fun_prop\n"
        "  · exact hden\n",
        (Header(41423, 2, "`fun_prop` was unable to prove"),),
        "Apply the local ContDiff.div API explicitly, leaving fun_prop only the polynomial numerator and denominator subgoals.",
        "Exact P10 line 45482 demonstrates the same ContDiff.div producer with a pointwise nonzero denominator proof.",
    ),
    Rule(
        "cusp_trace_contdiff_change_coercion_function",
        "  simpa [actualFixedPhaseNamedCuspTraceRepresentative,\n"
        "    upperLift, Function.comp_def] using hcomp\n",
        "  change ContDiff ℝ ∞\n"
        "    (fun x : ℝ =>\n"
        "      (u : SmoothQuotientCompactFunction)\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x))\n"
        "  exact hcomp\n",
        (Header(41440, 2, "Type mismatch: After simplification"),),
        "Change the named trace to the exact coercion-level function already proved ContDiff by comp_contDiff.",
        "The diagnostic prints hcomp with precisely this pointwise SmoothQuotientCompactFunction evaluation.",
    ),
    Rule(
        "smooth_boundary_reuse_certified_cusp_curve_contdiff",
        "theorem actualFixedPhaseNamedCuspAmbientCoordinate_contDiff\n"
        "    (kappa : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoCusp) (Y : ℝ) :\n"
        "    ContDiff ℝ ∞\n"
        "      (actualFixedPhaseNamedCuspAmbientCoordinate kappa Y) := by\n"
        "  let sigma : SL(2, ℤ) := Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspScaling kappa\n"
        "  have hden : ∀ x : ℝ,\n"
        "      ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *\n"
        "          (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +\n"
        "        (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) ≠ 0 := by\n"
        "    intro x\n"
        "    simpa [UpperHalfPlane.denom, sigma] using\n"
        "      (UpperHalfPlane.denom_ne_zero\n"
        "        ((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspScaling kappa : SL(2, ℤ)) : GL (Fin 2) ℝ)\n"
        "        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseHorizontalHorocyclePoint Y x))\n"
        "  simp only [actualFixedPhaseNamedCuspAmbientCoordinate,\n"
        "    QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint,\n"
        "    QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseHorizontalHorocyclePoint,\n"
        "    UpperHalfPlane.coe_specialLinearGroup_apply]\n"
        "  fun_prop (disch := exact hden _)\n",
        "theorem actualFixedPhaseNamedCuspAmbientCoordinate_contDiff\n"
        "    (kappa : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoCusp) (Y : ℝ) :\n"
        "    ContDiff ℝ ∞\n"
        "      (actualFixedPhaseNamedCuspAmbientCoordinate kappa Y) := by\n"
        "  change ContDiff ℝ ∞\n"
        "    (fun x : ℝ =>\n"
        "      ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint\n"
        "        kappa Y x : ℍ) : ℂ))\n"
        "  exact\n"
        "    QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint_coe_contDiff\n"
        "      kappa Y\n",
        (Header(42354, 2, "`simp` made no progress"),),
        "Reuse the already certified identical ambient cusp curve instead of duplicating its rational-map proof.",
        "The local ambient-coordinate definition is definitionally the complex coercion proved ContDiff at exact P10 line 41330.",
    ),
    Rule(
        "polygon_edge_pairing_move_pointwise_scope_before_doc",
        "/-- The transported pairing carries the whole labelled edge onto its paired\n"
        "labelled edge. -/\n"
        "open scoped Pointwise in\n"
        "theorem polygonEdge_pairing_set (e : PolygonEdge) :\n"
        "    ((e.pairingElement : SL(2, ℤ)) • polygonEdgeSet e : Set ℍ) =\n"
        "      polygonEdgeSet e.paired := by\n"
        "  exact gammaTwoActualPolygonEdgePairing_set e\n",
        "open scoped Pointwise\n"
        "\n"
        "/-- The transported pairing carries the whole labelled edge onto its paired\n"
        "labelled edge. -/\n"
        "theorem polygonEdge_pairing_set (e : PolygonEdge) :\n"
        "    ((e.pairingElement : SL(2, ℤ)) • polygonEdgeSet e : Set ℍ) =\n"
        "      polygonEdgeSet e.paired := by\n"
        "  exact gammaTwoActualPolygonEdgePairing_set e\n",
        (Header(34075, 17, "unexpected token 'open'; expected 'lemma'"),),
        "Move the Pointwise scope command before the declaration doc comment so the doc comment remains attached directly to the theorem declaration.",
        "Lean reports the scope command itself where the doc-comment parser expects the documented declaration; Pointwise is already used globally in the exit-zero FA producer.",
    ),
    Rule(
        "smooth_compact_covariance_bridge_gamma_two_action",
        "theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace\n"
        "    {k : ℤ} {M : HalfIntegralMultiplier GammaTwo k}\n"
        "    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore M) :\n"
        "    HasMultiplierMatchedPolygonTrace M\n"
        "      (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.toSection u) := by\n"
        "  apply hasMultiplierMatchedPolygonTrace_of_covariance M\n"
        "    (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.toSection u)\n"
        "  intro γ z\n"
        "  simpa only using\n"
        "    (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.covariance u γ z)\n",
        "theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace\n"
        "    {k : ℤ} {M : HalfIntegralMultiplier GammaTwo k}\n"
        "    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore M) :\n"
        "    HasMultiplierMatchedPolygonTrace M\n"
        "      (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.toSection u) := by\n"
        "  apply hasMultiplierMatchedPolygonTrace_of_covariance M\n"
        "    (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.toSection u)\n"
        "  intro γ z\n"
        "  have hCov :=\n"
        "    Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.covariance u γ z\n"
        "  rw [← Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov\n"
        "  rw [show\n"
        "    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoToSL2Real γ • z =\n"
        "      Matrix.SpecialLinearGroup.toGL\n"
        "        (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoToSL2Real γ) • z by rfl] at hCov\n"
        "  simpa only [Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoToSL2Real] using hCov\n",
        (Header(34171, 2, "Type mismatch: After simplification"),),
        "Bridge the stored GammaTwo action to the explicit special-linear action expected by the polygon-trace covariance interface.",
        "The exit-zero Mock2_FunctionalAnalysis producer uses the same gammaTwoToSL2Real_smul bridge and toGL normalization at lines 20616-20625 and 22353-22361.",
    ),
    Rule(
        "twisted_difference_zero_expose_pi_zero_function",
        "  · simp [widthTwoTwistedDifferenceQuotient, hp,\n"
        "      widthTwoTwistedIncrement_zero]\n",
        "  · simp [widthTwoTwistedDifferenceQuotient, hp]\n"
        "    change widthTwoTwistedIncrement tau\n"
        "      (fun _ : ℝ => (0 : ℂ)) p.1 p.2 = 0\n"
        "    exact widthTwoTwistedIncrement_zero tau p.1 p.2\n",
        (Header(40646, 2, "unsolved goals"),),
        "Expose the Pi zero function explicitly after the distance branch simplification, then apply the already-proved zero-increment producer.",
        "The exact residual Probe11 goal differs from widthTwoTwistedIncrement_zero only by the opaque Pi zero notation.",
    ),
)


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("probe11_early_frontier", "qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py", "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a"),
    ("probe11_mid", "qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py", "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6"),
    ("probe11_tail", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("probe11_earlymid", "qym-probe11-earlymid-p10-conditional/qym_probe11_earlymid_p10_conditional.py", "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6"),
    ("probe11_40k", "qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py", "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052"),
    ("probe11_structural50", "qym-probe11-50k-structural-p10/qym_probe11_50k_structural_p10.py", "82189532a76f4785734d851f459a67c2dc04e373d1fc70eb5a137506f2dc57ae"),
    ("probe12_refinement", "qym-probe12-p10-midlate-refinement/qym_probe12_p10_midlate_refinement.py", "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d"),
    ("probe12_43k49k_p11", "qym-probe12-43k49k-p11-conditional/qym_probe12_43k49k_p11_conditional.py", "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523"),
    ("probe12_52k61k_p11", "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py", "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795"),
)


DECLARED_REFINEMENTS: dict[str, tuple[str, str]] = {
    "polygon_edge_pairing_move_pointwise_scope_before_doc": (
        "probe12_refinement",
        "polygon_edge_pairing_set_open_pointwise_refinement",
    ),
    "smooth_compact_covariance_bridge_gamma_two_action": (
        "probe12_refinement",
        "smooth_compact_weight_core_namespace_accessor_refinement",
    ),
    "twisted_difference_zero_expose_pi_zero_function": (
        "probe11_mid",
        "twisted_difference_zero_split_distance_and_use_increment_zero",
    ),
}

# The covariance refinement consumes its owner rule's complete active new
# anchor.  The Pointwise and zero refinements consume strict spans inside their
# owners' larger anchors, so those are overlaps without whole-anchor equality.
DECLARED_EXACT_EQUALITIES = frozenset(
    {
        "smooth_compact_covariance_bridge_gamma_two_action",
    }
)

DECLARED_OVERLAP_VARIANTS: dict[str, frozenset[str]] = {
    "polygon_edge_pairing_move_pointwise_scope_before_doc": frozenset(
        {"old", "new"}
    ),
    "smooth_compact_covariance_bridge_gamma_two_action": frozenset({"new"}),
    "twisted_difference_zero_expose_pi_zero_function": frozenset({"new"}),
}

DECLARED_INVERSE_OVERLAP_VARIANTS: dict[str, frozenset[str]] = {
    "polygon_edge_pairing_move_pointwise_scope_before_doc": frozenset({"old"}),
    "smooth_compact_covariance_bridge_gamma_two_action": frozenset(),
    "twisted_difference_zero_expose_pi_zero_function": frozenset(),
}


EXCLUDED: tuple[dict[str, object], ...] = (
    {
        "lines": [37101, 37312],
        "kind": "canonical_trace_structural_cascade",
        "reason": "owned or downstream of the canonical trace-class/core timeout and unknown-constant cluster",
    },
    {
        "lines": [37526],
        "kind": "deferred_active_rule_api_refinement",
        "reason": "the active Probe11 map-eq-bottom repair still misses an explicit subgroup argument; deferred under the three-new-root cap",
    },
    {
        "lines": [37725],
        "kind": "multi_branch_modular_arithmetic_blocker",
        "reason": "ten noncentral stabilizer alternatives remain and no single exact local contradiction producer is established",
    },
    {
        "lines": [41305],
        "kind": "continuousAt_composition_api_blocker",
        "reason": "both prior one-stage comp call shapes failed; the required two-stage coercion and curve composition was not Lean-validated",
    },
    {
        "lines": [40657, 40668],
        "kind": "deferred_active_pi_function_refinements",
        "reason": "the add and smul variants remain exact direct roots but were deferred to preserve the three-new-root cap after explicit 34k ownership was assigned",
    },
    {
        "lines": [41962],
        "kind": "deep_typeclass_timeout_blocker",
        "reason": "ambient WithLp/product/submodule InnerProductSpace synthesis times out; no exact explicit instance constructor was validated statically",
    },
    {
        "lines": [42162, 42181],
        "kind": "completion_core_timeout_cascade",
        "reason": "timeout followed by unknown generated core constant; not an independent local producer",
    },
    {
        "lines": [42744, 42856, 42864, 42867, 42875, 42888, 42892],
        "kind": "quotient_loop_action_instance_and_calc_blocker",
        "reason": "the typed SL2 homeomorphism still lacks ContinuousConstSMul and the subsequent quotient calc requires an unverified action bridge",
    },
)


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "cr": b"\r" in raw,
        "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": raw.endswith(b"\n"),
    }


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def input_expected() -> dict[str, object]:
    return {
        "sha256": INPUT_SHA256,
        "git_blob": INPUT_GIT_BLOB,
        "bytes": INPUT_BYTES,
        "lf": INPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def output_expected() -> dict[str, object]:
    return {
        "sha256": OUTPUT_SHA256,
        "git_blob": OUTPUT_GIT_BLOB,
        "bytes": OUTPUT_BYTES,
        "lf": OUTPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def sentinels_unsealed() -> bool:
    return OUTPUT_SHA256 == "" and OUTPUT_GIT_BLOB == "" and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], *, unsealed: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if unsealed else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes) -> list[dict[str, object]]:
    for label, actual, expected in (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(header_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    ):
        if actual != expected:
            raise RuntimeError(f"Probe11 {label} identity mismatch: {actual}")
    header_lines = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    if len(header_lines) != 217:
        raise RuntimeError(f"expected 217 exact error headers, got {len(header_lines)}")
    if sum(row.get("severity") == "error" for row in rows) != 217:
        raise RuntimeError("diagnostic error count is not 217")
    if sum(row.get("severity") == "warning" for row in rows) != 350:
        raise RuntimeError("diagnostic warning count is not 350")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error{code}: {re.escape(header.message)}"
            )
            hm = [line for line in header_lines if pattern.match(line)]
            dm = [
                row
                for row in rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append(
                {
                    "rule": rule.label,
                    **header.__dict__,
                    "kind": (
                        "declared_active_probe11_rule_refinement"
                        if rule.label in DECLARED_REFINEMENTS
                        else "surviving_exact_probe10_direct_root_reanchored_to_probe11"
                    ),
                }
            )
    return mapped


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        found = text.find(needle, start)
        if found < 0:
            return result
        result.append((found, found + len(needle)))
        start = found + 1


def load_foreign(name: str, relative: str, expected_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parent.parent / relative
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"foreign helper identity mismatch: {name}")
    module_name = "_qym_36k42k_foreign_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def audit_collisions(text: str, *, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: active anchor count {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 34000 <= line <= 42999:
                raise RuntimeError(f"{rule.label}: scope violation at line {line}")
            own.append((start, end, rule.label))
    own_sorted = sorted(own)
    own_overlaps: list[dict[str, object]] = []
    for left, right in zip(own_sorted, own_sorted[1:]):
        if left[1] > right[0]:
            own_overlaps.append({"left": left[2], "right": right[2]})
    equalities: list[dict[str, str]] = []
    overlaps: list[dict[str, object]] = []
    foreign_active_spans = 0
    identities: dict[str, str] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        for foreign in foreign_rules:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                foreign_active_spans += len(found)
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            equalities.append(
                                {
                                    "own": own_rule.label,
                                    "own_variant": own_variant,
                                    "foreign": f"{name}:{foreign.label}",
                                    "foreign_variant": variant,
                                }
                            )
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            overlaps.append(
                                {
                                    "own": own_label,
                                    "foreign": f"{name}:{foreign.label}",
                                    "foreign_variant": variant,
                                    "own_span": [ostart, oend],
                                    "foreign_span": [fstart, fend],
                                }
                            )
    expected_equalities = {
        (own, "old", f"{owner_name}:{owner_rule}", "new")
        for own, (owner_name, owner_rule) in DECLARED_REFINEMENTS.items()
        if own in DECLARED_EXACT_EQUALITIES
    }
    actual_equalities = {
        (
            item["own"],
            item["own_variant"],
            item["foreign"],
            item["foreign_variant"],
        )
        for item in equalities
    }
    undeclared_equalities = actual_equalities - expected_equalities
    missing_equalities = expected_equalities - actual_equalities
    expected_overlaps = {
        (own, f"{owner_name}:{owner_rule}", variant)
        for own, (owner_name, owner_rule) in DECLARED_REFINEMENTS.items()
        for variant in (
            DECLARED_INVERSE_OVERLAP_VARIANTS[own]
            if inverse
            else DECLARED_OVERLAP_VARIANTS[own]
        )
    }
    actual_overlaps = {
        (item["own"], item["foreign"], item["foreign_variant"])
        for item in overlaps
    }
    undeclared_overlaps = actual_overlaps - expected_overlaps
    missing_overlaps = expected_overlaps - actual_overlaps
    if (
        own_overlaps
        or undeclared_equalities
        or missing_equalities
        or undeclared_overlaps
        or missing_overlaps
    ):
        raise RuntimeError(
            "collision contract mismatch: "
            f"own={own_overlaps}, "
            f"undeclared_equalities={sorted(undeclared_equalities)}, "
            f"missing_equalities={sorted(missing_equalities)}, "
            f"undeclared_overlaps={sorted(undeclared_overlaps)}, "
            f"missing_overlaps={sorted(missing_overlaps)}"
        )
    return {
        "foreign_helper_sha256": identities,
        "own_spans_checked": len(own),
        "foreign_active_spans_checked": foreign_active_spans,
        "own_span_overlaps": own_overlaps,
        "declared_exact_anchor_equalities": equalities,
        "declared_foreign_span_overlaps": overlaps,
        "declared_refinements": {
            label: {
                "foreign_helper": owner[0],
                "foreign_rule": owner[1],
                "exact_anchor_equality": label in DECLARED_EXACT_EQUALITIES,
                "overlap_variants": sorted(DECLARED_OVERLAP_VARIANTS[label]),
                "inverse_overlap_variants": sorted(
                    DECLARED_INVERSE_OVERLAP_VARIANTS[label]
                ),
            }
            for label, owner in DECLARED_REFINEMENTS.items()
        },
        "undeclared_exact_anchor_equalities": [],
        "undeclared_foreign_span_overlaps": [],
    }


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}")
        text = text.replace(old, new)
        audits.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
                "precedent": rule.precedent,
                "declared_refinement": (
                    {
                        "foreign_helper": DECLARED_REFINEMENTS[rule.label][0],
                        "foreign_rule": DECLARED_REFINEMENTS[rule.label][1],
                    }
                    if rule.label in DECLARED_REFINEMENTS
                    else None
                ),
            }
        )
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe11-log", type=Path, required=True)
    parser.add_argument("--probe11-error-headers", type=Path, required=True)
    parser.add_argument("--probe11-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal and not sentinels_unsealed():
        raise RuntimeError("bootstrap refused: output identity already sealed")
    if not args.bootstrap_seal and sentinels_unsealed():
        raise RuntimeError("output identity unsealed")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        output_expected() if inverse else input_expected(),
        unsealed=args.bootstrap_seal and inverse,
    )
    mapped = verify_authority(
        args.probe11_log.read_bytes(),
        args.probe11_error_headers.read_bytes(),
        args.probe11_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    collision = audit_collisions(source_text, inverse=inverse)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        input_expected() if inverse else output_expected(),
        unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored, _ = apply_rules(result_text, inverse=not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE11_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 217,
            "warnings": 350,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [34000, 42999],
            "explicit_early_owner_lines": [34075, 34171],
            "independent_direct_roots_only": True,
            "declared_active_probe11_refinements": len(DECLARED_REFINEMENTS),
            "undeclared_foreign_helper_span_overlap": False,
            "cascade_diagnostics_selected": False,
            "excluded": EXCLUDED,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(mapped),
        "selected_exact_probe11_lines": sorted({header.line for rule in RULES for header in rule.headers}),
        "diagnostic_map": mapped,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
