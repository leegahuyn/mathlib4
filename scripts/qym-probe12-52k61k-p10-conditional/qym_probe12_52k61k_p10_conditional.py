#!/usr/bin/env python3
"""Conditional direct-root repairs for exact terminal-Probe10 lines 52000-61999.

The selected rules are local API, coercion, simplifier-exposure, or parser-
stable proof repairs.  The unresolved integral rewrite at 53091 and the
CoordinateL2 normed-space instance mismatch at 58816 are deliberately
excluded.  This transformer is byte-locked, exact-counted, reversible,
trust0, collision-audited against all 60 active Probe11 rules and the two
frozen sibling Probe12 helpers, and activation-disabled.  It never invokes
Lean, Lake, Git, the network, or a remote service.
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

SCHEMA = "qym-probe12-52k61k-p10-conditional-v1-exact-terminal-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "77c39481adea58a2e046aec56f6573d66a4efbb8e599fa5512cf46fabfda9d09"
OUTPUT_GIT_BLOB = "6a2462d46cc8ff72f91bedb28607de9291ee91f9"
OUTPUT_BYTES = 2_924_920
OUTPUT_LF = 61_810


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
        "sector_potential_symmetry_use_generic_inner_smul",
        "  rw [actualStageSectorDiscriminantPotentialOperator_apply,\n"
        "    actualStageSectorDiscriminantPotentialOperator_apply,\n"
        "    InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "    InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ),\n"
        "    actualStageDiscriminantPotentialOperator_inner_symmetric Y u v]\n",
        "  rw [actualStageSectorDiscriminantPotentialOperator_apply,\n"
        "    actualStageSectorDiscriminantPotentialOperator_apply,\n"
        "    inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "    Complex.star_def, Complex.conj_ofReal,\n"
        "    actualStageDiscriminantPotentialOperator_inner_symmetric Y u v]\n",
        (Header(53318, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Use the generic complex inner-product smul API, then normalize the real scalar's specialized Complex star.",
        "Exact P10 line 58531 reaches the same generic inner_smul normal form; its only failure is the unpinned generic real-conjugation lemma.",
    ),
    Rule(
        "sqrt_lower_bound_square_without_recursive_reverse_rw",
        "    actualStageDiscriminantPotentialLowerBound Y * ‖u‖ ^ 2 =\n"
        "        (Real.sqrt (actualStageDiscriminantPotentialLowerBound Y) * ‖u‖) *\n"
        "          (Real.sqrt (actualStageDiscriminantPotentialLowerBound Y) * ‖u‖) := by\n"
        "      rw [← Real.mul_self_sqrt\n"
        "        (actualStageDiscriminantPotentialLowerBound_pos Y).le]\n"
        "      ring\n",
        "    actualStageDiscriminantPotentialLowerBound Y * ‖u‖ ^ 2 =\n"
        "        (Real.sqrt (actualStageDiscriminantPotentialLowerBound Y) * ‖u‖) *\n"
        "          (Real.sqrt (actualStageDiscriminantPotentialLowerBound Y) * ‖u‖) := by\n"
        "      calc\n"
        "        actualStageDiscriminantPotentialLowerBound Y * ‖u‖ ^ 2 =\n"
        "            (Real.sqrt (actualStageDiscriminantPotentialLowerBound Y)) ^ 2 * ‖u‖ ^ 2 := by\n"
        "          rw [Real.sq_sqrt\n"
        "            (actualStageDiscriminantPotentialLowerBound_pos Y).le]\n"
        "        _ = (Real.sqrt (actualStageDiscriminantPotentialLowerBound Y) * ‖u‖) *\n"
        "              (Real.sqrt (actualStageDiscriminantPotentialLowerBound Y) * ‖u‖) := by\n"
        "          ring\n",
        (Header(54308, 78, "unsolved goals"),),
        "Rewrite the square on the right forward with sq_sqrt, then discharge only the polynomial rearrangement by ring.",
        "The exact residual comes from reverse rewriting every matching lower-bound occurrence, including occurrences beneath square roots.",
    ),
    Rule(
        "sector_sqrt_symmetry_use_generic_inner_smul",
        "  rw [actualStageSectorDiscriminantSqrtOperator_apply,\n"
        "    actualStageSectorDiscriminantSqrtOperator_apply,\n"
        "    InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "    InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ),\n"
        "    actualStageDiscriminantSqrtOperator_inner_symmetric Y u v]\n",
        "  rw [actualStageSectorDiscriminantSqrtOperator_apply,\n"
        "    actualStageSectorDiscriminantSqrtOperator_apply,\n"
        "    inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "    Complex.star_def, Complex.conj_ofReal,\n"
        "    actualStageDiscriminantSqrtOperator_inner_symmetric Y u v]\n",
        (Header(54563, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Use the generic complex inner_smul laws for the already complex-coerced square-root coefficient.",
        "This is the square-root analogue of the exact direct root at P10 line 53318.",
    ),
    Rule(
        "l2_delta_family_beta_reduce_both_types",
        "  simpa only [actualStageL2DeltaFamily, Function.comp_apply] using hMapped\n",
        "  change LinearIndependent ℂ\n"
        "    (fun i : Fin n =>\n"
        "      QYM.FullCertification.P4ActualStageContinuousDensityExtension.actualStageContinuousToL2 Y\n"
        "        (actualStageDeltaComplex q hY n i))\n"
        "  change LinearIndependent ℂ\n"
        "    (fun i : Fin n =>\n"
        "      QYM.FullCertification.P4ActualStageContinuousDensityExtension.actualStageContinuousToL2 Y\n"
        "        (actualStageDeltaComplex q hY n i)) at hMapped\n"
        "  exact hMapped\n",
        (Header(55033, 2, "Type mismatch: After simplification, term"),),
        "Put the named family goal and map' witness into the same explicit pointwise lambda normal form.",
        "The exact diagnostic differs only by the named family versus the coercion-composition presentation.",
    ),
    Rule(
        "off_test_witness_change_to_p4_complement",
        "  simpa only [actualInverseEtaOffTestWitness,\n"
        "    QYM.FullCertification.P12ActualInverseEtaTestOperatorExtension.actualInverseEtaTestVector] using\n"
        "    QYM.FullCertification.P4ActualStageNonconstantCoreExtension.actualStageSeparatingOrthogonalL2_mem_complement q hY\n",
        "  change\n"
        "    QYM.FullCertification.P4ActualStageNonconstantCoreExtension.actualStageSeparatingOrthogonalL2 q hY ∈\n"
        "      QYM.FullCertification.P4ActualStageNonconstantCoreExtension.ActualStageDistinguishedComplement Y\n"
        "  exact\n"
        "    QYM.FullCertification.P4ActualStageNonconstantCoreExtension.actualStageSeparatingOrthogonalL2_mem_complement q hY\n",
        (Header(55850, 2, "Type mismatch: After simplification, term"),),
        "Expose the definitionally identical P4 carrier, distinguished line, and orthogonal complement before applying its membership theorem.",
        "Both test-space aliases reduce to the P3 actual-stage carrier and both complements span the same distinguished inverse-eta section.",
    ),
    Rule(
        "projection_hamiltonian_inner_self_close_cast_power",
        "    _ = ((‖actualInverseEtaProjectionHamiltonian hY u‖ ^ 2 : ℝ) : ℂ) := by\n"
        "      rw [inner_self_eq_norm_sq_to_K]\n",
        "    _ = ((‖actualInverseEtaProjectionHamiltonian hY u‖ ^ 2 : ℝ) : ℂ) := by\n"
        "      rw [inner_self_eq_norm_sq_to_K]\n"
        "      norm_cast\n",
        (Header(56381, 72, "unsolved goals"),),
        "Close the exact cast-versus-power residual with norm_cast after the standard inner-self identity.",
        "The P10 residual is precisely (norm : Complex)^2 = ((norm^2 : Real) : Complex).",
    ),
    Rule(
        "off_test_inner_self_close_cast_power",
        "  rw [actualInverseEtaProjectionHamiltonian_eq_self_of_mem_offTest hY hu,\n"
        "    inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]\n",
        "  rw [actualInverseEtaProjectionHamiltonian_eq_self_of_mem_offTest hY hu,\n"
        "    inner_self_eq_norm_sq_to_K]\n"
        "  norm_cast\n",
        (Header(56407, 29, "unsolved goals"),),
        "Let norm_cast normalize the two syntactically different real-to-complex power presentations.",
        "The exact P10 residual prints equal mathematical terms with the cast placed on opposite sides of the exponentiation.",
    ),
    Rule(
        "projection_absorb_left_simp_indicator_branches",
        "  by_cases hxm : x ∈ naturalStageSet m\n"
        "  · have hxn : x ∈ naturalStageSet n :=\n"
        "      naturalStageSet_monotone hmn hxm\n"
        "    rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hxm, hinner,\n"
        "      globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hxn]\n"
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hxm, Set.indicator_of_notMem hxm]\n",
        "  by_cases hxm : x ∈ naturalStageSet m\n"
        "  · have hxn : x ∈ naturalStageSet n :=\n"
        "      naturalStageSet_monotone hmn hxm\n"
        "    simp only [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hxm, Set.indicator_of_mem hxn, hinner]\n"
        "  · simp only [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hxm]\n",
        (
            Header(57164, 2, "unsolved goals"),
            Header(57171, 35, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
        ),
        "Simplify the representative definition in both branches so the inner ae equality is used before the outer representative disappears.",
        "The positive residual is the direct representative at m and the negative residual is zero equals that same indicator.",
    ),
    Rule(
        "projection_error_bound_preserve_natural_stage_name",
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity, naturalStageSet,\n"
        "      globalStageProjectionRepresentative, hx]\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity, naturalStageSet,\n"
        "      globalStageProjectionRepresentative, hx]\n",
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n",
        (
            Header(57309, 2, "unsolved goals"),
            Header(57312, 2, "unsolved goals"),
        ),
        "Keep naturalStageSet opaque long enough for hx to simplify its indicator in both branches.",
        "The P10 unused-simp warning confirms that prematurely unfolding naturalStageSet prevents hx from matching the XSet indicator.",
    ),
    Rule(
        "projection_error_eventually_zero_preserve_stage_name",
        "  filter_upwards [eventually_mem_naturalStageSet x] with n hn\n"
        "  simp [globalStageProjectionErrorDensity, naturalStageSet,\n"
        "    globalStageProjectionRepresentative, hn]\n",
        "  filter_upwards [eventually_mem_naturalStageSet x] with n hn\n"
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hn]\n",
        (Header(57334, 66, "unsolved goals"),),
        "Preserve the named exhaustion set until hn reduces the representative indicator.",
        "The exact residual and unused-simp warning are the single-branch form of the P10 lines 57309/57312 producer.",
    ),
    Rule(
        "projection_error_pointwise_tendsto_preserve_stage_name",
        "  simp [globalStageProjectionErrorDensity, naturalStageSet,\n"
        "    globalStageProjectionRepresentative, hx]\n",
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hx]\n",
        (Header(57343, 21, "unsolved goals"),),
        "Preserve naturalStageSet until the monotonicity-derived hx can simplify the indicator.",
        "This is the same exact producer as the neighboring eventually-zero theorem, with hx obtained from monotonicity.",
    ),
    Rule(
        "covariant_derivative_symmetry_transport_ground_equality",
        "  rw [covariantDerivative_apply, covariantDerivative_apply,\n"
        "    inner_sub_left, inner_sub_right]\n"
        "  rw [groundProjection_isSymmetric u v]\n",
        "  rw [covariantDerivative_apply, covariantDerivative_apply,\n"
        "    inner_sub_left, inner_sub_right]\n"
        "  exact congrArg (fun z : ℂ => inner ℂ u v - z)\n"
        "    (groundProjection_isSymmetric u v)\n",
        (Header(58437, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Transport the symmetric projection equality through subtraction instead of relying on rewrite's coercion-sensitive pattern.",
        "The exact residual is A-B=A-C and groundProjection_isSymmetric proves B=C.",
    ),
    Rule(
        "potential_symmetry_pin_complex_real_conjugation",
        "  rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "    RCLike.star_def, RCLike.conj_ofReal,\n"
        "    groundProjection_isSymmetric u v]\n",
        "  rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "    Complex.star_def, Complex.conj_ofReal,\n"
        "    groundProjection_isSymmetric u v]\n",
        (Header(58532, 21, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Pin both star normalization and real conjugation to Complex for the concrete quarter coefficient.",
        "The exact target contains starRingEnd Complex applied to a real cast; only the generic RCLike conjugation step fails.",
    ),
    Rule(
        "coordinate_hamiltonian_symmetry_transport_two_equalities",
        "  rw [coordinateHamiltonian_apply, coordinateHamiltonian_apply,\n"
        "    inner_add_left, inner_add_right]\n"
        "  rw [covariantDerivative_isSymmetric u v, potential_isSymmetric u v]\n",
        "  rw [coordinateHamiltonian_apply, coordinateHamiltonian_apply,\n"
        "    inner_add_left, inner_add_right]\n"
        "  exact congrArg₂ (fun a b : ℂ => a + b)\n"
        "    (covariantDerivative_isSymmetric u v)\n"
        "    (potential_isSymmetric u v)\n",
        (Header(58557, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Transport the two component symmetry equalities through addition without coercion-sensitive rewriting.",
        "The exact residual is A+B=C+D and the two named symmetry theorems prove A=C and B=D.",
    ),
    Rule(
        "hamiltonian_form_hermitian_pin_complex_conjugation",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    coordinateHamiltonianForm_apply, RCLike.star_def, map_add, map_mul,\n"
        "    starRingEnd_apply, RCLike.star_def, RCLike.conj_ofReal]\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    coordinateHamiltonianForm_apply, Complex.star_def, map_add, map_mul,\n"
        "    starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]\n",
        (Header(58684, 40, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Normalize the outer star before map_add/map_mul and pin the real quarter conjugation to Complex.",
        "The exact P10 residual is fully concrete over Complex; the failure occurs only at the unpinned generic conjugation lemma.",
    ),
    Rule(
        "hamiltonian_form_representation_pin_complex_conjugation",
        "  rw [coordinateHamiltonianForm_apply, coordinateHamiltonian_apply,\n"
        "    inner_add_left, potential_apply, inner_smul_left,\n"
        "    starRingEnd_apply, RCLike.star_def, RCLike.conj_ofReal]\n",
        "  rw [coordinateHamiltonianForm_apply, coordinateHamiltonian_apply,\n"
        "    inner_add_left, potential_apply, inner_smul_left,\n"
        "    starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]\n",
        (Header(58698, 40, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Pin the star and real-conjugation normalization to the concrete Complex scalar field.",
        "The exact P10 residual again contains starRingEnd Complex on the real quarter cast.",
    ),
    Rule(
        "hamiltonian_form_re_self_drop_redundant_final_simp",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n"
        "  simp only [Complex.ofReal_re]\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n",
        (Header(58720, 2, "`simp` made no progress"),),
        "Remove the tactic executed after the preceding simp has already closed the goal.",
        "Lean reports made-no-progress at the final line rather than an open goal from the preceding simp.",
    ),
    Rule(
        "negative_one_left_inverse_expand_nested_projection_map",
        "  rw [actualCutoffNegativeOneResolvent_apply,\n"
        "    actualCutoffNegativeOneShift_apply,\n"
        "    actualCutoffEscapeHamiltonian_apply, map_sub, map_neg,\n"
        "    QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "    QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "    QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjection_idempotent]\n"
        "  module\n",
        "  have hIdempotent :\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n\n"
        "          (QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n u) =\n"
        "        QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n u := by\n"
        "    rw [QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjection_idempotent]\n"
        "  rw [actualCutoffNegativeOneResolvent_apply,\n"
        "    actualCutoffNegativeOneShift_apply,\n"
        "    actualCutoffEscapeHamiltonian_apply, map_sub, map_neg, map_sub,\n"
        "    hIdempotent]\n"
        "  module\n",
        (Header(59492, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expand both nested continuous-linear-map subtractions before using an explicitly typed CLM idempotence fact.",
        "Exact P10 line 59642 proves the same CLM idempotence fact; the residual at 59492 still contains P(u-Pu), so direct bare-map idempotence cannot match.",
    ),
    Rule(
        "negative_one_resolvent_tendsto_beta_reduce_composition",
        "  have hScaled :=\n"
        "    ((continuous_const_smul (-(1 / 2 : ℂ))).tendsto (u + u)).comp hSum\n"
        "  have hScaleLimit : (-(1 / 2 : ℂ)) • (u + u) = -u := by\n",
        "  have hScaled :=\n"
        "    ((continuous_const_smul (-(1 / 2 : ℂ))).tendsto (u + u)).comp hSum\n"
        "  change Tendsto\n"
        "    (fun n => (-(1 / 2 : ℂ)) •\n"
        "      (u + QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n u))\n"
        "    atTop (𝓝 (-(1 / 2 : ℂ) • (u + u))) at hScaled\n"
        "  have hScaleLimit : (-(1 / 2 : ℂ)) • (u + u) = -u := by\n",
        (Header(59587, 2, "Type mismatch: After simplification, term"),),
        "Beta-reduce the composed Tendsto witness at its hypothesis before rewriting the named resolvent.",
        "The exact diagnostic differs only between a composed function and its pointwise lambda.",
    ),
    Rule(
        "ground_range_reverse_use_sub_eq_self",
        "    refine ⟨u, ?_⟩\n"
        "    change actualCutoffEscapeHamiltonian n u = u\n"
        "    rw [actualCutoffEscapeHamiltonian_apply, hu, sub_zero]\n",
        "    refine ⟨u, ?_⟩\n"
        "    change u -\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n u = u\n"
        "    exact sub_eq_self.mpr hu\n",
        (Header(59654, 45, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Use the additive-group equivalence sub_eq_self directly on the already typed kernel equality.",
        "The exact P10 context prints hu as precisely the projection value equals zero needed by sub_eq_self.",
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
    ("probe12_36k42k", "qym-probe12-36k42k-p10-conditional/qym_probe12_36k42k_p10_conditional.py", "9c3df7c522538373943cde18e2a788a4fc7feec5412724e37ccfb6a508865095"),
    ("probe12_43k49k", "qym-probe12-43k49k-p10-conditional/qym_probe12_43k49k_p10_conditional.py", "5cea81a9deb981609655d767487a3cbb5fda032849869902ba074d8729fa976d"),
)


EXCLUDED: tuple[dict[str, object], ...] = (
    {
        "lines": [52887, 52902, 52996, 53036, 53043, 53049, 53055, 53965, 53980, 54076, 55342, 56327, 56827, 56960, 56979, 57072],
        "kind": "owned_by_frozen_probe11_helpers_or_cascades",
        "reason": "excluded by exact foreign-rule span and ownership contract",
    },
    {
        "lines": [53091],
        "kind": "integral_rewrite_binder_blocker",
        "reason": "the apparently matching integral_re theorem does not rewrite the coercion-heavy integrand; no exact local bridge was established statically",
    },
    {
        "lines": [58816],
        "kind": "normed_space_instance_coherence_blocker",
        "reason": "HasCompactResolventAt is built with PiLp.innerProductSpace.toNormedSpace but the target uses PiLp.normedSpace; no principled local instance equality was validated",
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


def expected_input() -> dict[str, object]:
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB, "bytes": INPUT_BYTES,
            "lf": INPUT_LF, "cr": False, "nul": False, "bom": False, "terminal_lf": True}


def expected_output() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB, "bytes": OUTPUT_BYTES,
            "lf": OUTPUT_LF, "cr": False, "nul": False, "bom": False, "terminal_lf": True}


def unsealed() -> bool:
    return OUTPUT_SHA256 == "" and OUTPUT_GIT_BLOB == "" and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], *, bootstrap: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if bootstrap else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes) -> list[dict[str, object]]:
    for label, actual, expected in (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(header_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    ):
        if actual != expected:
            raise RuntimeError(f"Probe10 {label} identity mismatch: {actual}")
    header_lines = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    if len(header_lines) != 255:
        raise RuntimeError(f"expected 255 exact error headers, got {len(header_lines)}")
    if sum(row.get("severity") == "error" for row in rows) != 255:
        raise RuntimeError("diagnostic error count is not 255")
    if sum(row.get("severity") == "warning" for row in rows) != 343:
        raise RuntimeError("diagnostic warning count is not 343")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error{code}: {re.escape(header.message)}"
            )
            hm = [line for line in header_lines if pattern.match(line)]
            dm = [row for row in rows if row.get("severity") == "error"
                  and row.get("line") == header.line and row.get("column") == header.column
                  and row.get("code") == header.code
                  and str(row.get("message", "")).startswith(header.message)]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append({"rule": rule.label, **header.__dict__, "kind": "independent_direct_root"})
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
    module_name = "_qym_52k61k_foreign_" + name
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
            if not 52000 <= line <= 61999:
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
    foreign_rule_count = 0
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        foreign_rule_count += len(foreign_rules)
        for foreign in foreign_rules:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                foreign_active_spans += len(found)
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            equalities.append({"own": own_rule.label, "own_variant": own_variant,
                                               "foreign": f"{name}:{foreign.label}", "foreign_variant": variant})
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            overlaps.append({"own": own_label, "foreign": f"{name}:{foreign.label}",
                                             "foreign_variant": variant, "own_span": [ostart, oend],
                                             "foreign_span": [fstart, fend]})
    if foreign_rule_count < 60:
        raise RuntimeError(f"expected at least the 60 active Probe11 rules, got {foreign_rule_count}")
    if own_overlaps or equalities or overlaps:
        raise RuntimeError(f"collision: own={own_overlaps}, equalities={equalities}, foreign={overlaps}")
    return {
        "foreign_helper_sha256": identities,
        "foreign_rule_count": foreign_rule_count,
        "own_spans_checked": len(own),
        "foreign_active_spans_checked": foreign_active_spans,
        "own_span_overlaps": own_overlaps,
        "exact_anchor_equalities": equalities,
        "foreign_span_overlaps": overlaps,
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
        audits.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                       "occurrences": count, "headers": [header.__dict__ for header in rule.headers],
                       "rationale": rule.rationale, "precedent": rule.precedent})
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe10-log", type=Path, required=True)
    parser.add_argument("--probe10-error-headers", type=Path, required=True)
    parser.add_argument("--probe10-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal and not unsealed():
        raise RuntimeError("bootstrap refused: output identity already sealed")
    if not args.bootstrap_seal and unsealed():
        raise RuntimeError("output identity unsealed")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected_output() if inverse else expected_input(),
                bootstrap=args.bootstrap_seal and inverse)
    mapped = verify_authority(args.probe10_log.read_bytes(),
                              args.probe10_error_headers.read_bytes(),
                              args.probe10_diagnostics.read_bytes())
    source_text = source.decode("utf-8", errors="strict")
    collision = audit_collisions(source_text, inverse=inverse)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected_input() if inverse else expected_output(),
                bootstrap=args.bootstrap_seal and not inverse)
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
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE10_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {"candidate_sha256": INPUT_SHA256, "candidate_git_blob": INPUT_GIT_BLOB,
                      "log_sha256": LOG_SHA256, "error_headers_sha256": HEADERS_SHA256,
                      "diagnostics_sha256": DIAGNOSTICS_SHA256, "errors": 255, "warnings": 343,
                      "panic": 0, "exit": 1},
        "scope": {"candidate_lines": [52000, 61999], "independent_direct_roots_only": True,
                  "foreign_helper_span_overlap": False, "cascade_diagnostics_selected": False,
                  "excluded": EXCLUDED},
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(mapped),
        "selected_exact_probe10_lines": sorted({header.line for rule in RULES for header in rule.headers}),
        "diagnostic_map": mapped,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {"lean": False, "lake": False, "git": False, "network": False,
                      "remote": False, "repository_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
