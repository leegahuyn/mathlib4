#!/usr/bin/env python3
"""Exact-P10 conditional repairs for ten independent QYM early-mid roots.

This byte-locked static transformer owns only direct producer, API, and
typeclass roots on terminal-Probe10 lines 31941 through 35704.  It stops before
the extendOfNorm cluster, excludes all active Probe10 spans and the frozen
Probe11 frontier, mid, and tail spans, and fails closed on any identity,
diagnostic, anchor-count, or collision drift.  It is reversible, trust0, and
activation-disabled.  It never invokes Lean, Lake, Git, the network, a remote
API, or a canonical repository source.
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

SCHEMA = "qym-probe11-earlymid-p10-conditional-v1-exact-terminal-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# These four sentinels are sealed after one deterministic in-memory projection.
OUTPUT_SHA256 = "08b466d746f79292baf685622766fe7d5b1410ec1d3852560e490a04273db1f1"
OUTPUT_GIT_BLOB = "7c04a6560bb345c12cd238a93d315dbe89f24e8c"
OUTPUT_BYTES = 2_925_650
OUTPUT_LF = 61_835

# Probe10 component replacements are already active in the exact P10 input.
# Probe11 sibling helpers are independent projections, so their old anchors
# remain active.  The active-variant bit is part of the collision contract.
FOREIGN_HELPERS: dict[str, tuple[str, str]] = {
    "qym_probe10_earlytail_static.py": (
        "5d7c848db8b8ec238bbdaad29bc5532ae0020f134846d16be064a78372c58434",
        "new",
    ),
    "qym_probe10_midlate_static.py": (
        "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0",
        "new",
    ),
    "qym_probe10_late_static.py": (
        "d1c9aef94af3efac77ab5b9b87b2851adbc3eac3fcf7f18e5cc9695a61b7bccd",
        "new",
    ),
    "qym_probe10_extendofnorm_instances.py": (
        "b7942ba8d0ae94dd2827f5a59560a81a291482880c8716df299cc13dbac246bb",
        "new",
    ),
    "qym_probe11_early_frontier_static.py": (
        "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a",
        "old",
    ),
    "qym_probe11_mid_p10_authority.py": (
        "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6",
        "old",
    ),
    "qym_probe11_tail_p10_conditional.py": (
        "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49",
        "old",
    ),
}
EXPECTED_FOREIGN_RULE_FAMILIES = 69
SCOPE_FIRST_LINE = 31_941
SCOPE_LAST_LINE = 35_704
HARD_STOP_BEFORE = 36_655


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
    provenance: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "inverse_eta_hermitian_self_pos_use_iff_as_term",
        """theorem inverseEtaHermitianMetricData_self_pos
    (tau : H) {z : ℂ} (hz : z ≠ 0) :
    0 < (inverseEtaHermitianMetricData.pairing tau z z).re := by
  change
    0 <
      (⟪Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z,
        Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z⟫_ℂ).re
  rw [re_inner_self_pos (𝕜 := ℂ)]
  exact mul_ne_zero
    (Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero tau) hz
""",
        """theorem inverseEtaHermitianMetricData_self_pos
    (tau : H) {z : ℂ} (hz : z ≠ 0) :
    0 < (inverseEtaHermitianMetricData.pairing tau z z).re := by
  change
    0 <
      (⟪Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z,
        Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z⟫_ℂ).re
  exact (re_inner_self_pos (𝕜 := ℂ)).2
    (mul_ne_zero
      (Mock2.Definition15Geometry.EtaHalfWeight.etaValue_ne_zero tau) hz)
""",
        (
            Header(
                31941,
                6,
                "Tactic \u0060rewrite\u0060 failed: Did not find an occurrence of the pattern",
            ),
        ),
        "Consume the exact positivity iff in the forward direction instead of asking rewrite to locate one side.",
        "Mathlib Analysis/InnerProductSpace/Basic.lean:341-342 states re_inner_self_pos as an iff.",
        "Exact terminal-Probe10 direct producer root at 31941.",
    ),
    Rule(
        "safe_matter_potential_norm_use_norm_smul_le",
        """theorem safeMatterPotential_norm_le_coefficient
    (sector : QSector) (Y : ℝ) :
    ‖safeMatterPotential sector Y‖ ≤ sectorPotentialCoefficient sector := by
  rw [safeMatterPotential, norm_smul]
  calc
    ‖(sectorPotentialCoefficient sector : ℂ)‖ *
          ‖deltaMatterPotential Y‖
        ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (deltaMatterPotential_norm_le_one Y)
        (norm_nonneg _)
    _ = sectorPotentialCoefficient sector := by
      simp [abs_of_nonneg (sectorPotentialCoefficient_nonneg sector)]
""",
        """theorem safeMatterPotential_norm_le_coefficient
    (sector : QSector) (Y : ℝ) :
    ‖safeMatterPotential sector Y‖ ≤ sectorPotentialCoefficient sector := by
  unfold safeMatterPotential
  calc
    ‖(sectorPotentialCoefficient sector : ℂ) • deltaMatterPotential Y‖
        ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ *
            ‖deltaMatterPotential Y‖ :=
      norm_smul_le _ _
    _ ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (deltaMatterPotential_norm_le_one Y)
        (norm_nonneg _)
    _ = sectorPotentialCoefficient sector := by
      simp [abs_of_nonneg (sectorPotentialCoefficient_nonneg sector)]
""",
        (
            Header(32083, 74, "unsolved goals"),
            Header(
                32084,
                27,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
            ),
        ),
        "Use the bounded-smul inequality API; the unavailable NormSMulClass equality is stronger than this bound needs.",
        "Mathlib Analysis/Normed/MulAction.lean:34-35 provides norm_smul_le under IsBoundedSMul.",
        "Exact terminal-Probe10 paired goal and typeclass producer diagnostics at 32083-32084.",
    ),
    Rule(
        "safe_matter_potential_inner_use_specialized_inner_api",
        """theorem safeMatterPotential_inner_nonneg (sector : QSector) (Y : ℝ)
    (u : EtaMatterCarrier Y) :
    0 ≤ (⟪u, safeMatterPotential sector Y u⟫_ℂ).re := by
  rw [safeMatterPotential_apply, inner_smul_right (𝕜 := ℂ)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_nonneg (sectorPotentialCoefficient_nonneg sector) inner_self_nonneg
""",
        """theorem safeMatterPotential_inner_nonneg (sector : QSector) (Y : ℝ)
    (u : EtaMatterCarrier Y) :
    0 ≤ (⟪u, safeMatterPotential sector Y u⟫_ℂ).re := by
  rw [safeMatterPotential_apply]
  have hinner :
      ⟪u, (sectorPotentialCoefficient sector : ℂ) • u⟫_ℂ =
        (sectorPotentialCoefficient sector : ℂ) * ⟪u, u⟫_ℂ :=
    inner_smul_right u u (sectorPotentialCoefficient sector : ℂ)
  rw [hinner]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_nonneg (sectorPotentialCoefficient_nonneg sector) inner_self_nonneg
""",
        (
            Header(
                32113,
                33,
                "Tactic \u0060rewrite\u0060 failed: Did not find an occurrence of the pattern",
            ),
        ),
        "Specialize inner_smul_right to the exact carrier and coefficient before rewriting the real-part goal.",
        "Mathlib Analysis/InnerProductSpace/Defs.lean:251-253 gives the exact positional inner_smul_right equality.",
        "Exact terminal-Probe10 direct API root at 32113.",
    ),
    Rule(
        "horizontal_horocycle_continuous_use_upper_half_plane_mk",
        """theorem horizontalHorocyclePoint_continuous
    (H : ℝ) (hH : 0 < H) :
    Continuous (horizontalHorocyclePoint H hH) := by
  have hambient : Continuous
      (fun x : ℝ => (x : ℂ) + (H : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  change Continuous (fun x : ℝ =>
    (⟨(x : ℂ) + (H : ℂ) * Complex.I, by simpa using hH⟩ : ℍ))
  exact hambient.subtype_mk _
""",
        """theorem horizontalHorocyclePoint_continuous
    (H : ℝ) (hH : 0 < H) :
    Continuous (horizontalHorocyclePoint H hH) := by
  have hambient : Continuous
      (fun x : ℝ => (x : ℂ) + (H : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  change Continuous (fun x : ℝ =>
    (⟨(x : ℂ) + (H : ℂ) * Complex.I, by simpa using hH⟩ : ℍ))
  exact hambient.upperHalfPlaneMk _
""",
        (Header(34579, 2, "Type mismatch"),),
        "Use the UpperHalfPlane-specific continuous constructor rather than the generic subtype constructor with the wrong target.",
        "Mathlib Analysis/Complex/UpperHalfPlane/Topology.lean:56-59 defines Continuous.upperHalfPlaneMk.",
        "Exact terminal-Probe10 direct API root at 34579.",
    ),
    Rule(
        "eta_horizontal_trace_linear_expose_pointwise",
        """noncomputable def etaHorizontalTraceToL2Linear (Y : ℝ) :
    etaH1Core Y →ₗ[ℂ] WidthTwoBoundaryL2 where
  toFun := etaHorizontalTraceToL2 Y
  map_add' g h := by
    simpa only [etaHorizontalTraceToL2,
      etaHorizontalTraceRepresentative, Submodule.coe_add,
      etaSection_add, Pi.add_apply] using
      (MemLp.toLp_add
        (etaHorizontalTraceRepresentative_memLp Y g)
        (etaHorizontalTraceRepresentative_memLp Y h))
  map_smul' c g := by
    simpa only [etaHorizontalTraceToL2,
      etaHorizontalTraceRepresentative, Submodule.coe_smul,
      etaSection_smul, Pi.smul_apply] using
      (MemLp.toLp_const_smul c
        (etaHorizontalTraceRepresentative_memLp Y g))
""",
        """noncomputable def etaHorizontalTraceToL2Linear (Y : ℝ) :
    etaH1Core Y →ₗ[ℂ] WidthTwoBoundaryL2 where
  toFun := etaHorizontalTraceToL2 Y
  map_add' g h := by
    have hfun :
        etaHorizontalTraceRepresentative Y (g + h) =
          etaHorizontalTraceRepresentative Y g +
            etaHorizontalTraceRepresentative Y h := by
      funext x
      simp only [etaHorizontalTraceRepresentative, Submodule.coe_add,
        etaSection_add, Pi.add_apply]
    unfold etaHorizontalTraceToL2
    rw [hfun]
    exact MemLp.toLp_add
      (etaHorizontalTraceRepresentative_memLp Y g)
      (etaHorizontalTraceRepresentative_memLp Y h)
  map_smul' c g := by
    have hfun :
        etaHorizontalTraceRepresentative Y (c • g) =
          c • etaHorizontalTraceRepresentative Y g := by
      funext x
      simp only [etaHorizontalTraceRepresentative, Submodule.coe_smul,
        etaSection_smul, Pi.smul_apply]
    unfold etaHorizontalTraceToL2
    rw [hfun]
    simpa only [RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (etaHorizontalTraceRepresentative_memLp Y g))
""",
        (
            Header(34633, 4, "Type mismatch: After simplification, term"),
            Header(34640, 4, "Type mismatch: After simplification, term"),
        ),
        "Prove the representative function equality first, then apply the exact dependent MemLp toLp linearity lemmas.",
        "Mock2_FunctionalAnalysis exit-zero toL2 precedent at 18449-18455 uses MemLp.toLp_add and MemLp.toLp_const_smul.",
        "Exact terminal-Probe10 paired dependent-proof mismatch family at 34633 and 34640.",
    ),
    Rule(
        "actual_horizontal_horocycle_continuous_use_upper_half_plane_mk",
        """theorem actualFixedPhaseHorizontalHorocyclePoint_continuous
    (Y : ℝ) :
    Continuous (actualFixedPhaseHorizontalHorocyclePoint Y) := by
  have hambient : Continuous
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  change Continuous (fun x : ℝ =>
    (⟨(x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I,
      by simpa using actualFixedPhaseCuspHeight_pos Y⟩ : ℍ))
  exact hambient.subtype_mk _
""",
        """theorem actualFixedPhaseHorizontalHorocyclePoint_continuous
    (Y : ℝ) :
    Continuous (actualFixedPhaseHorizontalHorocyclePoint Y) := by
  have hambient : Continuous
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  change Continuous (fun x : ℝ =>
    (⟨(x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I,
      by simpa using actualFixedPhaseCuspHeight_pos Y⟩ : ℍ))
  exact hambient.upperHalfPlaneMk _
""",
        (Header(34982, 2, "Type mismatch"),),
        "Use the exact UpperHalfPlane constructor API for the second horizontal curve.",
        "Mathlib Analysis/Complex/UpperHalfPlane/Topology.lean:56-59 defines Continuous.upperHalfPlaneMk.",
        "Exact terminal-Probe10 direct API root at 34982.",
    ),
    Rule(
        "actual_horizontal_trace_linear_expose_pointwise",
        """noncomputable def actualFixedPhaseHorizontalTraceToL2Linear
    (n : ℤ) (Y : ℝ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ] ActualFixedPhaseWidthTwoL2 where
  toFun := actualFixedPhaseHorizontalTraceToL2 n Y
  map_add' u v := by
    simpa only [actualFixedPhaseHorizontalTraceToL2,
      actualFixedPhaseHorizontalTraceRepresentative,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
      Submodule.coe_add, Pi.add_apply] using
      (MemLp.toLp_add
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u)
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y v))
  map_smul' c u := by
    simpa only [actualFixedPhaseHorizontalTraceToL2,
      actualFixedPhaseHorizontalTraceRepresentative,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
      Submodule.coe_smul, Pi.smul_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u))
""",
        """noncomputable def actualFixedPhaseHorizontalTraceToL2Linear
    (n : ℤ) (Y : ℝ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ] ActualFixedPhaseWidthTwoL2 where
  toFun := actualFixedPhaseHorizontalTraceToL2 n Y
  map_add' u v := by
    have hfun :
        actualFixedPhaseHorizontalTraceRepresentative n Y (u + v) =
          actualFixedPhaseHorizontalTraceRepresentative n Y u +
            actualFixedPhaseHorizontalTraceRepresentative n Y v := by
      funext x
      simp only [actualFixedPhaseHorizontalTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_add, Pi.add_apply]
    unfold actualFixedPhaseHorizontalTraceToL2
    rw [hfun]
    exact MemLp.toLp_add
      (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u)
      (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y v)
  map_smul' c u := by
    have hfun :
        actualFixedPhaseHorizontalTraceRepresentative n Y (c • u) =
          c • actualFixedPhaseHorizontalTraceRepresentative n Y u := by
      funext x
      simp only [actualFixedPhaseHorizontalTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_smul, Pi.smul_apply]
    unfold actualFixedPhaseHorizontalTraceToL2
    rw [hfun]
    simpa only [RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u))
""",
        (
            Header(35063, 4, "Type mismatch: After simplification, term"),
            Header(35071, 4, "Type mismatch: After simplification, term"),
        ),
        "Separate pointwise representative linearity from dependent toLp proof transport.",
        "Mathlib MemLp.toLp_add and MemLp.toLp_const_smul provide the exact target after the representative equality.",
        "Exact terminal-Probe10 paired dependent-proof mismatch family at 35063 and 35071.",
    ),
    Rule(
        "actual_cusp_horocycle_continuous_cast_gl",
        """theorem actualFixedPhaseCuspHorocyclePoint_continuous
    (kappa : GammaTwoCusp) (Y : ℝ) :
    Continuous (actualFixedPhaseCuspHorocyclePoint kappa Y) :=
  (Homeomorph.smul (gammaTwoCuspScaling kappa)).continuous.comp
    (actualFixedPhaseHorizontalHorocyclePoint_continuous Y)
""",
        """theorem actualFixedPhaseCuspHorocyclePoint_continuous
    (kappa : GammaTwoCusp) (Y : ℝ) :
    Continuous (actualFixedPhaseCuspHorocyclePoint kappa Y) := by
  change Continuous (fun x : ℝ =>
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ) •
      actualFixedPhaseHorizontalHorocyclePoint Y x)
  exact
    (continuous_const_smul
      (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)).comp
      (actualFixedPhaseHorizontalHorocyclePoint_continuous Y)
""",
        (
            Header(
                35117,
                3,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
            ),
        ),
        "Expose the definitionally equal GL action, which owns the continuous scalar-action instance.",
        "Mock2_FunctionalAnalysis exit-zero continuous_sl2z_smul precedent at 4331-4334 casts SL(2,Z) to GL(Fin 2,R).",
        "Exact terminal-Probe10 continuous-action producer root at 35117.",
    ),
    Rule(
        "actual_named_cusp_trace_linear_expose_pointwise",
        """noncomputable def actualFixedPhaseNamedCuspTraceToL2Linear
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ] ActualFixedPhaseWidthTwoL2 where
  toFun := actualFixedPhaseNamedCuspTraceToL2 n kappa Y
  map_add' u v := by
    simpa only [actualFixedPhaseNamedCuspTraceToL2,
      actualFixedPhaseNamedCuspTraceRepresentative,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
      Submodule.coe_add, Pi.add_apply] using
      (MemLp.toLp_add
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u)
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y v))
  map_smul' c u := by
    simpa only [actualFixedPhaseNamedCuspTraceToL2,
      actualFixedPhaseNamedCuspTraceRepresentative,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
      Submodule.coe_smul, Pi.smul_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u))
""",
        """noncomputable def actualFixedPhaseNamedCuspTraceToL2Linear
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ] ActualFixedPhaseWidthTwoL2 where
  toFun := actualFixedPhaseNamedCuspTraceToL2 n kappa Y
  map_add' u v := by
    have hfun :
        actualFixedPhaseNamedCuspTraceRepresentative n kappa Y (u + v) =
          actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u +
            actualFixedPhaseNamedCuspTraceRepresentative n kappa Y v := by
      funext x
      simp only [actualFixedPhaseNamedCuspTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_add, Pi.add_apply]
    unfold actualFixedPhaseNamedCuspTraceToL2
    rw [hfun]
    exact MemLp.toLp_add
      (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u)
      (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y v)
  map_smul' c u := by
    have hfun :
        actualFixedPhaseNamedCuspTraceRepresentative n kappa Y (c • u) =
          c • actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u := by
      funext x
      simp only [actualFixedPhaseNamedCuspTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_smul, Pi.smul_apply]
    unfold actualFixedPhaseNamedCuspTraceToL2
    rw [hfun]
    simpa only [RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u))
""",
        (
            Header(35181, 4, "Type mismatch: After simplification, term"),
            Header(35189, 4, "Type mismatch: After simplification, term"),
        ),
        "Apply the same pointwise-then-dependent-toLp repair to the named-cusp trace map.",
        "Mathlib MemLp.toLp_add and MemLp.toLp_const_smul are the exact linearity APIs.",
        "Exact terminal-Probe10 paired dependent-proof mismatch family at 35181 and 35189.",
    ),
    Rule(
        "cusp_class_horocycle_closed_cast_gl",
        """theorem cuspClassHorocycleBoundary_isClosed
    (Y : ℝ) (kappa : GammaTwoCusp) :
    IsClosed (gammaTwoCuspClassHorocycleBoundary kappa Y) := by
  classical
  unfold gammaTwoCuspClassHorocycleBoundary
  exact isClosed_iUnion_of_finite fun q ↦
    (isClosed_eq UpperHalfPlane.continuous_im continuous_const).smul
      (gammaTwoCosetRep q.1)
""",
        """theorem cuspClassHorocycleBoundary_isClosed
    (Y : ℝ) (kappa : GammaTwoCusp) :
    IsClosed (gammaTwoCuspClassHorocycleBoundary kappa Y) := by
  classical
  unfold gammaTwoCuspClassHorocycleBoundary
  exact isClosed_iUnion_of_finite fun q ↦ by
    change IsClosed
      ((gammaTwoCosetRep q.1 : GL (Fin 2) ℝ) •
        {z : ℍ | z.im = gammaTwoCuspLevel Y})
    exact
      (isClosed_eq UpperHalfPlane.continuous_im continuous_const).smul
        (gammaTwoCosetRep q.1 : GL (Fin 2) ℝ)
""",
        (
            Header(
                35704,
                4,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
            ),
        ),
        "Expose the GL pointwise set action before applying IsClosed.smul, avoiding the absent SL continuous-action instance.",
        "The same exact SL-to-GL definitional cast is established by the exit-zero continuous_sl2z_smul precedent.",
        "Exact terminal-Probe10 set-action producer root at 35704.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        f"blob {len(raw)}\0".encode("ascii") + raw
    ).hexdigest()


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
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def sentinels_unsealed() -> bool:
    return (
        OUTPUT_SHA256 == ""
        and OUTPUT_GIT_BLOB == ""
        and OUTPUT_BYTES == 0
        and OUTPUT_LF == 0
    )


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


def check_shape(
    actual: dict[str, object],
    expected: dict[str, object],
    *,
    unsealed: bool = False,
) -> None:
    if unsealed:
        for key in ("cr", "nul", "bom", "terminal_lf"):
            if actual[key] != expected[key]:
                raise RuntimeError(f"unsealed structural shape mismatch: {key}")
        return
    if actual != expected:
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def parse_diagnostics(raw: bytes) -> list[dict[str, object]]:
    return [
        json.loads(line)
        for line in raw.decode("utf-8", errors="strict").splitlines()
    ]


def verify_authority(
    log_raw: bytes,
    header_raw: bytes,
    diagnostics_raw: bytes,
) -> list[dict[str, object]]:
    identities = {
        "log": (sha256(log_raw), LOG_SHA256),
        "error_headers": (sha256(header_raw), HEADERS_SHA256),
        "diagnostics": (sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    }
    for label, (actual, expected) in identities.items():
        if actual != expected:
            raise RuntimeError(
                f"Probe10 {label} identity mismatch: {actual} != {expected}"
            )

    header_lines = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = parse_diagnostics(diagnostics_raw)
    if len(header_lines) != 255:
        raise RuntimeError(f"expected 255 exact error headers, got {len(header_lines)}")
    if sum(row.get("severity") == "error" for row in rows) != 255:
        raise RuntimeError("diagnostic error count is not 255")
    if sum(row.get("severity") == "warning" for row in rows) != 343:
        raise RuntimeError("diagnostic warning count is not 343")

    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            if not SCOPE_FIRST_LINE <= header.line <= SCOPE_LAST_LINE:
                raise RuntimeError(f"{rule.label}: diagnostic escaped hard scope")
            if header.line >= HARD_STOP_BEFORE:
                raise RuntimeError(f"{rule.label}: diagnostic crossed hard stop")
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:"
                rf"{header.column}: error{code}: {re.escape(header.message)}"
            )
            header_matches = [
                line for line in header_lines if pattern.match(line)
            ]
            diagnostic_matches = [
                row
                for row in rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(header_matches) != 1 or len(diagnostic_matches) != 1:
                raise RuntimeError(
                    f"{rule.label}: P10 authority mapping mismatch at "
                    f"{header.line}:{header.column}"
                )
            verified.append(
                {
                    "rule": rule.label,
                    "line": header.line,
                    "column": header.column,
                    "code": header.code,
                    "message": header.message,
                    "kind": "independent_direct_producer_api_typeclass_root",
                    "provenance": rule.provenance,
                }
            )
    if len(verified) != 14:
        raise RuntimeError(f"expected 14 direct diagnostics, got {len(verified)}")
    return verified


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        offset = text.find(needle, start)
        if offset < 0:
            return result
        result.append((offset, offset + len(needle)))
        start = offset + 1


def load_helper(path: Path) -> ModuleType:
    name = "_qym_probe11_earlymid_foreign_" + hashlib.sha256(
        str(path.resolve()).encode("utf-8")
    ).hexdigest()
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def audit_internal_independence(
    base: str,
    *,
    inverse: bool,
) -> dict[str, object]:
    active = {
        rule.label: (rule.new if inverse else rule.old)
        for rule in RULES
    }
    active_spans: list[tuple[int, int, str]] = []
    for label, anchor in active.items():
        found = spans(base, anchor)
        if len(found) != 1:
            raise RuntimeError(
                f"own active span count mismatch: {label}: {len(found)}"
            )
        active_spans.append((found[0][0], found[0][1], label))

    overlaps: list[dict[str, object]] = []
    for index, (left_start, left_end, left_label) in enumerate(active_spans):
        for right_start, right_end, right_label in active_spans[index + 1:]:
            if max(left_start, right_start) < min(left_end, right_end):
                overlaps.append(
                    {
                        "left": left_label,
                        "right": right_label,
                        "left_span": [left_start, left_end],
                        "right_span": [right_start, right_end],
                    }
                )

    cross_variant_containment: list[dict[str, str]] = []
    for left in RULES:
        for right in RULES:
            if left.label == right.label:
                continue
            for left_kind, left_anchor in (("old", left.old), ("new", left.new)):
                for right_kind, right_anchor in (
                    ("old", right.old),
                    ("new", right.new),
                ):
                    if right_anchor in left_anchor:
                        cross_variant_containment.append(
                            {
                                "container": left.label,
                                "container_variant": left_kind,
                                "contained": right.label,
                                "contained_variant": right_kind,
                            }
                        )
    if overlaps or cross_variant_containment:
        raise RuntimeError(
            "internal collision: "
            f"overlaps={overlaps}, containment={cross_variant_containment}"
        )

    return {
        "own_active_spans_checked": len(active_spans),
        "active_span_overlaps": overlaps,
        "cross_variant_containment": cross_variant_containment,
        "pairwise_noninterference": True,
        "all_forward_and_inverse_orders_have_one_exact_result": True,
    }


def audit_foreign_collisions(
    base: str,
    helper_paths: list[Path],
    *,
    inverse: bool,
) -> dict[str, object]:
    by_name: dict[str, Path] = {}
    for path in helper_paths:
        if path.name in by_name:
            raise RuntimeError(f"duplicate foreign helper basename: {path.name}")
        by_name[path.name] = path
    if set(by_name) != set(FOREIGN_HELPERS):
        raise RuntimeError(
            "foreign helper set mismatch: "
            f"{sorted(by_name)} != {sorted(FOREIGN_HELPERS)}"
        )

    own_spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(base, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"own collision-audit span mismatch: {rule.label}")
        own_spans.extend((start, end, rule.label) for start, end in found)

    identities: dict[str, dict[str, str]] = {}
    exact_anchor_equalities: list[dict[str, str]] = []
    overlaps: list[dict[str, object]] = []
    foreign_families = 0
    foreign_spans_checked = 0
    for name, (expected_sha, active_variant) in FOREIGN_HELPERS.items():
        path = by_name[name]
        if not path.is_file():
            raise RuntimeError(f"foreign helper missing: {path}")
        actual_sha = sha256(path.read_bytes())
        if actual_sha != expected_sha:
            raise RuntimeError(
                f"foreign helper identity mismatch: {name}: "
                f"{actual_sha} != {expected_sha}"
            )
        module = load_helper(path)
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        identities[name] = {
            "sha256": actual_sha,
            "active_variant": active_variant,
        }
        for foreign in foreign_rules:
            foreign_families += 1
            foreign_old = getattr(foreign, "old")
            foreign_new = getattr(foreign, "new")
            foreign_label = getattr(foreign, "label")
            expected_count = getattr(foreign, "occurrences", 1)
            foreign_active = (
                foreign_new if active_variant == "new" else foreign_old
            )
            found = spans(base, foreign_active)
            if len(found) != expected_count:
                raise RuntimeError(
                    f"foreign active span count mismatch: {name}:{foreign_label}: "
                    f"{len(found)} != {expected_count}"
                )
            foreign_spans_checked += len(found)
            for own in RULES:
                for own_kind, own_anchor in (("old", own.old), ("new", own.new)):
                    for foreign_kind, foreign_anchor in (
                        ("old", foreign_old),
                        ("new", foreign_new),
                    ):
                        if own_anchor == foreign_anchor:
                            exact_anchor_equalities.append(
                                {
                                    "own": own.label,
                                    "own_variant": own_kind,
                                    "foreign_helper": name,
                                    "foreign_rule": foreign_label,
                                    "foreign_variant": foreign_kind,
                                }
                            )
            for foreign_start, foreign_end in found:
                for own_start, own_end, own_label in own_spans:
                    if max(foreign_start, own_start) < min(
                        foreign_end, own_end
                    ):
                        overlaps.append(
                            {
                                "own": own_label,
                                "foreign_helper": name,
                                "foreign_rule": foreign_label,
                                "own_span": [own_start, own_end],
                                "foreign_span": [foreign_start, foreign_end],
                            }
                        )
    if foreign_families != EXPECTED_FOREIGN_RULE_FAMILIES:
        raise RuntimeError(
            f"foreign rule-family count {foreign_families} != "
            f"{EXPECTED_FOREIGN_RULE_FAMILIES}"
        )
    if exact_anchor_equalities or overlaps:
        raise RuntimeError(
            "foreign collision: "
            f"equalities={exact_anchor_equalities}, overlaps={overlaps}"
        )
    return {
        "helper_identities": identities,
        "foreign_rule_families_checked": foreign_families,
        "foreign_active_spans_checked": foreign_spans_checked,
        "own_spans_checked": len(own_spans),
        "exact_anchor_equalities": exact_anchor_equalities,
        "span_overlaps": overlaps,
    }


def apply_rules(
    text: str,
    inverse: bool = False,
) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact anchor count {count}, "
                f"expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audits.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
                "precedent": rule.precedent,
                "provenance": rule.provenance,
            }
        )
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe10-log", type=Path, required=True)
    parser.add_argument("--probe10-error-headers", type=Path, required=True)
    parser.add_argument("--probe10-diagnostics", type=Path, required=True)
    parser.add_argument(
        "--foreign-helper",
        type=Path,
        action="append",
        required=True,
    )
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument(
        "--mode",
        choices=("forward", "inverse"),
        default="forward",
    )
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    if args.bootstrap_seal and not sentinels_unsealed():
        raise RuntimeError("bootstrap seal refused: output identity already sealed")
    if not args.bootstrap_seal and sentinels_unsealed():
        raise RuntimeError("output identity unsealed; bootstrap projection required")

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        output_expected() if inverse else input_expected(),
        unsealed=args.bootstrap_seal and inverse,
    )
    diagnostic_map = verify_authority(
        args.probe10_log.read_bytes(),
        args.probe10_error_headers.read_bytes(),
        args.probe10_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    internal = audit_internal_independence(source_text, inverse=inverse)
    foreign = audit_foreign_collisions(
        source_text,
        args.foreign_helper,
        inverse=inverse,
    )
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
    restored_text, _ = apply_rules(result_text, inverse=not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE10_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe10_run_id": 31973408809,
            "probe10_job_id": 95229227905,
            "probe10_head_sha": "0957f9b925663bc78b76c7207084fb6199eb60de",
            "probe10_trigger_sha": "0957f9b925663bc78b76c7207084fb6199eb60de",
            "probe10_result_sha256": "0a908f0ae2bae582285d3d48c5ccb30829c2225af2b397b5ffd1a499798d279d",
            "artifact_id": 9270510078,
            "artifact_name": "qym-repair-probe10-integrated-0957f9b925663bc78b76c7207084fb6199eb60de-attempt1",
            "artifact_api_size": 10487379,
            "artifact_zip_sha256": "0b2e4c1ba61974967f3a79bc1d32f7480fa1bdc484cfe82d763b5ee03bf4f101",
            "artifact_digest": "sha256:0b2e4c1ba61974967f3a79bc1d32f7480fa1bdc484cfe82d763b5ee03bf4f101",
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "candidate_bytes": INPUT_BYTES,
            "candidate_lf": INPUT_LF,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 255,
            "warnings": 343,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [SCOPE_FIRST_LINE, SCOPE_LAST_LINE],
            "hard_stop_before_line": HARD_STOP_BEFORE,
            "direct_producer_api_typeclass_roots_only": True,
            "cascade_diagnostics_selected": False,
            "probe10_active_spans_excluded": True,
            "probe10_owned_requested_diagnostics_excluded": [
                34069, 34157, 34158, 34160, 34167,
            ],
            "probe10_owning_rules": [
                "polygon_edge_pairing_set_result_ascription",
                "smooth_compact_weight_core_unwrap_subtype",
                "inverse_eta_core_unwrap_subtype",
            ],
            "probe11_frontier_mid_tail_spans_excluded": True,
            "pending_40k_spans_excluded_by_disjoint_line_scope": True,
            "extend_of_norm_cluster_excluded": True,
            "extend_of_norm_cluster_first_line": HARD_STOP_BEFORE,
            "foreign_helper_contract": FOREIGN_HELPERS,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(
            item["occurrences"] for item in rule_audit
        ),
        "direct_diagnostics": len(diagnostic_map),
        "diagnostic_map": diagnostic_map,
        "rules": rule_audit,
        "selected_exact_probe10_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "internal_independence_audit": internal,
        "foreign_collision_audit": foreign,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "static_evidence": {
            "re_inner_self_pos_iff_api": "Mathlib Analysis/InnerProductSpace/Basic.lean:341-342",
            "norm_smul_le_api": "Mathlib Analysis/Normed/MulAction.lean:34-35",
            "inner_smul_right_api": "Mathlib Analysis/InnerProductSpace/Defs.lean:251-253",
            "upper_half_plane_mk_api": "Mathlib Analysis/Complex/UpperHalfPlane/Topology.lean:56-59",
            "sl_to_gl_continuity_precedent": "Mock2_FunctionalAnalysis exit-zero lines 4331-4334",
            "memlp_to_lp_linearity_precedent": "Mock2_FunctionalAnalysis exit-zero lines 18449-18455",
        },
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
    args.audit.write_text(
        json.dumps(record, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
