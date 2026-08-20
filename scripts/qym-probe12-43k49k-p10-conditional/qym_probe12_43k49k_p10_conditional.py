#!/usr/bin/env python3
"""Exact-P10 conditional repairs for independent QYM roots in lines 43000-49999.

The transformer is byte-locked to terminal Probe10 and owns only direct
producer/API/typeclass roots that are not owned by the seven frozen Probe11
helpers.  It also audits the four already-active Probe10 helpers, the frozen
Probe12 36k-42k sibling, and the explicit Probe12 midlate refinement.  The
large inverse-eta base cascade, every timeout cascade, every 40k-owned span,
and the structural 50k tranche are excluded.  The transform is reversible,
trust0, activation-disabled, and performs no Lean, Lake, Git, network, remote,
or canonical-source operation.
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

SCHEMA = "qym-probe12-43k49k-p10-conditional-v1-exact-terminal-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# Sealed after one deterministic in-memory bootstrap projection.
OUTPUT_SHA256 = "9fb96bda383ca230e04a937b7f4e852f0892794cba90e5ac7d862cce1641a6a2"
OUTPUT_GIT_BLOB = "95c92d5e88805b49ba24b994dc7f88399e795b8e"
OUTPUT_BYTES = 2_928_709
OUTPUT_LF = 61_883

SCOPE_FIRST_LINE = 43_000
SCOPE_LAST_LINE = 49_999
HARD_STOP_BEFORE = 50_000

# Probe10 helpers are already active in INPUT, so their new anchors must exist.
# Probe11/Probe12 helpers are independent projections from INPUT, so their old
# anchors must exist.  Every identity and active-variant bit is fail-closed.
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
    "qym_probe11_earlymid_p10_conditional.py": (
        "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6",
        "old",
    ),
    "qym_probe11_40k_p10_conditional.py": (
        "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052",
        "old",
    ),
    "qym_probe11_50k_structural_p10.py": (
        "82189532a76f4785734d851f459a67c2dc04e373d1fc70eb5a137506f2dc57ae",
        "old",
    ),
    "qym_probe12_p10_midlate_refinement.py": (
        "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d",
        "old",
    ),
    "qym_probe12_36k42k_p10_conditional.py": (
        "9c3df7c522538373943cde18e2a788a4fc7feec5412724e37ccfb6a508865095",
        "old",
    ),
}
EXPECTED_FOREIGN_RULE_FAMILIES = 107


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
        "hhalf_difference_to_l2_expose_raw_tolp",
        """    simpa only [QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoHhalfDifferenceToL2] using
      (u (phi (psi k))).property.coeFn_toLp
""",
        """    change
      (((u (phi (psi k))).property.toLp
          (QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoTwistedDifferenceQuotient tau
            ((u (phi (psi k))).1 : ℝ → ℂ)) :
        QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2) :
          (ℝ × ℝ) → ℂ) =ᵐ[
            QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseWidthTwoProductMeasure]
        QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoTwistedDifferenceQuotient tau
          ((u (phi (psi k))).1 : ℝ → ℂ)
    exact (u (phi (psi k))).property.coeFn_toLp
""",
        (Header(43238, 4, "Type mismatch: After simplification, term"),),
        "Expose the literal MemLp.toLp representative before consuming coeFn_toLp.",
        "Exact same coeFn_toLp shape is used directly by QYM Lp realization lemmas at P10 lines 27894-27900 and 28785-28790.",
        "Exact P10 direct producer root 43238; no downstream diagnostic is selected.",
    ),
    Rule(
        "hhalf_graph_fst_tendsto_expose_fstL",
        """    simpa only [Function.comp_def] using
      (WithLp.fstL 2 ℂ QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
        QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2).continuous.continuousAt.tendsto.comp
          hGraphTendsto
""",
        """    change
      Tendsto
        (fun n =>
          (WithLp.fstL 2 ℂ
            QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
            QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2)
              (QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoHhalfGraphMap tau (f n)))
        atTop
        (𝓝 ((WithLp.fstL 2 ℂ
          QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
          QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2)
            (z : QYM.FullCertification.P2ClassicalHhalfTraceExtension.WidthTwoHhalfGraphAmbient)))
    exact
      (WithLp.fstL 2 ℂ QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
        QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2).continuous.continuousAt.tendsto.comp
          hGraphTendsto
""",
        (Header(43305, 4, "Type mismatch: After simplification, term"),),
        "State the projection limit with the exact continuous-linear projection used by the producer.",
        "The exact diagnostic differs only by WithLp.fst versus WithLp.fstL application.",
        "Exact P10 direct API root 43305.",
    ),
    Rule(
        "hhalf_graph_snd_tendsto_expose_sndL",
        """      simpa only [Function.comp_def] using
        (WithLp.sndL 2 ℂ QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
          QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2).continuous.continuousAt.tendsto.comp
            hGraphTendsto
""",
        """      change
        Tendsto
          (fun n =>
            (WithLp.sndL 2 ℂ
              QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
              QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2)
                (QYM.FullCertification.P2ClassicalHhalfTraceExtension.widthTwoHhalfGraphMap tau (f n)))
          atTop
          (𝓝 ((WithLp.sndL 2 ℂ
            QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
            QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2)
              (z : QYM.FullCertification.P2ClassicalHhalfTraceExtension.WidthTwoHhalfGraphAmbient)))
      exact
        (WithLp.sndL 2 ℂ QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.ActualFixedPhaseWidthTwoL2
          QYM.FullCertification.P2ClassicalHhalfTraceExtension.ActualFixedPhaseWidthTwoGagliardoL2).continuous.continuousAt.tendsto.comp
            hGraphTendsto
""",
        (Header(43324, 6, "Type mismatch: After simplification, term"),),
        "State the second-projection limit with the exact continuous-linear projection.",
        "The exact diagnostic differs only by WithLp.snd versus WithLp.sndL application.",
        "Exact P10 direct API root 43324.",
    ),
    Rule(
        "hhalf_injective_unwrap_withlp_projections",
        """  apply Prod.ext
  · simpa only [WithLp.ofLp_zero] using hzFst
  · simpa only [WithLp.ofLp_zero] using hzSnd
""",
        """  apply Prod.ext
  · change
      WithLp.fst
          (z : QYM.FullCertification.P2ClassicalHhalfTraceExtension.WidthTwoHhalfGraphAmbient) = 0
    exact hzFst
  · change
      WithLp.snd
          (z : QYM.FullCertification.P2ClassicalHhalfTraceExtension.WidthTwoHhalfGraphAmbient) = 0
    exact hzSnd
""",
        (
            Header(43356, 4, "Type mismatch: After simplification, term"),
            Header(43357, 4, "Type mismatch: After simplification, term"),
        ),
        "Expose each WithLp projection instead of simplifying across the raw ofLp product.",
        "The exact expected goals are the two raw ofLp Prod projections produced by WithLp.ofLp_injective.",
        "Exact P10 paired direct projection roots 43356-43357.",
    ),
    Rule(
        "circular_radicand_derivative_tolerate_normal_goals",
        """  convert (hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_id t).div_const 2).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
""",
        """  convert (hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_id t).div_const 2).pow 2) using 1 <;>
      (try simp only [id_eq]) <;> ring
""",
        (Header(43592, 60, "unsolved goals"),),
        "Permit the id simplifier to be a no-op on the already-normalized derivative coefficient, then close it by ring.",
        "The exact residual is -t/2 = 0 - 2*(t/2)^(2-1)*(1/2), a polynomial identity.",
        "Exact P10 direct algebra root 43592; duplicate simp-no-progress and declaration cascades are not selected.",
    ),
    Rule(
        "selected_representative_derivative_use_exact_det_pos",
        """      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := selectedRepresentativeRealMatrix q) (by simp) z)
""",
        """      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := selectedRepresentativeRealMatrix q) (by
          change 0 <
            (((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
              SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det
          exact
            Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseIntrinsicAdjointCutoff.integralMoebius_det_pos
              (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)) z)
""",
        (Header(43680, 54, "`simp` made no progress"),),
        "Use the already-proved determinant-positivity theorem for the exact integral representative.",
        "Mock2 FunctionalAnalysis exit-zero integralMoebius_det_pos proves positivity for every SL(2,Z) cast to GL(2,R).",
        "Exact P10 direct API root 43680; owner line 43629 is untouched.",
    ),
    Rule(
        "edge_velocity_tail_pin_canonical_derivative_instances",
        """  exact actualEdgeCoordinate_eq_explicit_of_mem e hs

/-- The explicit actual curve has the displayed ordinary derivative. -/
""",
        """  exact actualEdgeCoordinate_eq_explicit_of_mem e hs

local instance p2EdgeVelocityCanonicalComplexAddCommGroup : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup

local instance p2EdgeVelocityCanonicalRealAddCommGroup : AddCommGroup ℝ :=
  Real.normedCommRing.toAddCommGroup

local instance p2EdgeVelocityCanonicalRealModule : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule

/-- The explicit actual curve has the displayed ordinary derivative. -/
""",
        (
            Header(43729, 2, "Type mismatch: After simplification, term"),
            Header(43855, 4, "Type mismatch: After simplification, term"),
            Header(43868, 2, "Type mismatch: After simplification, term"),
            Header(43885, 2, "Type mismatch: After simplification, term"),
        ),
        "Pin the exact norm-derived additive and scalar instances for the remaining derivative declarations in this namespace.",
        "The diagnostics print the canonical norm-derived instances on producer terms and distinct additive/module diamonds on expected types.",
        "Exact P10 typeclass producer root after 43712; it begins after the 40k-owned 43629 theorem.",
    ),
    Rule(
        "action_d1_change_to_moebius_coordinate",
        """  have hD1 :
      d1 (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate e.pairingElement)
          (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t) =
        QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t /
          inverseEtaPaperOrbitDenom e.pairingElement
            (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) ^ 2 := by
    simpa [Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate, gammaTwoMoebiusCoordinate] using
      (d1_gammaTwoMoebiusCoordinate e.pairingElement
        (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t))
""",
        """  have hD1 :
      d1 (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate e.pairingElement)
          (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t) =
        QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t /
          inverseEtaPaperOrbitDenom e.pairingElement
            (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) ^ 2 := by
    change
      d1 (gammaTwoMoebiusCoordinate e.pairingElement)
          (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t)
          (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t) =
        QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t /
          inverseEtaPaperOrbitDenom e.pairingElement
            (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) ^ 2
    exact d1_gammaTwoMoebiusCoordinate e.pairingElement
      (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t)
      (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t)
""",
        (Header(43847, 4, "Type mismatch: After simplification, term"),),
        "Change the definitional action-coordinate alias to the exact theorem API before applying it.",
        "Both imported coordinate definitions are the same typed SL(2,Z) action, but simp retained different opaque names.",
        "Exact P10 direct API root 43847.",
    ),
    Rule(
        "inverse_eta_transition_contdiff_use_pointwise_bridge",
        """  have hinverseEta : ContDiff ℝ ∞
      (fun x : ℝ =>
        (inverseEtaMultiplier GammaTwo).factor
          (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspDeckTranslation kappa)
          (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x)) := by
    simp_rw [inverseEtaMultiplier_factor,
      ← QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspHorocyclePoint_add_two]
    exact heta.div hetaShift
      (fun x => ModularForm.eta_ne_zero
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2)
""",
        """  have hinverseEta : ContDiff ℝ ∞
      (fun x : ℝ =>
        (inverseEtaMultiplier GammaTwo).factor
          (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspDeckTranslation kappa)
          (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x)) := by
    have hfun :
        (fun x : ℝ =>
          (inverseEtaMultiplier GammaTwo).factor
            (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspDeckTranslation kappa)
            (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x)) =
          (fun x : ℝ =>
            ModularForm.eta
                ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ) /
              ModularForm.eta
                ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2) : ℍ) : ℂ)) := by
      funext x
      rw [inverseEtaMultiplier_factor]
      exact (congrArg
        (fun z : ℍ =>
          ModularForm.eta
              ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ) /
            ModularForm.eta (z : ℂ))
        (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspHorocyclePoint_add_two
          kappa Y x)).symm
    rw [hfun]
    exact heta.div hetaShift
      (fun x => ModularForm.eta_ne_zero
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2)
""",
        (Header(44040, 6, "`simp` made no progress"),),
        "Prove the eta-ratio function equality pointwise with the existing width-two shift theorem, then transport ContDiff.",
        "Exact P10 lines 41237-41252 prove the continuous analogue by the identical inverseEtaMultiplier_factor congrArg bridge.",
        "Exact P10 direct API root 44040; 40k-owned power branches 44067/44069 are untouched.",
    ),
    Rule(
        "right_normal_signed_area_finish_ring_nf",
        """  field_simp [hn]
  <;> ring
""",
        """  field_simp [hn]
  <;> ring_nf
""",
        (Header(44364, 18, "unsolved goals"),),
        "Normalize the residual coordinate polynomial after clearing the nonzero norm denominator.",
        "The frozen 40k sibling uses ring_nf for the two adjacent right-normal coordinate residuals.",
        "Exact P10 direct algebra root 44364; sibling-owned 44344/44356 spans are disjoint.",
    ),
    Rule(
        "selected_horocycle_base_derivative_use_ofreal_clm",
        """theorem selectedHorocycleBaseCoordinate_hasDerivAt (Y t : ℝ) :
    HasDerivAt (selectedHorocycleBaseCoordinate Y) (1 : ℂ) t := by
  have h :=
    ((hasDerivAt_id (t : ℂ)).comp_ofReal).const_add
      (((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y : ℝ) : ℂ) * Complex.I)
  simpa [selectedHorocycleBaseCoordinate, Complex.mk_eq_add_mul_I,
    add_comm] using h
""",
        """theorem selectedHorocycleBaseCoordinate_hasDerivAt (Y t : ℝ) :
    HasDerivAt (selectedHorocycleBaseCoordinate Y) (1 : ℂ) t := by
  have hreal : HasDerivAt (⇑Complex.ofRealCLM) 1 t :=
    (Complex.ofRealCLM.hasFDerivAt (x := t)).hasDerivAt
  have hcurve :
      selectedHorocycleBaseCoordinate Y =
        fun s : ℝ =>
          (s : ℂ) +
            (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y : ℂ) * Complex.I := by
    funext s
    simp only [selectedHorocycleBaseCoordinate, Complex.mk_eq_add_mul_I]
  rw [hcurve]
  exact hreal.add_const
    ((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y : ℂ) * Complex.I)
""",
        (Header(46956, 2, "Type mismatch: After simplification, term"),),
        "Use the typed ofReal continuous-linear derivative and a separate exact curve identity.",
        "Exact P10 horizontalHorocycleAmbientCurve_hasDerivAt at lines 34410-34422 uses the same ofRealCLM plus add_const proof.",
        "Exact P10 direct derivative root 46956; sibling-owned 46996 is untouched.",
    ),
    Rule(
        "product_collar_fst_norm_use_carrier_argument",
        """  exact WithLp.norm_fst_le ℂ x
""",
        """  exact WithLp.norm_fst_le
    (ActualFixedPhaseCollarBoundary n Y) x
""",
        (Header(48668, 29, "Application type mismatch: The argument"),),
        "Pass the first product carrier expected by WithLp.norm_fst_le, not the scalar field.",
        "All exit-zero WithLp.norm_fst_le precedents pass the first coordinate type as the explicit argument.",
        "Exact P10 direct API root 48668; subsequent typeclass timeouts are excluded cascades.",
    ),
    Rule(
        "product_collar_pythagoras_normalize_pow_two",
        """    _ =
        ‖actualFixedPhaseProductCollarProfileExtension n Y
            (actualFixedPhaseProductCollarCentralTrace n Y x)‖ ^ 2 +
          ‖actualFixedPhaseProductCollarZeroTraceRemainder n Y x‖ ^ 2 :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner
""",
        """    _ =
        ‖actualFixedPhaseProductCollarProfileExtension n Y
            (actualFixedPhaseProductCollarCentralTrace n Y x)‖ ^ 2 +
          ‖actualFixedPhaseProductCollarZeroTraceRemainder n Y x‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner
""",
        (Header(48893, 6, "Type mismatch"),),
        "Normalize squares to the multiplication form returned by the exact orthogonality theorem.",
        "The diagnostic prints only x^2 versus x*x on all three norm terms.",
        "Exact P10 direct API-shape root 48893.",
    ),
    Rule(
        "product_collar_core_smul_expose_exact_map",
        """  map_smul' c p := by
    simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, Submodule.coe_smul]
    exact (smul_add c _ _).symm
""",
        """  map_smul' c p := by
    change
      actualFixedPhaseProductCollarProfileExtension n Y (c • p.1) +
          c • p.2.1 =
        c • (actualFixedPhaseProductCollarProfileExtension n Y p.1 + p.2.1)
    rw [map_smul]
    exact (smul_add c _ _).symm
""",
        (Header(48920, 4, "`simp` made no progress"),),
        "Expose the exact product/submodule scalar coordinates, rewrite the one linear map, and apply smul_add.",
        "The old broad WithLp simplifier has no occurrence in the exact structure goal.",
        "Exact P10 direct structure-field root 48920; timeout declarations after it are excluded.",
    ),
    Rule(
        "selected_high_point_use_typed_action_and_setof_goal",
        """  have hUOpen : IsOpen U := by
    exact isOpen_lt
      (gammaTwoModularHeightEnvelope_continuous.comp
        (continuous_const_smul (gammaTwoCosetRep q)⁻¹))
      continuous_const
  have hUSubset : U ⊆ QYM.FullCertification.P2ExactBoundaryInhabitantsExtension.saturatedXStage Y := by
    intro z hz
    exact QYM.FullCertification.P2ExactBoundaryInhabitantsExtension.mem_saturatedXStage_of_tileEnvelope_lt q
      (by simpa only [U] using hz)
""",
        """  have hUOpen : IsOpen U := by
    exact isOpen_lt
      (gammaTwoModularHeightEnvelope_continuous.comp
        ((Homeomorph.smul ((gammaTwoCosetRep q)⁻¹) : ℍ ≃ₜ ℍ).continuous))
      continuous_const
  have hUSubset : U ⊆ QYM.FullCertification.P2ExactBoundaryInhabitantsExtension.saturatedXStage Y := by
    intro z hz
    change
      gammaTwoModularHeightEnvelope ((gammaTwoCosetRep q)⁻¹ • z) <
        gammaTwoCuspLevel Y at hz
    exact QYM.FullCertification.P2ExactBoundaryInhabitantsExtension.mem_saturatedXStage_of_tileEnvelope_lt q hz
""",
        (
            Header(
                49255,
                9,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
            ),
            Header(49260, 10, "Type mismatch: After simplification, term"),
        ),
        "Pin the upper-half-plane action homeomorphism and expose Set.mem_setOf directly.",
        "Frozen 40k rule 42663 uses the identical typed Homeomorph.smul continuity producer.",
        "Exact P10 paired direct topology/API roots 49255 and 49260.",
    ),
    Rule(
        "one_sided_height_embedding_expose_codrestrict",
        """theorem oneSidedHeightToCuspBand_isEmbedding (Y : ℝ) :
    IsEmbedding (oneSidedHeightToCuspBand Y) := by
  simpa only [oneSidedHeightToCuspBand] using
    (Topology.IsEmbedding.subtypeVal.codRestrict
      (QYM.FullCertification.P2CuspCollarClosureExtension.CuspBand Y)
      (fun h : OneSidedHeightBand Y =>
        ⟨h.2.1,
          lt_of_le_of_lt h.2.2
            (lt_add_of_pos_right _ QYM.FullCertification.P2CuspCollarClosureExtension.collarRadius_pos)⟩))
""",
        """theorem oneSidedHeightToCuspBand_isEmbedding (Y : ℝ) :
    IsEmbedding (oneSidedHeightToCuspBand Y) := by
  change IsEmbedding
    (fun h : OneSidedHeightBand Y =>
      (⟨h.1, h.2.1,
        lt_of_le_of_lt h.2.2
          (lt_add_of_pos_right _ QYM.FullCertification.P2CuspCollarClosureExtension.collarRadius_pos)⟩ :
        QYM.FullCertification.P2CuspCollarClosureExtension.CuspBand Y))
  exact
    Topology.IsEmbedding.subtypeVal.codRestrict
      (QYM.FullCertification.P2CuspCollarClosureExtension.CuspBand Y)
      (fun h : OneSidedHeightBand Y =>
        ⟨h.2.1,
          lt_of_le_of_lt h.2.2
            (lt_add_of_pos_right _ QYM.FullCertification.P2CuspCollarClosureExtension.collarRadius_pos)⟩)
""",
        (Header(49515, 2, "Type mismatch: After simplification, term"),),
        "Expose the exact codRestrict function before applying subtypeVal's embedding theorem.",
        "The diagnostic types differ only by the opaque oneSidedHeightToCuspBand function name.",
        "Exact P10 direct topology root 49515.",
    ),
    Rule(
        "stage_boundary_certificate_eta_expand_implicit_level",
        """  exact
    ⟨topologicalStageBoundaryCollarCertificate Y,
      preimage_cuspBandMap_XSet_eq_halfBand,
      preimage_cuspBandMap_frontier_XSet_eq_levelSlice⟩
""",
        """  exact
    ⟨topologicalStageBoundaryCollarCertificate Y,
      (fun q hY =>
        preimage_cuspBandMap_XSet_eq_halfBand q (Y := Y) hY),
      (fun q hY =>
        preimage_cuspBandMap_frontier_XSet_eq_levelSlice q (Y := Y) hY)⟩
""",
        (Header(49819, 6, "Application type mismatch: The argument"),),
        "Eta-expand both certificate fields and pin the implicit stage level to the theorem's explicit Y.",
        "The diagnostic contrasts an implicit {Y} producer with the expected explicit fixed-Y forall field.",
        "Exact P10 direct dependent-function root 49819.",
    ),
    Rule(
        "actual_stage_high_height_proof_skip_noop_dsimp",
        """  let h : QYM.FullCertification.P2CuspCollarClosureExtension.HighHeight :=
    ⟨(1 + Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y) / 2, by
      dsimp only
      linarith⟩
""",
        """  let h : QYM.FullCertification.P2CuspCollarClosureExtension.HighHeight :=
    ⟨(1 + Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y) / 2, by
      linarith⟩
""",
        (Header(49964, 6, "`dsimp` made no progress"),),
        "Apply linear arithmetic directly to the already-exposed subtype proof goal.",
        "The exact diagnostic says dsimp has no work; hY is already the needed strict inequality premise.",
        "Exact P10 direct arithmetic root 49964; structural 50k begins after the hard stop.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
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
                    f"{rule.label}: authority mapping mismatch at "
                    f"{header.line}:{header.column}: "
                    f"headers={len(header_matches)}, diagnostics={len(diagnostic_matches)}"
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
    if len(verified) != 23:
        raise RuntimeError(f"expected 23 direct diagnostics, got {len(verified)}")
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
    name = "_qym_probe12_43k49k_foreign_" + hashlib.sha256(
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
    active_spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(base, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(
                f"own active span count mismatch: {rule.label}: {len(found)}"
            )
        active_spans.extend((start, end, rule.label) for start, end in found)

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

    containment: list[dict[str, str]] = []
    for left in RULES:
        for right in RULES:
            if left.label == right.label:
                continue
            for left_kind, left_anchor in (("old", left.old), ("new", left.new)):
                for right_kind, right_anchor in (("old", right.old), ("new", right.new)):
                    if right_anchor in left_anchor:
                        containment.append(
                            {
                                "container": left.label,
                                "container_variant": left_kind,
                                "contained": right.label,
                                "contained_variant": right_kind,
                            }
                        )
    if overlaps or containment:
        raise RuntimeError(
            f"internal collision: overlaps={overlaps}, containment={containment}"
        )
    return {
        "own_active_spans_checked": len(active_spans),
        "active_span_overlaps": overlaps,
        "cross_variant_containment": containment,
        "pairwise_noninterference": True,
        "forward_order_fixed": True,
        "inverse_order_exact_reverse": True,
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
            raise RuntimeError(f"own collision span mismatch: {rule.label}")
        own_spans.extend((start, end, rule.label) for start, end in found)

    identities: dict[str, dict[str, str]] = {}
    equalities: list[dict[str, str]] = []
    containments: list[dict[str, str]] = []
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
            foreign_active = foreign_new if active_variant == "new" else foreign_old
            found = spans(base, foreign_active)
            if len(found) != expected_count:
                raise RuntimeError(
                    f"foreign active span mismatch: {name}:{foreign_label}: "
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
                            equalities.append(
                                {
                                    "own": own.label,
                                    "own_variant": own_kind,
                                    "foreign_helper": name,
                                    "foreign_rule": foreign_label,
                                    "foreign_variant": foreign_kind,
                                }
                            )
                        elif own_anchor in foreign_anchor or foreign_anchor in own_anchor:
                            containments.append(
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
                    if max(foreign_start, own_start) < min(foreign_end, own_end):
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
            f"foreign family count {foreign_families} != "
            f"{EXPECTED_FOREIGN_RULE_FAMILIES}"
        )
    if equalities or containments or overlaps:
        raise RuntimeError(
            "foreign collision: "
            f"equalities={equalities}, containments={containments}, overlaps={overlaps}"
        )
    return {
        "helper_identities": identities,
        "foreign_rule_families_checked": foreign_families,
        "foreign_active_spans_checked": foreign_spans_checked,
        "own_spans_checked": len(own_spans),
        "exact_anchor_equalities": equalities,
        "cross_variant_containments": containments,
        "active_span_overlaps": overlaps,
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
                f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}"
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
            "probe11_current_seven_helpers_collision_audited": True,
            "probe12_36k42k_sibling_collision_audited": True,
            "probe12_midlate_refinement_collision_audited": True,
            "probe11_40k_owned_lines_excluded": [
                43629,
                44067,
                44069,
                44344,
                44356,
                44416,
                44602,
                45114,
                45529,
                46147,
                46182,
                46183,
                46255,
                46574,
                46996,
            ],
            "inverse_eta_base_bridge_cascade_excluded": [
                47875,
                47960,
                47974,
                47979,
                47982,
                47986,
                47991,
                48032,
                48049,
                48058,
                48066,
                48109,
                48127,
                48212,
                48225,
                48251,
                48260,
                48267,
                48304,
                48321,
                48370,
                48379,
            ],
            "timeout_and_unknown_declaration_cascades_excluded": [
                48672,
                48673,
                48681,
                48682,
                48802,
                48934,
                49007,
                49035,
                49037,
                49059,
                49070,
                49072,
            ],
            "unknown_measure_api_not_guessed": [49919, 49928, 49926],
            "structural_50k_excluded": True,
            "foreign_helper_contract": FOREIGN_HELPERS,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
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
            "coeFn_toLp_precedents": "exact P10 lines 27894-27900 and 28785-28790",
            "integral_moebius_det_pos": "Mock2 FunctionalAnalysis exit-zero lines 40260-40278",
            "eta_ratio_continuity_precedent": "exact P10 lines 41237-41252",
            "horizontal_ofreal_derivative_precedent": "exact P10 lines 34410-34422",
            "typed_action_homeomorph_precedent": "frozen Probe11 40k rule at exact P10 line 42663",
            "withlp_norm_projection_precedents": "Mock2 FunctionalAnalysis exit-zero lines 18922-18940",
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
