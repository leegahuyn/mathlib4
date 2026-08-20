#!/usr/bin/env python3
"""Conditional exact-P9 repairs for the remaining early and tail QYM roots.

The transformer is byte-locked to the terminal Probe9 authority.  It performs
only static, exact-counted text projections, verifies the corresponding Probe9
diagnostics, audits downstream refinements and anchor collisions with the
already-applied Probe9 and inactive Probe10-midlate helpers, and proves
byte-for-byte reversibility.  It never runs Lean/Lake/Git, touches repository
sources, uses the network, or authorizes activation.
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

SCHEMA = "qym-probe10-earlytail-static-transform-v2"
INPUT_SHA256 = "fb37854ff158ae20a2acebe7722847726eb651ba9c716eff6b903cb4f32e8029"
INPUT_GIT_BLOB = "d29c6aff411f93b3c44d7d866fe2b2558f616a87"
INPUT_BYTES = 2_921_397
INPUT_LF = 61_746
LOG_SHA256 = "e8315f541ddcd8d9f99a395caddbcf57ceb3a1457a900bcefb45422dff81cd0f"
HEADERS_SHA256 = "e8b25cc78d4f2a9915cd25c6c7700f7f80ca73c7f01229fe531e3ef13386186f"
DIAGNOSTICS_SHA256 = "a34f5b424f8aac739ac05ce4375003fe9da7f0ee4689050d4d712c9816f66580"

# Filled from one deterministic bootstrap projection, then enforced in both
# directions.  ``--bootstrap-seal`` is accepted only for that first projection.
OUTPUT_SHA256 = "8c0aa79e298a243690d9cdcfbbfa388deec940dd095787d4c1df1e7180e740e5"
OUTPUT_GIT_BLOB = "5a9304ad8c59300f91a01928f6596bb94d58d463"
OUTPUT_BYTES = 2_922_043
OUTPUT_LF = 61_765

FOREIGN_HELPER_SHA256 = {
    "qym_probe9_early2_static.py":
        "d644233fcbe2f4bdaa9cbe5d9f0fd5b9c6bc5ce19961ebded59122c9113508a3",
    "qym_probe9_frontier_next2.py":
        "1e2074beeb236f8099ea227863547d34c52af7ce7ccfbcd10237479b9be5b11c",
    "qym_probe9_50k_static.py":
        "44b17336ea2cfa089c461e8c23cf25d2de95987e106e8473f2765cb2bf5faab4",
    "qym_probe9_55k_static.py":
        "605fc454aea53613082b357004ed182ac1ec12cc813258640d4904cc054e2d6f",
    "qym_probe9_tail60k_first4.py":
        "d6bf9e829c4bc54528b4abe62b15e631f642ba27e7e699434bc5d548b3630125",
    "qym_probe9_extendofnorm_static.py":
        "2d2fadc115ecf9e1eef0d6b5b58637bdc371a27756b5612db8f64ccf1484afe9",
    "qym_probe10_midlate_static.py":
        "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0",
}

# Probe9 helpers are already projected into the exact Probe9 candidate; the
# Probe10-midlate helper remains conditional and therefore contributes its old
# spans.  This explicit state avoids guessing from substring counts.
FOREIGN_HELPER_STATE = {
    "qym_probe9_early2_static.py": "applied_new",
    "qym_probe9_frontier_next2.py": "applied_new",
    "qym_probe9_50k_static.py": "applied_new",
    "qym_probe9_55k_static.py": "applied_new",
    "qym_probe9_tail60k_first4.py": "applied_new",
    "qym_probe9_extendofnorm_static.py": "applied_new",
    "qym_probe10_midlate_static.py": "inactive_old",
}

# These are not competing edits.  They are exact downstream corrections of
# Probe9 quotient rules whose new text elaborated far enough to expose residual
# Setoid errors.  The adjacent eta MemLp coercion cascade does not share an
# anchor span.  Every undeclared overlap is rejected.
AUTHORIZED_CASCADE_OVERLAPS = {
    (
        "quotient_map_measurable_pin_explicit_setoid",
        "qym_probe9_early2_static.py",
        "quotient_map_measurable_supply_orbit_setoid",
    ),
    (
        "quotient_map_surjective_pin_explicit_setoid",
        "qym_probe9_early2_static.py",
        "quotient_map_surjective_supply_orbit_setoid",
    ),
}


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str
    code: str | None = None
    kind: str = "direct"


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    rationale: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "raw_differential_use_vector_valued_manifold_derivative",
        "noncomputable def rawDifferential\n"
        "    (g : SmoothInvariantScalar) (τ : H) : ScalarOneFormValue :=\n"
        "  mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 τ\n"
        "\n"
        "/-- Chain-rule invariance of `dg`: `deckPullback(dg) = dg`. -/\n"
        "theorem rawDifferential_deck_comp\n"
        "    (g : SmoothInvariantScalar) (γ : Gamma2) (τ : H) :\n"
        "    (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =\n"
        "      rawDifferential g τ := by\n"
        "  have hgAt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 (γ • τ) :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) (γ • τ)\n"
        "  have hdeckAt :\n"
        "      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (manifoldDeckMap γ) τ :=\n"
        "    (manifoldDeckMap_smooth γ).mdifferentiable (by simp) τ\n"
        "  have hfun : g.1 ∘ manifoldDeckMap γ = g.1 := by\n"
        "    funext σ\n"
        "    exact SmoothInvariantScalar.invariant g γ σ\n"
        "  calc\n"
        "    (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =\n"
        "        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :\n"
        "          ScalarOneFormValue) := by\n"
        "      symm\n"
        "      simpa only [rawDifferential, manifoldDeckDerivative, manifoldDeckMap]\n"
        "        using mfderiv_comp τ hgAt hdeckAt\n"
        "    _ = rawDifferential g τ := by\n"
        "      simpa only [rawDifferential] using\n"
        "        (mfderiv_congr (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (x := τ) hfun)\n"
        "\n"
        "theorem rawDifferential_add\n"
        "    (g h : SmoothInvariantScalar) (τ : H) :\n"
        "    rawDifferential (g + h) τ =\n"
        "      rawDifferential g τ + rawDifferential h τ := by\n"
        "  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ\n"
        "  have hh : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth h).mdifferentiable (by simp)) τ\n"
        "  change (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 + h.1) τ :\n"
        "      ScalarOneFormValue) =\n"
        "    (mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 τ : ScalarOneFormValue) +\n"
        "      (mfderiv 𝓘(ℂ) 𝓘(ℂ) h.1 τ : ScalarOneFormValue)\n"
        "  exact mfderiv_add hg hh\n",
        "noncomputable def rawDifferential\n"
        "    (g : SmoothInvariantScalar) (τ : H) : ScalarOneFormValue :=\n"
        "  mvfderiv 𝓘(ℂ) g.1 τ\n"
        "\n"
        "/-- Chain-rule invariance of `dg`: `deckPullback(dg) = dg`. -/\n"
        "theorem rawDifferential_deck_comp\n"
        "    (g : SmoothInvariantScalar) (γ : Gamma2) (τ : H) :\n"
        "    (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =\n"
        "      rawDifferential g τ := by\n"
        "  have hgAt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 (γ • τ) :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) (γ • τ)\n"
        "  have hdeckAt :\n"
        "      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (manifoldDeckMap γ) τ :=\n"
        "    (manifoldDeckMap_smooth γ).mdifferentiable (by simp) τ\n"
        "  have hfun : g.1 ∘ manifoldDeckMap γ = g.1 := by\n"
        "    funext σ\n"
        "    exact SmoothInvariantScalar.invariant g γ σ\n"
        "  calc\n"
        "    (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =\n"
        "        mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ := by\n"
        "      symm\n"
        "      simpa only [rawDifferential, manifoldDeckDerivative, manifoldDeckMap]\n"
        "        using mvfderiv_comp τ hgAt hdeckAt\n"
        "    _ = rawDifferential g τ := by\n"
        "      simpa only [rawDifferential, hfun]\n"
        "\n"
        "theorem rawDifferential_add\n"
        "    (g h : SmoothInvariantScalar) (τ : H) :\n"
        "    rawDifferential (g + h) τ =\n"
        "      rawDifferential g τ + rawDifferential h τ := by\n"
        "  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ\n"
        "  have hh : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth h).mdifferentiable (by simp)) τ\n"
        "  change mvfderiv 𝓘(ℂ) (g.1 + h.1) τ =\n"
        "    mvfderiv 𝓘(ℂ) g.1 τ + mvfderiv 𝓘(ℂ) h.1 τ\n"
        "  exact mvfderiv_add hg hh\n",
        (
            Header(28363, 4, "invalid 'calc' step, failed to synthesize `Trans` instance"),
            Header(
                28377,
                4,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
            ),
        ),
        "Use Mathlib's value-space manifold derivative API. mvfderiv_comp removes the dependent target equality and mvfderiv_add supplies an ordinary CLM HAdd.",
    ),
    Rule(
        "raw_differential_smul_follow_mvfderiv",
        "theorem rawDifferential_smul\n"
        "    (c : ℂ) (g : SmoothInvariantScalar) (τ : H) :\n"
        "    rawDifferential (c • g) τ = c • rawDifferential g τ := by\n"
        "  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ\n"
        "  change mfderiv 𝓘(ℂ) 𝓘(ℂ) (c • g.1) τ =\n"
        "    c • mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 τ\n"
        "  exact const_smul_mfderiv hg c\n",
        "theorem rawDifferential_smul\n"
        "    (c : ℂ) (g : SmoothInvariantScalar) (τ : H) :\n"
        "    rawDifferential (c • g) τ = c • rawDifferential g τ := by\n"
        "  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 τ :=\n"
        "    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ\n"
        "  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)\n"
        "      (fun _ : H => c) τ :=\n"
        "    (contMDiff_const.mdifferentiable (by simp)) τ\n"
        "  simpa [rawDifferential, mvfderiv_const] using\n"
        "    (mvfderiv_smul hc hg)\n",
        (),
        "Supporting edit forced by the rawDifferential producer change: specialize mvfderiv_smul to the constant scalar function and discharge its zero derivative.",
    ),
    Rule(
        "raw_differential_constant_follow_mvfderiv",
        "theorem rawDifferential_constantOne (tau : H) :\n"
        "    rawDifferential constantOneInvariant tau = 0 := by\n"
        "  simp only [rawDifferential, constantOneInvariant, mfderiv_const]\n"
        "  rfl\n",
        "theorem rawDifferential_constantOne (tau : H) :\n"
        "    rawDifferential constantOneInvariant tau = 0 := by\n"
        "  simpa only [rawDifferential, constantOneInvariant] using\n"
        "    (mvfderiv_const (I := 𝓘(ℂ)) (c := (1 : ℂ)) (x := tau))\n",
        (),
        "Supporting edit forced by the rawDifferential producer change: use the value-space constant derivative theorem directly.",
    ),
    Rule(
        "quotient_map_measurable_pin_explicit_setoid",
        "  change Measurable\n"
        "    (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))\n"
        "  exact measurable_quotient_mk'\n",
        "  change Measurable\n"
        "    (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))\n"
        "  exact\n"
        "    @measurable_quotient_mk' H _\n"
        "      (MulAction.orbitRel Gamma2 H)\n",
        (
            Header(
                29120,
                8,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
                "direct_downstream_cascade",
            ),
        ),
        "The Probe9 change exposed the exact orbit-relation quotient but left the theorem's Setoid instance implicit. Pin the current measurable_quotient_mk' instance argument explicitly.",
    ),
    Rule(
        "quotient_map_surjective_pin_explicit_setoid",
        "  change Function.Surjective\n"
        "    (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))\n"
        "  exact Quotient.mk'_surjective\n",
        "  change Function.Surjective\n"
        "    (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))\n"
        "  exact\n"
        "    @Quotient.mk'_surjective H\n"
        "      (MulAction.orbitRel Gamma2 H)\n",
        (
            Header(
                29130,
                8,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
                "direct_downstream_cascade",
            ),
        ),
        "The corresponding surjectivity theorem also carries the Setoid as an instance argument; instantiate the same exact orbit relation explicitly.",
    ),
    Rule(
        "eta_memlp_norm_nonneg_unwrap_subtype",
        "          (hC ⟨tau, htau, rfl⟩) (norm_nonneg (f tau)))\n",
        "          (hC ⟨tau, htau, rfl⟩)\n"
        "            (norm_nonneg ((f : H → ℂ) tau)))\n",
        (
            Header(
                29375,
                46,
                "Function expected at",
                kind="direct_downstream_cascade",
            ),
        ),
        "Probe9 fixed the MemLp bound constant; the remaining error is only the eta-core subtype not being coerced before application. Reuse the explicit H-to-complex coercion already used in this section.",
    ),
    Rule(
        "eta_total_reexpose_exact_quotient_measurable_space",
        "/-! ## Descent to the actual associated eta line bundle -/\n"
        "\n"
        "/-- The inverse-eta bundle lift is measurable as a map to Mock2's actual\n",
        "/-! ## Descent to the actual associated eta line bundle -/\n"
        "\n"
        "/-- Re-expose the measurable structure of the exact associated-orbit\n"
        "quotient before stating measurable bundle-valued maps. -/\n"
        "noncomputable local instance etaAutomorphicLineBundleTotalMeasurableSpace :\n"
        "    MeasurableSpace EtaAutomorphicLineBundle.Total := by\n"
        "  change MeasurableSpace\n"
        "    (Quotient (Mock2.Definition15Geometry.lineOrbitRel etaMultiplier))\n"
        "  infer_instance\n"
        "\n"
        "/-- The inverse-eta bundle lift is measurable as a map to Mock2's actual\n",
        (
            Header(29472, 4, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(29473, 9, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(29510, 4, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(29519, 4, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(29520, 9, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(29558, 4, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        ),
        "Use the same exact Quotient(lineOrbitRel etaMultiplier) measurable-space producer that is already accepted later in QYM, before any Measurable statement needs it.",
    ),
    Rule(
        "inverse_eta_lift_supply_line_orbit_setoid",
        "  change Measurable\n"
        "    (fun tau : H =>\n"
        "      (Quotient.mk' (tau, inverseEtaSection tau) :\n"
        "        EtaAutomorphicLineBundle.Total))\n"
        "  exact measurable_quotient_mk'.comp\n"
        "    (measurable_id.prodMk inverseEtaSection_continuous.measurable)\n",
        "  change Measurable\n"
        "    (fun tau : H =>\n"
        "      (@Quotient.mk' (H × ℂ)\n"
        "        (Mock2.Definition15Geometry.lineOrbitRel etaMultiplier)\n"
        "        (tau, inverseEtaSection tau)))\n"
        "  exact\n"
        "    (@measurable_quotient_mk' (H × ℂ) _\n"
        "      (Mock2.Definition15Geometry.lineOrbitRel etaMultiplier)).comp\n"
        "      (measurable_id.prodMk inverseEtaSection_continuous.measurable)\n",
        (
            Header(29475, 7, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(29477, 8, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        ),
        "Supply the exact lineOrbitRel setoid to Quotient.mk' and to measurable_quotient_mk' rather than asking inference to recover it through an opaque associated-bundle abbreviation.",
    ),
    Rule(
        "eta_core_lift_supply_line_orbit_setoid",
        "  change Measurable\n"
        "    (fun tau : H =>\n"
        "      (Quotient.mk' (tau, (f : H → ℂ) tau) : EtaAutomorphicLineBundle.Total))\n"
        "  exact measurable_quotient_mk'.comp\n"
        "    (measurable_id.prodMk f.property.1.continuous.measurable)\n",
        "  change Measurable\n"
        "    (fun tau : H =>\n"
        "      (@Quotient.mk' (H × ℂ)\n"
        "        (Mock2.Definition15Geometry.lineOrbitRel etaMultiplier)\n"
        "        (tau, (f : H → ℂ) tau)))\n"
        "  exact\n"
        "    (@measurable_quotient_mk' (H × ℂ) _\n"
        "      (Mock2.Definition15Geometry.lineOrbitRel etaMultiplier)).comp\n"
        "      (measurable_id.prodMk f.property.1.continuous.measurable)\n",
        (
            Header(29522, 7, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(29523, 8, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        ),
        "Supply the same exact associated-line orbit setoid for general eta-core lifts.",
    ),
    Rule(
        "lower_unipotent_inverse_action_use_group_law",
        "@[simp] theorem gammaLower_inv_smul_lowPoint :\n"
        "    (Mock2.Definition11.gammaLowerInGamma2)⁻¹ • lowPoint =\n"
        "      UpperHalfPlane.I := by\n"
        "  simp [lowPoint]\n",
        "@[simp] theorem gammaLower_inv_smul_lowPoint :\n"
        "    (Mock2.Definition11.gammaLowerInGamma2)⁻¹ • lowPoint =\n"
        "      UpperHalfPlane.I := by\n"
        "  simpa only [lowPoint, inv_smul_smul]\n",
        (Header(29663, 26, "unsolved goals"),),
        "Expose lowPoint and invoke the exact group-action inverse law already used repeatedly in the same QYM candidate.",
    ),
    Rule(
        "negative_one_resolvent_error_normalize_at_clm_level",
        "theorem actualCutoffNegativeOneResolventError_eq_half_escape\n"
        "    (n : ℕ) :\n"
        "    actualCutoffNegativeOneResolventError n =\n"
        "      (1 / 2 : ℂ) • QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffEscapeHamiltonian n := by\n"
        "  ext u\n"
        "  rw [actualCutoffNegativeOneResolventError,\n"
        "    ContinuousLinearMap.sub_apply,\n"
        "    QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffNegativeOneResolvent_apply,\n"
        "    QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffLimitNegativeOneResolvent_apply,\n"
        "    ContinuousLinearMap.smul_apply,\n"
        "    QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffEscapeHamiltonian_apply]\n"
        "  module\n",
        "theorem actualCutoffNegativeOneResolventError_eq_half_escape\n"
        "    (n : ℕ) :\n"
        "    actualCutoffNegativeOneResolventError n =\n"
        "      (1 / 2 : ℂ) • QYM.FullCertification.Mock3ActualMockRSResolventUniformGapExtension.actualCutoffEscapeHamiltonian n := by\n"
        "  change\n"
        "    (-(1 / 2 : ℂ)) •\n"
        "          (ContinuousLinearMap.id ℂ ActualGlobalL2 +\n"
        "            QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n) -\n"
        "        (-(ContinuousLinearMap.id ℂ ActualGlobalL2)) =\n"
        "      (1 / 2 : ℂ) •\n"
        "        (ContinuousLinearMap.id ℂ ActualGlobalL2 -\n"
        "          QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n)\n"
        "  module\n",
        (Header(61203, 2, "ring failed, ring expressions not equal"),),
        "Unfold the three defining CLM expressions through change and prove the exact coefficient identity -1/2(I+P)-(-I)=1/2(I-P) before application rewrites can distort normalization.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw
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
    allow_unsealed: bool,
) -> None:
    if wanted[0] != "__TO_SEAL__" or not allow_unsealed:
        for key, value in zip(
            ("sha256", "git_blob", "bytes", "lf"), wanted, strict=True
        ):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_authority(
    log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes
) -> list[dict[str, object]]:
    if sha256(log_raw) != LOG_SHA256:
        raise RuntimeError("Probe9 log identity mismatch")
    if sha256(header_raw) != HEADERS_SHA256:
        raise RuntimeError("Probe9 error-header identity mismatch")
    if sha256(diagnostics_raw) != DIAGNOSTICS_SHA256:
        raise RuntimeError("Probe9 diagnostics identity mismatch")
    log_text = log_raw.decode("utf-8", errors="strict")
    artifact_headers = header_raw.decode("utf-8", errors="strict").splitlines()
    log_headers = [
        line
        for line in log_text.splitlines()
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if artifact_headers != log_headers or len(artifact_headers) != 287:
        raise RuntimeError("Probe9 log/header inventory mismatch")
    warning_count = len(
        re.findall(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"warning(?:\([^)]*\))?: ",
            log_text,
            re.MULTILINE,
        )
    )
    if warning_count != 361:
        raise RuntimeError(f"Probe9 warning count {warning_count} != 361")
    diagnostics = [
        json.loads(line)
        for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()
        if line
    ]
    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            matches = [
                item
                for item in diagnostics
                if item.get("file") == "PrimalitySheafVerification/QYM.lean"
                and item.get("severity") == "error"
                and item.get("line") == header.line
                and item.get("column") == header.column
                and str(item.get("message", "")).startswith(header.message)
                and (header.code is None or item.get("code") == header.code)
            ]
            if len(matches) != 1:
                raise RuntimeError(
                    f"{rule.label}: diagnostic mapping mismatch at "
                    f"{header.line}:{header.column}"
                )
            verified.append(
                {
                    "rule": rule.label,
                    "line": header.line,
                    "column": header.column,
                    "code": header.code,
                    "message": header.message,
                    "kind": header.kind,
                }
            )
    return verified


def apply_rules(
    text: str, inverse: bool = False
) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    rules = tuple(reversed(RULES)) if inverse else RULES
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
            }
        )
    return text, audit


# Compatibility alias for later tranche integrators.
transform = apply_rules


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        offset = text.find(needle, start)
        if offset < 0:
            return found
        found.append((offset, offset + len(needle)))
        start = offset + 1


def load_helper(path: Path) -> ModuleType:
    module_name = "_qym_foreign_" + hashlib.sha256(
        str(path).encode("utf-8")
    ).hexdigest()
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def audit_foreign_spans(base: str, paths: list[Path]) -> dict[str, object]:
    by_name = {path.name: path for path in paths}
    if set(by_name) != set(FOREIGN_HELPER_SHA256):
        raise RuntimeError("foreign helper set is not the exact sealed comparison set")
    if set(FOREIGN_HELPER_STATE) != set(FOREIGN_HELPER_SHA256):
        raise RuntimeError("foreign helper state inventory mismatch")
    own = [
        (start, end, rule.label)
        for rule in RULES
        for start, end in spans(base, rule.old)
    ]
    if len(own) != sum(rule.occurrences for rule in RULES):
        raise RuntimeError("own source-span inventory mismatch")
    identities: dict[str, str] = {}
    states: dict[str, str] = {}
    authorized_overlaps: list[dict[str, object]] = []
    undeclared_overlaps: list[dict[str, object]] = []
    exact_equalities = 0
    foreign_count = 0
    own_anchors = {value for rule in RULES for value in (rule.old, rule.new)}
    for name, expected_sha in FOREIGN_HELPER_SHA256.items():
        path = by_name[name]
        digest = sha256(path.read_bytes())
        if digest != expected_sha:
            raise RuntimeError(f"foreign helper identity mismatch: {name}")
        identities[name] = digest
        module = load_helper(path)
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        state = FOREIGN_HELPER_STATE[name]
        if state not in {"applied_new", "inactive_old"}:
            raise RuntimeError(f"invalid foreign helper state: {name}: {state}")
        states[name] = state
        for foreign_rule in foreign_rules:
            foreign_count += 1
            old = getattr(foreign_rule, "old")
            new = getattr(foreign_rule, "new")
            exact_equalities += int(old in own_anchors) + int(new in own_anchors)
            selected = new if state == "applied_new" else old
            matches = spans(base, selected)
            wanted = getattr(foreign_rule, "occurrences", 1)
            if len(matches) != wanted:
                raise RuntimeError(
                    f"foreign exact-P9 state anchor count mismatch: {name}:"
                    f"{getattr(foreign_rule, 'label')}: {len(matches)} != {wanted}"
                )
            for fstart, fend in matches:
                for ostart, oend, own_label in own:
                    if max(fstart, ostart) < min(fend, oend):
                        triple = (
                            own_label,
                            name,
                            getattr(foreign_rule, "label"),
                        )
                        item = {
                            "own": triple[0],
                            "foreign_helper": triple[1],
                            "foreign_rule": triple[2],
                            "foreign_state": state,
                        }
                        if triple in AUTHORIZED_CASCADE_OVERLAPS:
                            authorized_overlaps.append(item)
                        else:
                            undeclared_overlaps.append(item)
    observed_authorized = {
        (item["own"], item["foreign_helper"], item["foreign_rule"])
        for item in authorized_overlaps
    }
    if observed_authorized != AUTHORIZED_CASCADE_OVERLAPS:
        raise RuntimeError(
            "authorized cascade overlap inventory mismatch: "
            f"{observed_authorized} != {AUTHORIZED_CASCADE_OVERLAPS}"
        )
    if exact_equalities != len(AUTHORIZED_CASCADE_OVERLAPS):
        raise RuntimeError(
            "exact anchor equality inventory mismatch: "
            f"{exact_equalities} != {len(AUTHORIZED_CASCADE_OVERLAPS)}"
        )
    if undeclared_overlaps:
        raise RuntimeError(
            "foreign collision: "
            f"equalities={exact_equalities}, undeclared={undeclared_overlaps}"
        )
    return {
        "foreign_helper_sha256": identities,
        "foreign_helper_state": states,
        "foreign_rule_families_checked": foreign_count,
        "own_spans_checked": len(own),
        "authorized_exact_anchor_equalities": exact_equalities,
        "undeclared_exact_anchor_equalities": 0,
        "authorized_downstream_cascade_overlaps": authorized_overlaps,
        "undeclared_span_overlaps": undeclared_overlaps,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe9-log", type=Path, required=True)
    parser.add_argument("--probe9-error-headers", type=Path, required=True)
    parser.add_argument("--probe9-diagnostics", type=Path, required=True)
    parser.add_argument("--foreign-helper", type=Path, action="append", required=True)
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
        args.probe9_log.read_bytes(),
        args.probe9_error_headers.read_bytes(),
        args.probe9_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    collision_base = source_text
    if inverse:
        collision_base, _ = apply_rules(source_text, inverse=True)
    collision_audit = audit_foreign_spans(collision_base, args.foreign_helper)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored_text, _ = apply_rules(result_text, not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE9_AUTHORITY_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe9_run_id": 31971447929,
            "probe9_artifact_directory":
                "work/qym-probe9-run31971447929-authority/artifact",
            "probe9_result_sha256":
                "aeda853726579f5a6185b5e3e740bb131f36d9ce73464582c96e0298e057e3d8",
            "github_sha": "3b5e67d81c4d8979f2c4b57c9f2b7839b0806388",
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 287,
            "warnings": 361,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_line_ranges": [[28000, 29999], [60000, 61746]],
            "excluded_active_probe9_probe8_diagnostic_lines": [
                25161, 25170, 25203, 29115, 29125, 29237, 29306,
                29351, 29363, 29837, 29883, 29898, 29903, 29940,
                61034, 61038, 61152, 61335,
            ],
            "downstream_cascade_lines_modified": [29120, 29130, 29375],
            "cascade_overlap_policy":
                "two exact declared Probe9-early2 overlaps; one adjacent cascade",
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(diagnostic_map),
        "diagnostic_map": diagnostic_map,
        "rules": rule_audit,
        "selected_exact_probe9_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "foreign_anchor_collision_audit": collision_audit,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "static_evidence": {
            "mvfderiv_source":
                "Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean",
            "mvfderiv_value_space_target": True,
            "mvfderiv_comp_signature_verified": True,
            "mvfderiv_add_signature_verified": True,
            "mvfderiv_smul_signature_verified": True,
            "mvfderiv_const_signature_verified": True,
            "measurable_quotient_mk_instance_signature_verified": True,
            "quotient_mk_surjective_instance_signature_verified": True,
            "later_exact_quotient_measurable_instance_lines": [47613, 47617],
            "existing_inv_smul_smul_qym_lines": [34452, 38510, 49197],
            "resolvent_clm_coefficient_identity":
                "-1/2*(I+P)-(-I)=1/2*(I-P)",
        },
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
    args.audit.write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
