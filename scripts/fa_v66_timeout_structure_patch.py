#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

BASE_SHA256 = "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b"
BASE_BYTES = 2813986
BASE_LINES = 62963

VARIANTS: dict[str, dict[str, object]] = {
    "hb400_all": {"hb": 400_000, "dependent": False, "norm_direct": False},
    "hb800_all": {"hb": 800_000, "dependent": False, "norm_direct": False},
    "hb1600_all": {"hb": 1_600_000, "dependent": False, "norm_direct": False},
    "hb3200_all": {"hb": 3_200_000, "dependent": False, "norm_direct": False},
    "dep_hb400": {"hb": 400_000, "dependent": True, "norm_direct": False},
    "dep_hb800": {"hb": 800_000, "dependent": True, "norm_direct": False},
    "dep_hb1600": {"hb": 1_600_000, "dependent": True, "norm_direct": False},
    "dep_hb3200": {"hb": 3_200_000, "dependent": True, "norm_direct": False},
    "dep_norm_hb800": {"hb": 800_000, "dependent": True, "norm_direct": True},
    "dep_norm_hb1600": {"hb": 1_600_000, "dependent": True, "norm_direct": True},
}

TARGETS = (
    "theorem discriminantHardStageOperator_eq_weightedHard\n",
    "theorem weightedFull_sub_weightedHard_eq_weightedTail\n",
    "theorem norm_discriminantHardStageOperator_sub_graphPotential_le\n",
    "theorem graphPotentialOperator_isCompact_unconditional (n : ℤ) :\n",
)

OLD_NORM = '''theorem norm_discriminantHardStageOperator_sub_graphPotential_le
    (N : ℕ) (n : ℤ) :
    ‖discriminantHardStageOperator N n - graphPotentialOperator n‖ ≤
      discriminantCuspEpsilon N := by
  rw [graphPotentialOperator_eq_weightedFull]
  have hsplit := weightedFull_sub_weightedHard_eq_weightedTail N n
  calc
    ‖discriminantHardStageOperator N n -
        weightedGraphOperator n discriminantFullCarrierWeightLp‖ =
      ‖-(weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n)‖ := by
        congr 1
        abel
    _ = ‖weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n‖ := norm_neg _
    _ = ‖weightedGraphOperator n
        (discriminantTailCarrierWeightLp N)‖ := congrArg norm hsplit
    _ ≤ discriminantCuspEpsilon N :=
      (norm_weightedGraphOperator_le n
        (discriminantTailCarrierWeightLp N)).trans
          (norm_discriminantTailCarrierWeightLp_le N)
'''

NEW_NORM = '''theorem norm_discriminantHardStageOperator_sub_graphPotential_le
    (N : ℕ) (n : ℤ) :
    ‖discriminantHardStageOperator N n - graphPotentialOperator n‖ ≤
      discriminantCuspEpsilon N := by
  rw [graphPotentialOperator_eq_weightedFull]
  have hsplit := weightedFull_sub_weightedHard_eq_weightedTail N n
  have hop :
      discriminantHardStageOperator N n -
          weightedGraphOperator n discriminantFullCarrierWeightLp =
        -weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
    calc
      discriminantHardStageOperator N n -
          weightedGraphOperator n discriminantFullCarrierWeightLp =
        -(weightedGraphOperator n discriminantFullCarrierWeightLp -
          discriminantHardStageOperator N n) := by abel
      _ = -weightedGraphOperator n (discriminantTailCarrierWeightLp N) :=
        congrArg (fun T => -T) hsplit
  rw [hop, norm_neg]
  exact (norm_weightedGraphOperator_le n
    (discriminantTailCarrierWeightLp N)).trans
      (norm_discriminantTailCarrierWeightLp_le N)
'''

OLD_COMPACT = '''theorem graphPotentialOperator_isCompact_unconditional (n : ℤ) :
    IsCompactOperator
      (ExplicitDiscriminantPotential.FixedPhaseGraphPotential.graphPotentialOperator n) := by
  exact graphPotentialOperator_isCompact_of_literalStageFactorization n
    (fun N ↦ graphLiteralStageRestriction
      (discriminantHardLiteralStage N) n)
    (fun N ↦ discriminantHardStagePotentialPairing N n)
    (fun N ↦ graphLiteralStageRestriction_isCompact_unconditional
      (discriminantHardLiteralStage N) n)
    (fun N ↦ by
      simpa only [discriminantHardStageOperator] using
        norm_discriminantHardStageOperator_sub_graphPotential_le N n)
'''

DEPENDENT_HELPER_AND_COMPACT = '''theorem graphPotentialOperator_isCompact_of_dependentLiteralStageFactorization
    (n : ℤ)
    {E : ℕ → Type*}
    [∀ N, NormedAddCommGroup (E N)]
    [∀ N, NormedSpace ℂ (E N)]
    (stageRestriction : ∀ N, GraphSobolevCompletion n →L[ℂ] E N)
    (stagePotentialPairing : ∀ N,
      E N →L[ℂ] StrongAntiDual (GraphSobolevCompletion n))
    (hStage : ∀ N, IsCompactOperator (stageRestriction N))
    (hTail : ∀ N,
      ‖(stagePotentialPairing N).comp (stageRestriction N) -
          graphPotentialOperator n‖ ≤ discriminantCuspEpsilon N) :
    IsCompactOperator (graphPotentialOperator n) := by
  apply isCompactOperator_of_tendsto (l := (Filter.atTop : Filter ℕ))
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero
      (fun N ↦ norm_nonneg
        ((stagePotentialPairing N).comp (stageRestriction N) -
          graphPotentialOperator n))
      hTail discriminantCuspEpsilon_tendsto_zero
  · exact Filter.Eventually.of_forall fun N ↦
      (hStage N).clm_comp (stagePotentialPairing N)

/-- Final P5 endpoint: the actual pointwise scalar discriminant potential is
compact from the fixed-phase graph completion to its strong anti-dual.  The
proof uses finite-rank physical Fourier projections on literal cusp-height
stages and the explicit discriminant cusp tail; there is no abstract Rellich
certificate, no rank-one replacement, and no residual hypothesis. -/
theorem graphPotentialOperator_isCompact_unconditional (n : ℤ) :
    IsCompactOperator
      (ExplicitDiscriminantPotential.FixedPhaseGraphPotential.graphPotentialOperator n) := by
  exact graphPotentialOperator_isCompact_of_dependentLiteralStageFactorization n
    (E := fun N ↦ P5PhysicalHardStageRestriction.LiteralStageL2
      (discriminantHardLiteralStage N))
    (fun N ↦ graphLiteralStageRestriction
      (discriminantHardLiteralStage N) n)
    (fun N ↦ discriminantHardStagePotentialPairing N n)
    (fun N ↦ graphLiteralStageRestriction_isCompact_unconditional
      (discriminantHardLiteralStage N) n)
    (fun N ↦ by
      simpa only [discriminantHardStageOperator] using
        norm_discriminantHardStageOperator_sub_graphPotential_le N n)
'''


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise AssertionError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new, 1)


def insert_option(text: str, target: str, heartbeats: int) -> str:
    return replace_once(
        text,
        target,
        f"set_option maxHeartbeats {heartbeats} in\n{target}",
        f"heartbeat target {target.strip()}",
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", choices=sorted(VARIANTS), required=True)
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--audit", type=Path, required=True)
    ns = ap.parse_args()

    raw = ns.input.read_bytes()
    if sha(raw) != BASE_SHA256 or len(raw) != BASE_BYTES:
        raise AssertionError("base source identity mismatch")
    text = raw.decode("utf-8")
    if len(text.splitlines()) != BASE_LINES:
        raise AssertionError("base source line count mismatch")

    cfg = VARIANTS[ns.variant]
    hb = int(cfg["hb"])
    dependent = bool(cfg["dependent"])
    norm_direct = bool(cfg["norm_direct"])

    if norm_direct:
        text = replace_once(text, OLD_NORM, NEW_NORM, "norm theorem")

    if dependent:
        text = replace_once(
            text,
            '''/-- Final P5 endpoint: the actual pointwise scalar discriminant potential is
compact from the fixed-phase graph completion to its strong anti-dual.  The
proof uses finite-rank physical Fourier projections on literal cusp-height
stages and the explicit discriminant cusp tail; there is no abstract Rellich
certificate, no rank-one replacement, and no residual hypothesis. -/
''' + OLD_COMPACT,
            DEPENDENT_HELPER_AND_COMPACT,
            "dependent compactness helper",
        )

    for target in TARGETS:
        text = insert_option(text, target, hb)

    out = text.encode("utf-8")
    if any(token in text for token in ("\nsorry\n", "\nadmit\n", "\naxiom ", "native_decide", "Lean.ofReduceBool")):
        raise AssertionError("forbidden proof token introduced")
    ns.output.parent.mkdir(parents=True, exist_ok=True)
    ns.output.write_bytes(out)
    audit = {
        "schema": "fa-v66-timeout-structure-matrix-v1",
        "variant": ns.variant,
        "base_sha256": BASE_SHA256,
        "candidate_sha256": sha(out),
        "candidate_bytes": len(out),
        "candidate_lines": len(text.splitlines()),
        "heartbeat": hb,
        "dependent_compactness_helper": dependent,
        "norm_proof_restructured": norm_direct,
        "public_existing_theorem_statements_changed": False,
        "new_helper_added": dependent,
    }
    ns.audit.parent.mkdir(parents=True, exist_ok=True)
    ns.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
