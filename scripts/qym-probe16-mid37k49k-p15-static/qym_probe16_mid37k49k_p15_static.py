#!/usr/bin/env python3
"""Activation-disabled, byte-exact Probe15 repairs for direct QYM roots in lines 37k-49k."""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from itertools import permutations
from typing import Iterable, Sequence

sys.dont_write_bytecode = True

SCHEMA = "qym-probe16-mid37k49k-p15-static-v1"
ACTIVATION = False
TARGET_PATH = (
    "scripts/qym-probe16-mid37k49k-p15-static/"
    "qym_probe16_mid37k49k_p15_static.py"
)

AUTHORITY_RUN_ID = 31_992_267_418
AUTHORITY_JOB_ID = 95_277_790_400
AUTHORITY_ARTIFACT_ID = 9_275_890_870
AUTHORITY_COMMIT = "1679e9e9f916e95d5a4fe10f9e59502471c84191"
RESULT_SHA256 = "0254b92c4ce85a80a10f42f6038bf4fd6787411f84bae20a0abc0af638584853"
LOG_SHA256 = "8722d57acddee9696debb88d34a586ba4b28adbf9d2f64ca8b0500198a0db511"
HEADERS_SHA256 = "1c7ad5d2a165913802412602a9e4b37e719ce69bc1da8c0a1b74ad5e5df98381"
DIAGNOSTICS_SHA256 = "54e83aa0f8f792efc92b1a509729001e0049a87bb8ae5705b48792086bf6df58"
AUTHORITY_ERRORS = 100
AUTHORITY_WARNINGS = 350
AUTHORITY_PANICS = 0
AUTHORITY_EXIT = 1

INPUT_SHA256 = "9cd10544c82d5871d1cb336b1816b80c310e8413f051284db0261efcd676c7b6"
INPUT_GIT_BLOB = "c604421ed340e71fe3e24d3a7d391115990882ec"
INPUT_BYTES = 2_941_554
INPUT_LF = 62_190

OUTPUT_SHA256 = "19e13d24617978b7a4932680847e0ae235257b6b2087a5a002f801a7462ada02"
OUTPUT_GIT_BLOB = "c0cd987885babc7dd03d93f82c0f9c00b39901dc"
OUTPUT_BYTES = 2_941_847
OUTPUT_LF = 62_197

EXPECTED_RULES = 7
EXPECTED_OCCURRENCES = 7
EXPECTED_DIRECT_HEADERS = 9
EXPECTED_CASCADE_HEADERS = 0
DECLARED_OVERLAPS = 0


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
    evidence: str
    consumed_owner: str = "exact_p15"
    consumed_rule: str = "none"
    consumed_relation: str = "direct_p15_anchor"
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "trace_projection_opnorm_raise_instance_and_command_heartbeats",
        """set_option synthInstance.maxHeartbeats 200000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖actualFixedPhaseCanonicalTraceClassProjection n Y‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjection_norm_le
""",
        """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖actualFixedPhaseCanonicalTraceClassProjection n Y‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjection_norm_le
""",
        (
            Header(37220, 4, "failed to synthesize instance", "lean.synthInstanceFailed"),
            Header(37220, 4, "maximum heartbeats exceeded"),
        ),
        "Give the existing intrinsic projection API enough elaboration and command time.",
        "Exact P15 has one guarded theorem and reports both instance synthesis and timeout at its body.",
    ),
    Rule(
        "horocycle_contdiff_change_to_upperlift_composition",
        """  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (u : SmoothQuotientCompactFunction)
        (actualFixedPhaseCuspHorocyclePoint kappa Y x))
  simpa only [Function.comp_apply, upperLift_apply] using hcomp
""",
        """  change ContDiff ℝ ∞
    (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
      fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))
  exact hcomp
""",
        (Header(41520, 2, "type mismatch"),),
        "Expose the exact composition already proved by hcomp instead of asking simpa to beta-reduce the lift.",
        "The P15 diagnostic prints hcomp at this exact upperLift composition and the target as its pointwise form.",
    ),
    Rule(
        "hhalf_trace_completion_inner_product_raise_instance_and_command_heartbeats",
        """noncomputable def actualFixedPhaseHhalfTraceCompletionCompleteSpace
    (n : ℤ) (Y : ℝ) :
    CompleteSpace (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance

noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance
""",
        """noncomputable def actualFixedPhaseHhalfTraceCompletionCompleteSpace
    (n : ℤ) (Y : ℝ) :
    CompleteSpace (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance
""",
        (Header(42041, 2, "maximum heartbeats exceeded"),),
        "Bound the expensive but already available completion instance search locally.",
        "The exact P15 root is a bare inferInstance witness and no API or carrier change is required.",
    ),
    Rule(
        "explicit_edge_velocity_unfold_local_addcommgroup",
        """  simpa [explicitActualEdgeCoordinate, explicitActualEdgeVelocity,
    Function.comp_def, hz, ContinuousLinearMap.smul_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hComp
""",
        """  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    explicitActualEdgeCoordinate, explicitActualEdgeVelocity,
    Function.comp_def, hz, ContinuousLinearMap.smul_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hComp
""",
        (Header(43954, 2, "type mismatch"),),
        "Unfold the local canonical Complex additive instance before normalizing the derivative.",
        "The remaining P15 mismatch is instance-generated scalar arithmetic; the local instance is the producer.",
    ),
    Rule(
        "acted_edge_velocity_unfold_local_addcommgroup",
        """    simpa [actedSourceCoordinate, gammaTwoMoebiusChart,
      gammaTwoMoebiusCoordinate, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate,
      QYM.FullCertification.P2NormalGreenExtension.actualEdgeCoordinate, Function.comp_def,
      ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc,
      UpperHalfPlane.ofComplex_apply] using hComp
""",
        """    simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
      actedSourceCoordinate, gammaTwoMoebiusChart,
      gammaTwoMoebiusCoordinate, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate,
      QYM.FullCertification.P2NormalGreenExtension.actualEdgeCoordinate, Function.comp_def,
      ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc,
      UpperHalfPlane.ofComplex_apply] using hComp
""",
        (Header(44087, 4, "type mismatch"),),
        "Normalize the same local Complex additive instance in the acted-coordinate derivative proof.",
        "This is the second direct P15 residual generated by the identical local instance definition.",
    ),
    Rule(
        "paired_transport_velocity_unfold_local_addcommgroup",
        """  simpa [pairedTransportCoordinate, Function.comp_def,
    Complex.real_smul] using hComp
""",
        """  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    pairedTransportCoordinate, Function.comp_def,
    Complex.real_smul] using hComp
""",
        (Header(44117, 2, "type mismatch"),),
        "Normalize the local Complex additive instance before the paired transport beta reduction.",
        "The exact P15 goal and hComp differ only through the same local instance-backed scalar expression.",
    ),
    Rule(
        "eta_quotient_use_mul_inverse_contdiff_api",
        """    exact heta.div hetaShift
      (fun x => ModularForm.eta_ne_zero
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2)
""",
        """    rw [div_eq_mul_inv]
    exact heta.mul (hetaShift.inv
      (fun x => ModularForm.eta_ne_zero
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2))
""",
        (
            Header(44291, 10, "failed to synthesize scalar-valued division instance", "lean.synthInstanceFailed"),
            Header(44291, 19, "application type mismatch"),
        ),
        "Use the Complex-valued multiplication and inverse APIs; ContDiff.div is scalar-valued over the domain field.",
        "The same explicit div_eq_mul_inv plus mul/inv API shape is established in the active P15 ContDiff repair.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    prefix = b"blob " + str(len(raw)).encode("ascii") + bytes((0,))
    return hashlib.sha1(prefix + raw).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "cr": b"\r" in raw,
        "nul": bytes((0,)) in raw,
        "bom": raw.startswith(bytes((0xEF, 0xBB, 0xBF))),
        "terminal_lf": raw.endswith(b"\n"),
    }


def expected_input() -> dict[str, object]:
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


def expected_output() -> dict[str, object]:
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


def _require_shape(raw: bytes, expected: dict[str, object], label: str) -> None:
    actual = shape(raw)
    if actual != expected:
        raise ValueError(f"{label} identity mismatch: expected {expected}, got {actual}")


def _ordered_rules(order: Iterable[int] | None) -> tuple[Rule, ...]:
    if order is None:
        return RULES
    indices = tuple(order)
    if sorted(indices) != list(range(len(RULES))):
        raise ValueError(f"invalid rule order: {indices}")
    return tuple(RULES[index] for index in indices)


def apply_rules(raw: bytes, order: Iterable[int] | None = None) -> bytes:
    _require_shape(raw, expected_input(), "Probe15 input")
    text = raw.decode("utf-8", errors="strict")
    for rule in _ordered_rules(order):
        old_count = text.count(rule.old)
        new_count = text.count(rule.new)
        if old_count != rule.occurrences or new_count != 0:
            raise ValueError(
                f"{rule.label}: expected old={rule.occurrences}, new=0; "
                f"got old={old_count}, new={new_count}"
            )
        text = text.replace(rule.old, rule.new, rule.occurrences)
    output = text.encode("utf-8")
    _require_shape(output, expected_output(), "Probe16 output")
    return output


def inverse_rules(raw: bytes, order: Iterable[int] | None = None) -> bytes:
    _require_shape(raw, expected_output(), "Probe16 output")
    text = raw.decode("utf-8", errors="strict")
    selected = _ordered_rules(order)
    for rule in reversed(selected):
        new_count = text.count(rule.new)
        old_count = text.count(rule.old)
        if new_count != rule.occurrences or old_count != 0:
            raise ValueError(
                f"{rule.label}: expected new={rule.occurrences}, old=0; "
                f"got new={new_count}, old={old_count}"
            )
        text = text.replace(rule.new, rule.old, rule.occurrences)
    restored = text.encode("utf-8")
    _require_shape(restored, expected_input(), "restored Probe15 input")
    return restored


def static_audit() -> dict[str, object]:
    labels = [rule.label for rule in RULES]
    olds = [rule.old for rule in RULES]
    news = [rule.new for rule in RULES]
    if len(RULES) != EXPECTED_RULES:
        raise ValueError("rule count mismatch")
    if len(labels) != len(set(labels)) or len(olds) != len(set(olds)) or len(news) != len(set(news)):
        raise ValueError("duplicate labels or anchors")
    if sum(rule.occurrences for rule in RULES) != EXPECTED_OCCURRENCES:
        raise ValueError("occurrence count mismatch")
    headers = tuple(header for rule in RULES for header in rule.headers)
    direct = tuple(header for header in headers if header.kind == "direct")
    cascades = tuple(header for header in headers if header.kind == "cascade")
    if len(direct) != EXPECTED_DIRECT_HEADERS or len(cascades) != EXPECTED_CASCADE_HEADERS:
        raise ValueError("header count mismatch")
    if any(not 37_000 <= header.line < 50_000 for header in headers):
        raise ValueError("header outside owned 37k-49k tranche")
    if any(rule.old == rule.new for rule in RULES):
        raise ValueError("no-op rule")
    trust_terms = ("sorry", "admit", "axiom", "unsafe")
    trust_hits = [
        (rule.label, term)
        for rule in RULES
        for term in trust_terms
        if term in rule.new.lower()
    ]
    if trust_hits:
        raise ValueError(f"trust-token hits: {trust_hits}")
    cross_collisions = []
    for left_index, left in enumerate(RULES):
        for right_index, right in enumerate(RULES):
            if left_index == right_index:
                continue
            if right.old in left.new or right.new in left.old:
                cross_collisions.append((left.label, right.label))
    if cross_collisions:
        raise ValueError(f"undeclared cross-collisions: {cross_collisions}")
    if ACTIVATION:
        raise ValueError("helper must remain activation-disabled")
    return {
        "schema": SCHEMA,
        "activation": ACTIVATION,
        "rules": len(RULES),
        "occurrences": sum(rule.occurrences for rule in RULES),
        "headers": len(headers),
        "direct_headers": len(direct),
        "cascade_headers": len(cascades),
        "declared_overlaps": DECLARED_OVERLAPS,
        "undeclared_collisions": len(cross_collisions),
        "trust_hits": len(trust_hits),
    }


def exhaustive_audit(raw: bytes) -> dict[str, object]:
    static = static_audit()
    outputs: set[str] = set()
    inverses: set[str] = set()
    orders = 0
    for order in permutations(range(len(RULES))):
        output = apply_rules(raw, order)
        outputs.add(sha256(output))
        inverses.add(sha256(inverse_rules(output, order)))
        orders += 1
    if outputs != {OUTPUT_SHA256}:
        raise ValueError(f"noncommutative forward outputs: {outputs}")
    if inverses != {INPUT_SHA256}:
        raise ValueError(f"noncanonical inverses: {inverses}")
    return {
        **static,
        "orders": orders,
        "unique_forward_outputs": len(outputs),
        "unique_inverse_outputs": len(inverses),
        "input": shape(raw),
        "output": expected_output(),
    }


def manifest() -> dict[str, object]:
    return {
        **static_audit(),
        "target_path": TARGET_PATH,
        "authority": {
            "run_id": AUTHORITY_RUN_ID,
            "job_id": AUTHORITY_JOB_ID,
            "artifact_id": AUTHORITY_ARTIFACT_ID,
            "commit": AUTHORITY_COMMIT,
            "result_sha256": RESULT_SHA256,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": AUTHORITY_ERRORS,
            "warnings": AUTHORITY_WARNINGS,
            "panics": AUTHORITY_PANICS,
            "exit": AUTHORITY_EXIT,
        },
        "input": expected_input(),
        "output": expected_output(),
        "dependencies": [],
        "rule_labels": [rule.label for rule in RULES],
        "headers": [asdict(header) for rule in RULES for header in rule.headers],
    }


def main(argv: Sequence[str] | None = None) -> int:
    if argv not in (None, (), []):
        raise SystemExit("this activation-disabled helper accepts no arguments")
    print(json.dumps(manifest(), ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
