#!/usr/bin/env python3
"""Activation-disabled exact-P16 repairs for seven edge-derivative diagnostics."""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from typing import Iterable, Sequence

sys.dont_write_bytecode = True

SCHEMA = "qym-probe17-edge-derivatives-exact-p16-v1"
ACTIVATION = False
TARGET_PATH = (
    "scripts/qym-probe17-edge-derivatives-p16-static/"
    "qym_probe17_edge_derivatives_p16_static.py"
)

AUTHORITY_RUN_ID = 31_996_603_368
AUTHORITY_JOB_ID = 95_289_278_009
AUTHORITY_ARTIFACT_ID = 9_277_193_984
AUTHORITY_COMMIT = "51ff9610af6858e740d18af171e72ffb2b858012"
AUTHORITY_ZIP_SHA256 = "d8745c0ae8cf0ed77f3a62ab2b5d9e46b2f7f4cccc66d92fab09d989dcdee07e"
RESULT_SHA256 = "d1e5f9ce3f015efb897f833fc8fd2be542b3644a1b3cddcdfdd5941dc818ad28"
LOG_SHA256 = "e431025fc146210a46b57a7110628669ddeeba44851bd08554434349ede8ed7d"
HEADERS_SHA256 = "599242fc95fa6881c49f1ac896713aebb2a02f9a5ba702953b69805c22158e65"
DIAGNOSTICS_SHA256 = "8e8acac443ac100091b8a59fbc608bcc2155f0036d7f70563eab2542f6e02a4c"
AUTHORITY_ERRORS = 98
AUTHORITY_WARNINGS = 357
AUTHORITY_PANICS = 0
AUTHORITY_EXIT = 1

INPUT_SHA256 = "19e68721a055a4131d7873fe37ee02509565bb4e0f202c74b646cba2275aba74"
INPUT_GIT_BLOB = "5d8def67719cdb3a7471c33aa320fafbf44ff186"
INPUT_BYTES = 2_942_215
INPUT_LF = 62_206
OUTPUT_SHA256 = "9ae9dcf39c7e50f4d87d007f652a962e04e7ea0782e0564be345e72babed7e91"
OUTPUT_GIT_BLOB = "48d2307329ea1ff03e7ff80f532775652d49b99f"
OUTPUT_BYTES = 2_943_536
OUTPUT_LF = 62_234

EXPECTED_RULES = 7
EXPECTED_OCCURRENCES = 7
EXPECTED_DIRECT_HEADERS = 7
EXPECTED_CASCADE_HEADERS = 0

DECLARED_CONSUMED_NEW_OVERLAPS = (
    {
        "own_rule": "explicit_edge_derivative_expose_named_function",
        "foreign_owner": "probe16_mid37k49k",
        "foreign_rule": "explicit_edge_velocity_unfold_local_addcommgroup",
        "relation": "own_old_contains_consumed_new",
    },
    {
        "own_rule": "acted_edge_derivative_expose_named_function",
        "foreign_owner": "probe16_mid37k49k",
        "foreign_rule": "acted_edge_velocity_unfold_local_addcommgroup",
        "relation": "own_old_contains_consumed_new",
    },
    {
        "own_rule": "paired_transport_derivative_expose_named_function",
        "foreign_owner": "probe16_mid37k49k",
        "foreign_rule": "paired_transport_velocity_unfold_local_addcommgroup",
        "relation": "own_old_contains_consumed_new",
    },
)

PROBE16_MID_HELPER = {
    "target_path": (
        "scripts/qym-probe16-mid37k49k-p15-static/"
        "qym_probe16_mid37k49k_p15_static.py"
    ),
    "sha256": "5723983fb113915956363e8189299b51368e6ab5b3b2e7cc046de12668110473",
    "git_blob": "c130e0d8b76330c441b13ee737587aec177c3c24",
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
        "base_edge_derivative_pin_goal_complex_addcommgroup",
        """      (baseEdgeVelocity e.2 t) t := by
  rcases e with ⟨q, k⟩
""",
        """      (baseEdgeVelocity e.2 t) t := by
  letI : AddCommGroup ℂ := Complex.addCommGroup
  rcases e with ⟨q, k⟩
""",
        (Header(43842, 6, "Type mismatch: After simplification, term"),),
        "Pin the proof-local Complex additive group to the instance already elaborated into the theorem goal.",
        1,
    ),
    Rule(
        "base_edge_left_vertical_expose_constructor_lambda",
        """  | leftVerticalSegment =>
      have h :=
        ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
            ((-((1 : ℝ) / 2) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I))
      simpa [baseEdgeCoordinate, baseEdgeVelocity,
        Complex.mk_eq_add_mul_I, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
""",
        """  | leftVerticalSegment =>
      have h :=
        ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
            ((-((1 : ℝ) / 2) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I))
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa [baseEdgeCoordinate, baseEdgeVelocity,
        Complex.mk_eq_add_mul_I, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
""",
        (Header(43849, 6, "Type mismatch: After simplification, term"),),
        "Expose the exact left-vertical constructor lambda before normalizing the derivative proof.",
        1,
    ),
    Rule(
        "base_edge_right_vertical_expose_constructor_lambda",
        """  | rightVerticalSegment =>
      have h :=
        ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
            ((((1 : ℝ) / 2 : ℝ) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I))
      simpa [baseEdgeCoordinate, baseEdgeVelocity,
        Complex.mk_eq_add_mul_I, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
""",
        """  | rightVerticalSegment =>
      have h :=
        ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
            ((((1 : ℝ) / 2 : ℝ) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I))
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa [baseEdgeCoordinate, baseEdgeVelocity,
        Complex.mk_eq_add_mul_I, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
""",
        (Header(43857, 6, "Type mismatch: After simplification, term"),),
        "Expose the exact right-vertical constructor lambda before normalizing the derivative proof.",
        1,
    ),
    Rule(
        "explicit_edge_derivative_expose_named_function",
        """  have hComp := hOuter.comp_hasDerivAt t hBase
  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    explicitActualEdgeCoordinate, explicitActualEdgeVelocity,
    Function.comp_def, hz, ContinuousLinearMap.smul_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hComp
""",
        """  have hComp := hOuter.comp_hasDerivAt t hBase
  change HasDerivAt
    (fun x : ℝ =>
      selectedRepresentativeChart e.1 (baseEdgeCoordinate e.2 x))
    (explicitActualEdgeVelocity e t) t
  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    explicitActualEdgeCoordinate, explicitActualEdgeVelocity,
    Function.comp_def, hz, ContinuousLinearMap.smul_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hComp
""",
        (Header(43957, 2, "Type mismatch: After simplification, term"),),
        "Beta-expose explicitActualEdgeCoordinate to the exact function already carried by hComp.",
        1,
    ),
    Rule(
        "acted_edge_derivative_expose_named_function",
        """  have hComp' :
      HasDerivAt (actedSourceCoordinate e)
        (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t /
          inverseEtaPaperOrbitDenom e.pairingElement
            (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) ^ 2) t := by
    simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
      actedSourceCoordinate, gammaTwoMoebiusChart,
      gammaTwoMoebiusCoordinate, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate,
      QYM.FullCertification.P2NormalGreenExtension.actualEdgeCoordinate, Function.comp_def,
      ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc,
      UpperHalfPlane.ofComplex_apply] using hComp
""",
        """  have hComp' :
      HasDerivAt (actedSourceCoordinate e)
        (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t /
          inverseEtaPaperOrbitDenom e.pairingElement
            (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) ^ 2) t := by
    change HasDerivAt
      (fun x : ℝ =>
        Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate
          e.pairingElement
          (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e x))
      (QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e t /
        inverseEtaPaperOrbitDenom e.pairingElement
          (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t) ^ 2) t
    simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
      actedSourceCoordinate, gammaTwoMoebiusChart,
      gammaTwoMoebiusCoordinate, Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGreenBoundary.gammaTwoActionCoordinate,
      QYM.FullCertification.P2NormalGreenExtension.actualEdgeCoordinate, Function.comp_def,
      ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc,
      UpperHalfPlane.ofComplex_apply] using hComp
""",
        (Header(44091, 4, "Type mismatch: After simplification, term"),),
        "Beta-expose actedSourceCoordinate to the exact action lambda already carried by hComp.",
        1,
    ),
    Rule(
        "edge_parameter_transport_disable_conflicting_real_instances",
        """local instance p2EdgeVelocityCanonicalRealAddCommGroup : AddCommGroup ℝ :=
  Real.normedCommRing.toAddCommGroup

local instance p2EdgeVelocityCanonicalRealModule : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule
""",
        """local def p2EdgeVelocityCanonicalRealAddCommGroup : AddCommGroup ℝ :=
  Real.normedCommRing.toAddCommGroup

local def p2EdgeVelocityCanonicalRealModule : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule
""",
        (Header(44105, 2, "Type mismatch: After simplification, term"),),
        "Keep the named witnesses but stop them from overriding the canonical Real derivative instances.",
        1,
    ),
    Rule(
        "paired_transport_derivative_expose_named_function",
        """  have hComp := hPaired.scomp t (edgeParameterTransport_hasDerivAt e t)
  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    pairedTransportCoordinate, Function.comp_def,
    Complex.real_smul] using hComp
""",
        """  have hComp := hPaired.scomp t (edgeParameterTransport_hasDerivAt e t)
  change HasDerivAt
    (fun x : ℝ =>
      QYM.FullCertification.P2NormalGreenExtension.actualEdgeCoordinate e.paired
        (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e x))
    (((e.2.parameterSign : ℝ) : ℂ) *
      QYM.FullCertification.P2NormalGreenExtension.actualEdgeVelocity e.paired
        (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e t)) t
  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    pairedTransportCoordinate, Function.comp_def,
    Complex.real_smul] using hComp
""",
        (Header(44122, 2, "Type mismatch: After simplification, term"),),
        "Beta-expose pairedTransportCoordinate to the exact composed function already carried by hComp.",
        1,
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
    _require_shape(raw, expected_input(), "exact Probe16 input")
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
    _require_shape(output, expected_output(), "exact edge-repair output")
    return output


def inverse_rules(raw: bytes, order: Iterable[int] | None = None) -> bytes:
    _require_shape(raw, expected_output(), "exact edge-repair output")
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
    _require_shape(restored, expected_input(), "restored exact Probe16 input")
    return restored


def collision_audit() -> dict[str, object]:
    collisions: list[tuple[str, str, str]] = []
    for left_index, left in enumerate(RULES):
        for right_index, right in enumerate(RULES):
            if left_index >= right_index:
                continue
            for relation, left_anchor, right_anchor in (
                ("old-old", left.old, right.old),
                ("old-new", left.old, right.new),
                ("new-old", left.new, right.old),
                ("new-new", left.new, right.new),
            ):
                if left_anchor in right_anchor or right_anchor in left_anchor:
                    collisions.append((left.label, right.label, relation))
    if collisions:
        raise ValueError(f"undeclared own-rule collisions: {collisions}")
    return {
        "own_rule_collisions": 0,
        "declared_consumed_new_overlaps": len(DECLARED_CONSUMED_NEW_OVERLAPS),
        "undeclared_foreign_overlaps": 0,
        "foreign_owner": PROBE16_MID_HELPER,
    }


def static_audit() -> dict[str, object]:
    labels = [rule.label for rule in RULES]
    olds = [rule.old for rule in RULES]
    news = [rule.new for rule in RULES]
    if len(RULES) != EXPECTED_RULES:
        raise ValueError("rule count mismatch")
    if len(labels) != len(set(labels)) or len(olds) != len(set(olds)) or len(news) != len(set(news)):
        raise ValueError("duplicate label or anchor")
    if sum(rule.occurrences for rule in RULES) != EXPECTED_OCCURRENCES:
        raise ValueError("occurrence count mismatch")
    headers = tuple(header for rule in RULES for header in rule.headers)
    direct = tuple(header for header in headers if header.kind == "direct")
    cascades = tuple(header for header in headers if header.kind == "cascade")
    if len(direct) != EXPECTED_DIRECT_HEADERS or len(cascades) != EXPECTED_CASCADE_HEADERS:
        raise ValueError("header count mismatch")
    if [(header.line, header.column) for header in direct] != [
        (43842, 6),
        (43849, 6),
        (43857, 6),
        (43957, 2),
        (44091, 4),
        (44105, 2),
        (44122, 2),
    ]:
        raise ValueError("exact Probe16 diagnostic keys drifted")
    if any(not 37_000 <= header.line < 50_000 for header in headers):
        raise ValueError("header outside owned tranche")
    if any(rule.old == rule.new or not rule.old or not rule.new for rule in RULES):
        raise ValueError("empty or no-op rule")
    trust_terms = (
        "sorry",
        "admit",
        "axiom",
        "unsafe",
        "native_decide",
        "lean.ofreducebool",
        "maxheartbeats 0",
    )
    trust_hits = [
        (rule.label, term)
        for rule in RULES
        for term in trust_terms
        if term in rule.new.lower()
    ]
    if trust_hits:
        raise ValueError(f"trust-token hits: {trust_hits}")
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
        "trust_hits": len(trust_hits),
        **collision_audit(),
    }


def roundtrip_audit(raw: bytes) -> dict[str, object]:
    output = apply_rules(raw)
    restored = inverse_rules(output)
    if restored != raw:
        raise ValueError("canonical forward/inverse is not byte-exact")
    return {
        **static_audit(),
        "input": shape(raw),
        "output": shape(output),
        "inverse_byte_equal": True,
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
            "zip_sha256": AUTHORITY_ZIP_SHA256,
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
        "declared_consumed_new_overlaps": list(DECLARED_CONSUMED_NEW_OVERLAPS),
    }


def main(argv: Sequence[str] | None = None) -> int:
    if argv not in (None, (), []):
        raise SystemExit("this activation-disabled helper accepts no arguments")
    print(json.dumps(manifest(), ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
