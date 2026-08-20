#!/usr/bin/env python3
"""Conditional exact-P9 repairs for direct QYM roots in lines 30000--49999.

The helper is a byte-locked, exact-counted, reversible static transformer.  It
reads the terminal Probe9 candidate and diagnostics, but never runs Lean/Lake,
touches Git, performs network operations, or mutates repository sources.  Its
output remains activation-disabled until a later integrated CI probe executes
the candidate.
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

SCHEMA = "qym-probe10-midlate-static-transform-v2-exact-probe9"
INPUT_SHA256 = "fb37854ff158ae20a2acebe7722847726eb651ba9c716eff6b903cb4f32e8029"
INPUT_GIT_BLOB = "d29c6aff411f93b3c44d7d866fe2b2558f616a87"
INPUT_BYTES = 2_921_397
INPUT_LF = 61_746
LOG_SHA256 = "e8315f541ddcd8d9f99a395caddbcf57ceb3a1457a900bcefb45422dff81cd0f"
HEADERS_SHA256 = "e8b25cc78d4f2a9915cd25c6c7700f7f80ca73c7f01229fe531e3ef13386186f"
DIAGNOSTICS_SHA256 = "a34f5b424f8aac739ac05ce4375003fe9da7f0ee4689050d4d712c9816f66580"

# Filled after the deterministic in-memory bootstrap projection and then
# enforced for both forward and inverse execution.
OUTPUT_SHA256 = "b1f11b801fc665643e728b6083bbea22384e5f4794da512f368b52f8a126cfc4"
OUTPUT_GIT_BLOB = "788601940f92830920aa80bcaa0726322c52c7a4"
OUTPUT_BYTES = 2_921_367
OUTPUT_LF = 61_747

ACTIVE_PROBE9_HELPER_SHA256 = {
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
}


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
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "coupled_state_matter_top_reduce_to_true",
        "@[simp] theorem coupledState_matter_type (Y : \u211d)\n"
        "    (divergence : GaugeFluctuation Y \u2192L[\u2102] GaugeDivergenceTarget Y)\n"
        "    (u : CoupledState Y divergence) :\n"
        "    u.fst \u2208 (\u22a4 : Submodule \u2102 (MatterField Y)) := by\n"
        "  change (u.fst : MatterField Y) \u2208\n"
        "    (\u22a4 : Submodule \u2102 (MatterField Y))\n"
        "  exact Submodule.mem_top\n",
        "@[simp] theorem coupledState_matter_type (Y : \u211d)\n"
        "    (divergence : GaugeFluctuation Y \u2192L[\u2102] GaugeDivergenceTarget Y)\n"
        "    (u : CoupledState Y divergence) :\n"
        "    u.fst \u2208 (\u22a4 : Submodule \u2102 (MatterField Y)) := by\n"
        "  change True\n"
        "  trivial\n",
        (Header(31000, 8, "failed to synthesize instance of type class",
                "lean.synthInstanceFailed"),),
        "Reduce membership in the explicitly typed top submodule before opaque FieldCarrier blocks AddCommMonoid inference.",
    ),
    Rule(
        "coupled_state_gauge_top_reduce_to_true",
        "@[simp] theorem coupledState_gauge_type (Y : \u211d)\n"
        "    (divergence : GaugeFluctuation Y \u2192L[\u2102] GaugeDivergenceTarget Y)\n"
        "    (u : CoupledState Y divergence) :\n"
        "    u.snd \u2208 (\u22a4 : Submodule \u2102 (CoulombGaugeSlice Y divergence)) := by\n"
        "  change (u.snd : CoulombGaugeSlice Y divergence) \u2208\n"
        "    (\u22a4 : Submodule \u2102 (CoulombGaugeSlice Y divergence))\n"
        "  exact Submodule.mem_top\n",
        "@[simp] theorem coupledState_gauge_type (Y : \u211d)\n"
        "    (divergence : GaugeFluctuation Y \u2192L[\u2102] GaugeDivergenceTarget Y)\n"
        "    (u : CoupledState Y divergence) :\n"
        "    u.snd \u2208 (\u22a4 : Submodule \u2102 (CoulombGaugeSlice Y divergence)) := by\n"
        "  change True\n"
        "  trivial\n",
        (Header(31008, 8, "failed to synthesize instance of type class",
                "lean.synthInstanceFailed"),),
        "Reduce top membership to True before the opaque gauge FieldCarrier participates in typeclass search.",
    ),
    Rule(
        "standard_hermitian_self_nonneg_explicit_vector",
        "theorem standardHermitianMetricData_self_nonneg (tau : H) (z : \u2102) :\n"
        "    0 \u2264 (standardHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg (\U0001d55c := \u2102)\n",
        "theorem standardHermitianMetricData_self_nonneg (tau : H) (z : \u2102) :\n"
        "    0 \u2264 (standardHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg (\U0001d55c := \u2102) (x := z)\n",
        (Header(31884, 8, "typeclass instance problem is stuck"),),
        "Supply inner_self_nonneg's implicit vector so its InnerProductSpace carrier is exactly Complex.",
    ),
    Rule(
        "inverse_eta_hermitian_self_nonneg_explicit_vector",
        "theorem inverseEtaHermitianMetricData_self_nonneg\n"
        "    (tau : H) (z : \u2102) :\n"
        "    0 \u2264 (inverseEtaHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg (\U0001d55c := \u2102)\n",
        "theorem inverseEtaHermitianMetricData_self_nonneg\n"
        "    (tau : H) (z : \u2102) :\n"
        "    0 \u2264 (inverseEtaHermitianMetricData.pairing tau z z).re := by\n"
        "  exact inner_self_nonneg (\U0001d55c := \u2102)\n"
        "    (x := Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z)\n",
        (Header(31915, 8, "typeclass instance problem is stuck"),),
        "Fix the implicit vector to the concrete eta-weighted Complex value before typeclass synthesis.",
    ),
    Rule(
        "polygon_edge_pairing_set_result_ascription",
        "theorem polygonEdge_pairing_set (e : PolygonEdge) :\n"
        "    (e.pairingElement : SL(2, \u2124)) \u2022 polygonEdgeSet e =\n"
        "      polygonEdgeSet e.paired := by\n",
        "theorem polygonEdge_pairing_set (e : PolygonEdge) :\n"
        "    ((e.pairingElement : SL(2, \u2124)) \u2022 polygonEdgeSet e : Set \u210d) =\n"
        "      polygonEdgeSet e.paired := by\n",
        (Header(34052, 4, "failed to synthesize instance of type class",
                "lean.synthInstanceFailed"),),
        "Ascribe the pointwise action result as Set UpperHalfPlane so HSMul does not leave its result metavariable open.",
    ),
    Rule(
        "smooth_compact_weight_core_unwrap_subtype",
        "theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace\n"
        "    {k : \u2124} {M : HalfIntegralMultiplier GammaTwo k}\n"
        "    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore M) :\n"
        "    HasMultiplierMatchedPolygonTrace M u.toSection := by\n"
        "  apply hasMultiplierMatchedPolygonTrace_of_covariance M u.toSection\n"
        "  intro \u03b3 z\n"
        "  simpa only using u.covariance \u03b3 z\n",
        "theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace\n"
        "    {k : \u2124} {M : HalfIntegralMultiplier GammaTwo k}\n"
        "    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore M) :\n"
        "    HasMultiplierMatchedPolygonTrace M u.1.toSection := by\n"
        "  apply hasMultiplierMatchedPolygonTrace_of_covariance M u.1.toSection\n"
        "  intro \u03b3 z\n"
        "  simpa only using u.1.covariance \u03b3 z\n",
        (
            Header(34140, 41, "Invalid field `toSection`", "lean.invalidField"),
            Header(34141, 59, "Invalid field `toSection`", "lean.invalidField"),
            Header(34143, 21, "Invalid field `covariance`", "lean.invalidField"),
        ),
        "SmoothCompactWeightCore is a subtype; unwrap it before projecting the stored section and covariance fields.",
    ),
    Rule(
        "inverse_eta_core_unwrap_subtype",
        "    HasMultiplierMatchedPolygonTrace\n"
        "      (inverseEtaMultiplier GammaTwo) u.toSection :=\n"
        "  smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace u\n",
        "    HasMultiplierMatchedPolygonTrace\n"
        "      (inverseEtaMultiplier GammaTwo) u.1.toSection :=\n"
        "  smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace u\n",
        (Header(34150, 40, "Invalid field `toSection`", "lean.invalidField"),),
        "Unwrap the inverse-eta SmoothCompactWeightCore subtype in its specialized theorem statement.",
    ),
    Rule(
        "finite_energy_core_zero_use_memlp_namespace",
        "  zero_mem' := by\n"
        "    intro kappa\n"
        "    rw [actualFixedPhaseNamedCuspTraceRepresentative_zero,\n"
        "      widthTwoTwistedDifferenceQuotient_zero]\n"
        "    exact memLp_zero\n",
        "  zero_mem' := by\n"
        "    intro kappa\n"
        "    rw [actualFixedPhaseNamedCuspTraceRepresentative_zero,\n"
        "      widthTwoTwistedDifferenceQuotient_zero]\n"
        "    exact MemLp.zero\n",
        (Header(41467, 10, "Unknown identifier `memLp_zero`",
                "lean.unknownIdentifier"),),
        "Use the current MemLp.zero API already exercised at four earlier exact QYM sites.",
    ),
    Rule(
        "hyperbolic_normal_remove_nonexistent_neg_one_simp_name",
        "    neg_zero, neg_one, mul_zero, zero_mul, sub_zero, zero_sub,\n",
        "    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub,\n",
        (Header(44349, 14, "Unknown identifier `neg_one`",
                "lean.unknownIdentifier"),),
        "Remove the nonexistent simp theorem name; numeral negation normalization remains in the simp set.",
    ),
    Rule(
        "hhalf_density_qualify_gamma_two_cusp",
        "theorem actualFixedPhase_widthTwoHhalfFiniteEnergyDomainDense\n"
        "    (n : \u2124) (kappa : GammaTwoCusp) (Y : \u211d) :\n",
        "theorem actualFixedPhase_widthTwoHhalfFiniteEnergyDomainDense\n"
        "    (n : \u2124)\n"
        "    (kappa : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoCusp)\n"
        "    (Y : \u211d) :\n",
        (Header(45687, 21, "Unknown identifier `GammaTwoCusp`",
                "lean.unknownIdentifier"),),
        "Name GammaTwoCusp from its defining namespace after the preceding namespace scope has closed.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    prefix = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(prefix + raw).hexdigest()


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
    allow_unsealed: bool = False,
) -> None:
    if not allow_unsealed:
        for key, value in zip(
            ("sha256", "git_blob", "bytes", "lf"), wanted, strict=True
        ):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def error_header_pattern(header: Header) -> re.Pattern[str]:
    if header.code is None:
        lead = "error: "
    else:
        lead = rf"error\({re.escape(header.code)}\): "
    return re.compile(
        rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
        rf"{lead}{re.escape(header.message)}",
    )


def verify_authority(
    log_raw: bytes, headers_raw: bytes, diagnostics_raw: bytes
) -> list[dict[str, object]]:
    if sha256(log_raw) != LOG_SHA256:
        raise RuntimeError("Probe9 log identity mismatch")
    if sha256(headers_raw) != HEADERS_SHA256:
        raise RuntimeError("Probe9 error-header identity mismatch")
    if sha256(diagnostics_raw) != DIAGNOSTICS_SHA256:
        raise RuntimeError("Probe9 diagnostics identity mismatch")

    log_lines = log_raw.decode("utf-8", errors="strict").splitlines()
    header_lines = headers_raw.decode("utf-8", errors="strict").splitlines()
    extracted = [
        line
        for line in log_lines
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if extracted != header_lines or len(header_lines) != 287:
        raise RuntimeError("Probe9 exact error-header extraction mismatch")

    diagnostic_rows = [
        json.loads(line)
        for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()
    ]
    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = error_header_pattern(header)
            header_matches = [line for line in header_lines if pattern.match(line)]
            diag_matches = [
                row
                for row in diagnostic_rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(header_matches) != 1 or len(diag_matches) != 1:
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
                    "kind": "direct",
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


# Compatibility alias used by the existing tranche integrators.
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
    module_name = "_qym_foreign_" + hashlib.sha256(str(path).encode()).hexdigest()
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def audit_foreign_spans(
    base: str, foreign_helpers: list[Path], inverse: bool = False
) -> dict[str, object]:
    by_name = {path.name: path for path in foreign_helpers}
    if set(by_name) != set(ACTIVE_PROBE9_HELPER_SHA256):
        raise RuntimeError("foreign helper set is not the exact six active Probe9 helpers")

    own = [
        (start, end, rule.label)
        for rule in RULES
        for start, end in spans(base, rule.new if inverse else rule.old)
    ]
    if len(own) != sum(rule.occurrences for rule in RULES):
        raise RuntimeError("own source-span inventory mismatch")

    identities: dict[str, str] = {}
    overlaps: list[dict[str, object]] = []
    exact_equalities = 0
    foreign_count = 0
    own_anchors = {value for rule in RULES for value in (rule.old, rule.new)}
    for name, expected_sha in ACTIVE_PROBE9_HELPER_SHA256.items():
        path = by_name[name]
        digest = sha256(path.read_bytes())
        if digest != expected_sha:
            raise RuntimeError(f"foreign helper identity mismatch: {name}")
        identities[name] = digest
        module = load_helper(path)
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        for foreign_rule in foreign_rules:
            foreign_count += 1
            old = getattr(foreign_rule, "old")
            new = getattr(foreign_rule, "new")
            exact_equalities += int(old in own_anchors) + int(new in own_anchors)
            matches = spans(base, new)
            expected_count = getattr(foreign_rule, "occurrences", 1)
            if len(matches) != expected_count:
                raise RuntimeError(
                    f"foreign active exact-P9 anchor count mismatch: {name}:"
                    f"{getattr(foreign_rule, 'label')}"
                )
            for fstart, fend in matches:
                for ostart, oend, own_label in own:
                    if max(fstart, ostart) < min(fend, oend):
                        overlaps.append(
                            {
                                "own": own_label,
                                "foreign_helper": name,
                                "foreign_rule": getattr(foreign_rule, "label"),
                            }
                        )
    if exact_equalities or overlaps:
        raise RuntimeError(
            f"active Probe9 collision: equalities={exact_equalities}, overlaps={overlaps}"
        )
    return {
        "foreign_helper_sha256": identities,
        "foreign_rule_families_checked": foreign_count,
        "own_spans_checked": len(own),
        "exact_anchor_equalities": exact_equalities,
        "span_overlaps": overlaps,
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
    collision_audit = audit_foreign_spans(
        source_text, args.foreign_helper, inverse=inverse
    )
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
            "probe9_trigger_sha": "3b5e67d81c4d8979f2c4b57c9f2b7839b0806388",
            "probe9_result_source": "PROBE_RESULT.json",
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
            "candidate_lines": [30000, 49999],
            "direct_producer_roots_only": True,
            "cascade_lines_modified": False,
            "excluded_active_extendofnorm_roots": [36633, 42062, 48978],
            "active_probe9_components_verified_on_input": True,
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
            "inner_self_nonneg_signature_has_implicit_x": True,
            "memLp_zero_api_existing_qym_lines": [28687, 28689, 28758, 40850],
            "smooth_compact_core_diagnostics_identify_subtype_receiver": True,
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
