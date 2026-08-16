#!/usr/bin/env python3
"""Exact-P8 reversible Probe9 repair for three extendOfNorm producer roots.

This helper performs no Lean, Lake, Git, network, remote, or canonical-source
operation.  It is byte-locked to the terminal Probe8 authority and remains a
conditional static projection until the terminal Probe9 execution.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import runpy
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe9-extendofnorm-static-v1-exact-probe8"
INPUT_SHA256 = "63baae8766e3208ac1d8dfa66946ac5ae3cf4a4264d21218a1ccb17aed3c4fd8"
INPUT_GIT_BLOB = "a2d3f4f60018fc2bfebd904db17aa13025c39ed6"
INPUT_BYTES = 2_916_737
INPUT_LF = 61_671
LOG_SHA256 = "4408bf46825d32a935de970904c711510b774ef93026fbee3e20dbc18392beea"
HEADERS_SHA256 = "9f0d91787942db9470e307c5a44d8523b2b362ad31f737da0eb48b3f9f2d181f"

OUTPUT_SHA256 = "21a49adb8f3f2b4229161c147293a328d64d0d47be8d0990a9a8b6e4b76b9fb8"
OUTPUT_GIT_BLOB = "2f9b00135aca61f50728ddbc3f044e1bcb714d49"
OUTPUT_BYTES = 2_916_695
OUTPUT_LF = 61_668

FOREIGN_HELPER_SHA256 = {
    "qym_probe7_reanchored.py":
        "1919650925df78ea6b87a742937ba4c57cd1e3eeb123d5a2111131189a4fa53a",
    "qym_probe8_early_independent.py":
        "67843a8608038295f570bb15feb8f08cbb6d90f9c166d078fecde9e1ba215cf4",
    "qym_probe8_mid_static.py":
        "b529f1df682a1e9b1588399f3a951914452d1d9afb049dd7be22cef1d8570dbf",
    "qym_probe8_late_static.py":
        "4b3470fa2296d61002460e6f8532402f0509ae8c3385f36b512a732ad55c8f9f",
    "qym_probe9_50k_static.py":
        "44b17336ea2cfa089c461e8c23cf25d2de95987e106e8473f2765cb2bf5faab4",
    "qym_probe9_55k_static.py":
        "605fc454aea53613082b357004ed182ac1ec12cc813258640d4904cc054e2d6f",
}


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    direct: Header
    cascades: tuple[Header, ...]
    occurrences: int = 1


TIMEOUT = "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached"

RULES: tuple[Rule, ...] = (
    Rule(
        "stored_trace_extendofnorm_receiver_direction",
        "  LinearMap.extendOfNorm\n"
        "    (actualFixedPhaseThreeCuspTraceToL2Linear n Y)\n"
        "    (coreMap n)\n",
        "  (actualFixedPhaseThreeCuspTraceToL2Linear n Y).extendOfNorm\n"
        "    (coreMap n)\n",
        Header(36624, 4, "Application type mismatch: The argument"),
        (
            Header(36626, 0, TIMEOUT),
            Header(36653, 6, TIMEOUT),
            Header(36658, 8, "(kernel) unknown constant 'QYM.FullCertification.P2ClassicalTraceBoundaryExtension.actualFixedPhaseStoredTraceExtension_core'"),
            Header(36673, 0, TIMEOUT),
        ),
    ),
    Rule(
        "hhalf_trace_extendofnorm_receiver_direction",
        "  LinearMap.extendOfNorm\n"
        "    (actualFixedPhaseThreeCuspTraceToHhalfFull n Y)\n"
        "    (coreMap n)\n",
        "  (actualFixedPhaseThreeCuspTraceToHhalfFull n Y).extendOfNorm\n"
        "    (coreMap n)\n",
        Header(42054, 4, "Application type mismatch: The argument"),
        (
            Header(42056, 0, TIMEOUT),
            Header(42075, 8, "(kernel) unknown constant 'QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseHhalfTraceExtension_core'"),
        ),
    ),
    Rule(
        "product_collar_extendofnorm_receiver_direction",
        "  LinearMap.extendOfNorm\n"
        "    (actualFixedPhaseSmoothCoreToProductCollarProfile n Y)\n"
        "    (coreMap n)\n",
        "  (actualFixedPhaseSmoothCoreToProductCollarProfile n Y).extendOfNorm\n"
        "    (coreMap n)\n",
        Header(48970, 4, "Application type mismatch: The argument"),
        (
            Header(48972, 0, TIMEOUT),
            Header(49000, 6, TIMEOUT),
            Header(49002, 0, TIMEOUT),
            Header(49035, 12, "failed to synthesize"),
            Header(49037, 10, "failed to synthesize"),
            Header(49024, 8, "(kernel) unknown constant 'QYM.FullCertification.P2CollarTraceExtension.actualFixedPhaseOldGraphToProductCollarExtension_core'"),
        ),
    ),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8")
    return {
        "sha256": sha256(data),
        "git_blob": git_blob(data),
        "bytes": len(data),
        "lf": data.count(b"\n"),
        "cr": b"\r" in data,
        "nul": b"\0" in data,
        "bom": data.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": data.endswith(b"\n"),
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


def expected(inverse: bool, result: bool) -> tuple[str, str, int, int]:
    source = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    output = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    if inverse:
        source, output = output, source
    return output if result else source


def check_shape(actual: dict[str, object], wanted: tuple[str, str, int, int], *, bootstrap: bool = False) -> None:
    if not (bootstrap and wanted[0] == "__TO_SEAL__"):
        for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_authority(log: bytes, headers: bytes) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    if sha256(log) != LOG_SHA256 or sha256(headers) != HEADERS_SHA256:
        raise RuntimeError("exact Probe8 authority identity mismatch")
    text = log.decode("utf-8")
    extracted = [
        line for line in text.splitlines()
        if re.match(r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: error(?:\([^)]*\))?: ", line)
    ]
    if extracted != headers.decode("utf-8").splitlines() or len(extracted) != 344:
        raise RuntimeError("exact Probe8 error-header artifact mismatch")
    warnings = len(re.findall(r"(?m)^PrimalitySheafVerification/QYM\.lean:\d+:\d+: warning(?:\([^)]*\))?: ", text))
    if warnings != 374:
        raise RuntimeError(f"Probe8 warning count {warnings} != 374")

    def verify(header: Header, rule: str, kind: str) -> dict[str, object]:
        pattern = re.compile(
            rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
            rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
        )
        count = len(pattern.findall(text))
        if count != 1:
            raise RuntimeError(f"{rule}:{kind}:{header.line}:{header.column} count {count}")
        return {"rule": rule, "kind": kind, "line": header.line, "column": header.column,
                "message": header.message, "count": count}

    direct = [verify(rule.direct, rule.label, "direct") for rule in RULES]
    cascades = [verify(header, rule.label, "cascade") for rule in RULES for header in rule.cascades]
    return direct, cascades


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    rules = tuple(reversed(RULES)) if inverse else RULES
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact count {count} != {rule.occurrences}")
        text = text.replace(old, new)
        audit.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                      "occurrences": count, "direct_header": rule.direct.__dict__,
                      "cascade_headers": [header.__dict__ for header in rule.cascades]})
    return text, audit


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        index = text.find(needle, start)
        if index < 0:
            return result
        result.append((index, index + len(needle)))
        start = index + 1


def collision_audit(base: str, helpers: list[Path]) -> dict[str, object]:
    if {path.name for path in helpers} != set(FOREIGN_HELPER_SHA256):
        raise RuntimeError("foreign helper set mismatch")
    own = [(a, b, rule.label) for rule in RULES for a, b in spans(base, rule.old)]
    if len(own) != 3:
        raise RuntimeError(f"own exact span count {len(own)} != 3")
    active_new_names = {
        "qym_probe7_reanchored.py", "qym_probe8_early_independent.py",
        "qym_probe8_mid_static.py", "qym_probe8_late_static.py",
    }
    foreign: list[tuple[int, int, str, str]] = []
    consumed: list[str] = []
    identities: dict[str, str] = {}
    equality = 0
    own_anchors = {anchor for rule in RULES for anchor in (rule.old, rule.new)}
    for path in helpers:
        digest = sha256(path.read_bytes())
        if digest != FOREIGN_HELPER_SHA256[path.name]:
            raise RuntimeError(f"foreign helper identity mismatch: {path.name}")
        identities[path.name] = digest
        table = runpy.run_path(str(path)).get("RULES") or runpy.run_path(str(path)).get("REPAIRS")
        if not isinstance(table, tuple):
            raise RuntimeError(f"foreign helper has no tuple table: {path.name}")
        for item in table:
            old, new = getattr(item, "old"), getattr(item, "new")
            equality += int(old in own_anchors) + int(new in own_anchors)
            primary = new if path.name in active_new_names else old
            alternate = old if path.name in active_new_names else new
            wanted = int(getattr(item, "occurrences", 1))
            matches = spans(base, primary)
            if len(matches) != wanted:
                alt = spans(base, alternate)
                if not matches and len(alt) == wanted:
                    matches = alt
                elif not matches and not alt:
                    consumed.append(f"{path.name}:{getattr(item, 'label')}")
                    continue
                else:
                    raise RuntimeError(f"foreign anchor count mismatch: {path.name}:{getattr(item, 'label')}")
            foreign.extend((a, b, path.name, getattr(item, "label")) for a, b in matches)
    overlaps = [
        {"own": ol, "foreign_helper": hp, "foreign_rule": fl}
        for oa, ob, ol in own for fa, fb, hp, fl in foreign
        if oa < fb and fa < ob
    ]
    if equality or overlaps:
        raise RuntimeError(f"foreign collision equality={equality}, overlaps={overlaps}")
    return {"foreign_helper_sha256": identities, "foreign_spans_checked": len(foreign),
            "consumed_by_downstream": consumed, "exact_anchor_equalities": equality,
            "span_overlaps": overlaps, "pass": True}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe8-log", type=Path, required=True)
    parser.add_argument("--probe8-error-headers", type=Path, required=True)
    parser.add_argument("--foreign-helper", type=Path, action="append", required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected(inverse, False), bootstrap=args.bootstrap_seal and inverse)
    direct, cascades = verify_authority(args.probe8_log.read_bytes(), args.probe8_error_headers.read_bytes())
    source_text = source.decode("utf-8")
    foreign = None if inverse else collision_audit(source_text, args.foreign_helper)
    before = trust(source_text)
    result_text, rules = transform(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected(inverse, True), bootstrap=args.bootstrap_seal and not inverse)
    after = trust(result_text)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust inventory failure: {before} -> {after}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    record = {
        "schema": SCHEMA,
        "status": "CONDITIONAL_STATIC_PASS_EXACT_PROBE8_NOT_LEAN_EXECUTED",
        "activation": False,
        "activation_gate": "TERMINAL_PROBE9_EXECUTION_REQUIRED",
        "mode": args.mode,
        "authority": {"run_id": 31969310662, "candidate_sha256": INPUT_SHA256,
                      "candidate_git_blob": INPUT_GIT_BLOB, "log_sha256": LOG_SHA256,
                      "error_headers_sha256": HEADERS_SHA256, "errors": 344,
                      "warnings": 374, "exit": 1, "panic": 0},
        "scope": {"producer_lines": [36624, 42054, 48970],
                  "direct_producer_roots_only": True, "cascade_lines_modified": False},
        "source": source_shape,
        "result": result_shape,
        "repair_family": "extendOfNorm_receiver_direction",
        "repair_sites": 3,
        "active_occurrences": sum(item["occurrences"] for item in rules),
        "direct_headers_verified": direct,
        "cascade_headers_attributed": cascades,
        "rules": rules,
        "foreign_anchor_collision_audit": foreign,
        "inverse_byte_equal": True,
        "trust": after,
        "execution": {"lean": False, "lake": False, "git_mutation": False,
                      "network": False, "remote": False, "canonical_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
