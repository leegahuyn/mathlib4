#!/usr/bin/env python3
"""Exact-P9 reversible repair for three ``extendOfNorm`` instance roots.

The Probe9 diagnostics show that ``coreMap n`` was elaborated with the stored
``InverseEtaFixedPhaseCore`` module/additive structures while ``extendOfNorm``
introduced fresh structure metavariables.  The exact exit-0 c680 precedent
fixes the same boundary by pinning those two structures locally before the
extension call.  This helper applies only that proven pattern to the three
direct producer definitions; it never edits attributed cascades.

No Lean, Lake, Git, network, remote, or canonical-source operation is run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


SCHEMA = "qym-probe10-extendofnorm-instances-v1-exact-probe9"
INPUT_SHA256 = "fb37854ff158ae20a2acebe7722847726eb651ba9c716eff6b903cb4f32e8029"
INPUT_GIT_BLOB = "d29c6aff411f93b3c44d7d866fe2b2558f616a87"
INPUT_BYTES = 2_921_397
INPUT_LF = 61_746
LOG_SHA256 = "e8315f541ddcd8d9f99a395caddbcf57ceb3a1457a900bcefb45422dff81cd0f"
HEADERS_SHA256 = "e8b25cc78d4f2a9915cd25c6c7700f7f80ca73c7f01229fe531e3ef13386186f"
ERRORS = 287
WARNINGS = 361

# Sealed after the first in-memory transformation; ``--bootstrap-seal`` is
# accepted only while these four values retain the sentinel.
OUTPUT_SHA256 = "2051f6833163c46631431dda9187aed9f869eaadb4662f43e26c2cecb7cb3006"
OUTPUT_GIT_BLOB = "6b578ba82b4accccf90552bdc21d61197e2226f0"
OUTPUT_BYTES = 2_922_222
OUTPUT_LF = 61_755

# Exact source that compiled with exit 0 and zero error headers.  Its relevant
# blocks are lines 36553-36561 and 52430-52458.
PRECEDENT_SHA256 = "c680a35b9f12ea3223d8328ed0f5f0674b3439e650bb62cb900b54917f9653bd"
PRECEDENT_GIT_BLOB = "28f614d48e02a0f28d3f5a758e813350b3ea89cf"
PRECEDENT_BYTES = 2_821_792
PRECEDENT_LF = 63_138

MODULE_INSTANCE = (
    "  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=\n"
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n\n"
)
ADD_GROUP_INSTANCE = (
    "  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=\n"
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
)


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
        "stored_trace_extendofnorm_pin_core_instances",
        "      ActualFixedPhaseThreeCuspBoundaryL2 :=\n"
        "  (actualFixedPhaseThreeCuspTraceToL2Linear n Y).extendOfNorm\n"
        "    (coreMap n)\n",
        "      ActualFixedPhaseThreeCuspBoundaryL2 := by\n"
        + MODULE_INSTANCE
        + ADD_GROUP_INSTANCE
        + "  exact (actualFixedPhaseThreeCuspTraceToL2Linear n Y).extendOfNorm (coreMap n)\n",
        Header(36633, 4, "Application type mismatch: The argument"),
        (
            Header(36635, 0, TIMEOUT),
            Header(36662, 6, TIMEOUT),
            Header(36667, 8, "(kernel) unknown constant 'QYM.FullCertification.P2ClassicalTraceBoundaryExtension.actualFixedPhaseStoredTraceExtension_core'"),
            Header(36682, 0, TIMEOUT),
            Header(36742, 8, "(kernel) unknown constant 'QYM.FullCertification.P2ClassicalTraceBoundaryExtension.actualFixedPhaseStoredTraceExtension_core'"),
            Header(36801, 8, "(kernel) unknown constant 'QYM.FullCertification.P2ClassicalTraceBoundaryExtension.actualFixedPhaseStoredTraceExtension_core'"),
        ),
    ),
    Rule(
        "hhalf_trace_extendofnorm_pin_core_instances",
        "      ActualFixedPhaseThreeCuspBoundaryHhalf n Y :=\n"
        "  (actualFixedPhaseThreeCuspTraceToHhalfFull n Y).extendOfNorm\n"
        "    (coreMap n)\n",
        "      ActualFixedPhaseThreeCuspBoundaryHhalf n Y := by\n"
        + MODULE_INSTANCE
        + ADD_GROUP_INSTANCE
        + "  exact (actualFixedPhaseThreeCuspTraceToHhalfFull n Y).extendOfNorm (coreMap n)\n",
        Header(42062, 4, "Application type mismatch: The argument"),
        (
            Header(42064, 0, TIMEOUT),
            Header(42083, 8, "(kernel) unknown constant 'QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseHhalfTraceExtension_core'"),
        ),
    ),
    Rule(
        "product_collar_extendofnorm_pin_core_instances",
        "      ActualFixedPhaseProductCollarStoredEnergy n Y :=\n"
        "  (actualFixedPhaseSmoothCoreToProductCollarProfile n Y).extendOfNorm\n"
        "    (coreMap n)\n",
        "      ActualFixedPhaseProductCollarStoredEnergy n Y := by\n"
        + MODULE_INSTANCE
        + ADD_GROUP_INSTANCE
        + "  exact (actualFixedPhaseSmoothCoreToProductCollarProfile n Y).extendOfNorm (coreMap n)\n",
        Header(48977, 4, "Application type mismatch: The argument"),
        (
            Header(48979, 0, TIMEOUT),
            Header(49007, 6, TIMEOUT),
            Header(49009, 0, TIMEOUT),
            Header(49031, 8, "(kernel) unknown constant 'QYM.FullCertification.P2CollarTraceExtension.actualFixedPhaseOldGraphToProductCollarExtension_core'"),
            Header(49042, 12, "failed to synthesize"),
            Header(49044, 10, "failed to synthesize"),
        ),
    ),
)


PRECEDENT_SNIPPETS = (
    "  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=\n"
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n\n"
    "  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=\n"
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
    "  exact (selectedCuspCoreTrace n q Y).extendOfNorm (coreMap n)\n",
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
    "  exact (literalStagePlaneBaseCore Y n).extendOfNorm (coreMap n)\n",
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
    "  exact (literalStagePlaneDxCore Y n).extendOfNorm (coreMap n)\n",
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
    "  exact (literalStagePlaneDyCore Y n).extendOfNorm (coreMap n)\n",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    prefix = b"blob " + str(len(data)).encode("ascii") + b"\0"
    return hashlib.sha1(prefix + data).hexdigest()


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


def check_shape(
    actual: dict[str, object],
    wanted: tuple[str, str, int, int],
    *,
    bootstrap: bool = False,
) -> None:
    if not (bootstrap and wanted[0] == "__TO_SEAL__"):
        for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_authority(log: bytes, headers: bytes) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    if sha256(log) != LOG_SHA256 or sha256(headers) != HEADERS_SHA256:
        raise RuntimeError("exact Probe9 authority identity mismatch")
    text = log.decode("utf-8")
    extracted = [
        line
        for line in text.splitlines()
        if re.match(r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: error(?:\([^)]*\))?: ", line)
    ]
    if extracted != headers.decode("utf-8").splitlines() or len(extracted) != ERRORS:
        raise RuntimeError("exact Probe9 error-header artifact mismatch")
    warnings = len(
        re.findall(
            r"(?m)^PrimalitySheafVerification/QYM\.lean:\d+:\d+: warning(?:\([^)]*\))?: ",
            text,
        )
    )
    if warnings != WARNINGS:
        raise RuntimeError(f"Probe9 warning count {warnings} != {WARNINGS}")

    def verify(header: Header, rule: str, kind: str) -> dict[str, object]:
        pattern = re.compile(
            rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
            rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
        )
        count = len(pattern.findall(text))
        if count != 1:
            raise RuntimeError(f"{rule}:{kind}:{header.line}:{header.column} count {count}")
        return {
            "rule": rule,
            "kind": kind,
            **asdict(header),
            "count": count,
        }

    direct = [verify(rule.direct, rule.label, "direct") for rule in RULES]
    cascades = [
        verify(header, rule.label, "cascade")
        for rule in RULES
        for header in rule.cascades
    ]
    return direct, cascades


def verify_precedent(path: Path | None) -> dict[str, object]:
    if path is None:
        return {
            "verified": False,
            "sha256": PRECEDENT_SHA256,
            "git_blob": PRECEDENT_GIT_BLOB,
            "bytes": PRECEDENT_BYTES,
            "lf": PRECEDENT_LF,
            "claimed_exit": 0,
            "claimed_error_headers": 0,
        }
    data = path.read_bytes()
    actual = shape(data)
    check_shape(
        actual,
        (PRECEDENT_SHA256, PRECEDENT_GIT_BLOB, PRECEDENT_BYTES, PRECEDENT_LF),
    )
    text = data.decode("utf-8")
    counts = [text.count(snippet) for snippet in PRECEDENT_SNIPPETS]
    if counts != [1, 1, 1, 1]:
        raise RuntimeError(f"compiled-precedent snippet counts {counts} != [1, 1, 1, 1]")
    return {
        "verified": True,
        **actual,
        "relevant_lines": ["36553-36561", "52430-52458"],
        "matching_blocks": 4,
        "authority_exit_file_value": 0,
        "authority_error_headers": 0,
    }


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact count {count} != {rule.occurrences}")
        if text.count(new) != 0:
            raise RuntimeError(f"{rule.label}: destination anchor already present")
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "direct_header": asdict(rule.direct),
                "cascade_headers": [asdict(header) for header in rule.cascades],
            }
        )
    return text, audit


def verify_rule_independence(source: str) -> dict[str, object]:
    anchors: list[tuple[int, int, str]] = []
    for rule in RULES:
        start = source.find(rule.old)
        if start < 0 or source.find(rule.old, start + 1) >= 0:
            raise RuntimeError(f"{rule.label}: non-unique source anchor")
        anchors.append((start, start + len(rule.old), rule.label))
    overlaps = [
        (left_label, right_label)
        for i, (left_start, left_end, left_label) in enumerate(anchors)
        for right_start, right_end, right_label in anchors[i + 1 :]
        if left_start < right_end and right_start < left_end
    ]
    if overlaps:
        raise RuntimeError(f"own-rule overlaps: {overlaps}")
    return {
        "rules": len(RULES),
        "source_occurrences": len(anchors),
        "pairwise_checks": 3,
        "overlaps": [],
        "pass": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe9-log", type=Path, required=True)
    parser.add_argument("--probe9-error-headers", type=Path, required=True)
    parser.add_argument("--compiled-precedent", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()

    inverse = args.mode == "inverse"
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected(inverse, False), bootstrap=args.bootstrap_seal)
    direct, cascades = verify_authority(
        args.probe9_log.read_bytes(), args.probe9_error_headers.read_bytes()
    )
    precedent = verify_precedent(args.compiled_precedent)
    source_text = source.decode("utf-8")
    independence = None if inverse else verify_rule_independence(source_text)
    before = trust(source_text)
    result_text, rules = transform(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected(inverse, True), bootstrap=args.bootstrap_seal)
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
        "status": "STATIC_PASS_EXACT_PROBE9_NOT_LEAN_EXECUTED",
        "activation": False,
        "activation_gate": "TERMINAL_PROBE10_EXECUTION_REQUIRED",
        "mode": args.mode,
        "authority": {
            "run_id": 31971447929,
            "artifact_id": 9270002403,
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "errors": ERRORS,
            "warnings": WARNINGS,
            "exit": 1,
            "panic": 0,
        },
        "source": source_shape,
        "result": result_shape,
        "scope": {
            "producer_lines": [36633, 42062, 48977],
            "direct_producer_definitions_only": True,
            "cascade_lines_modified": False,
        },
        "repair_family": "extendOfNorm_pin_fixed_phase_core_instances",
        "repair_sites": len(RULES),
        "active_occurrences": sum(item["occurrences"] for item in rules),
        "direct_headers_verified": direct,
        "cascade_headers_attributed_only": cascades,
        "rules": rules,
        "own_rule_independence": independence,
        "compiled_exit0_precedent": precedent,
        "inverse_byte_equal": True,
        "trust": after,
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
