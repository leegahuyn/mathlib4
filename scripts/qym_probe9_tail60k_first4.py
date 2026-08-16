#!/usr/bin/env python3
"""Exact reversible repair of four high-confidence Probe8 roots at 60k.

This is a local static transformer over immutable Probe8 candidate and
diagnostic artifacts.  It does not execute Lean/Lake/Git/network operations,
does not mutate repository sources, and does not authorize promotion.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe9-tail60k-first4-transform-v1"
INPUT_SHA256 = "63baae8766e3208ac1d8dfa66946ac5ae3cf4a4264d21218a1ccb17aed3c4fd8"
INPUT_GIT_BLOB = "a2d3f4f60018fc2bfebd904db17aa13025c39ed6"
INPUT_BYTES = 2_916_737
INPUT_LF = 61_671
LOG_SHA256 = "4408bf46825d32a935de970904c711510b774ef93026fbee3e20dbc18392beea"
ERROR_HEADERS_SHA256 = "9f0d91787942db9470e307c5a44d8523b2b362ad31f737da0eb48b3f9f2d181f"

# Filled from one deterministic bootstrap projection, then enforced both ways.
OUTPUT_SHA256 = "74c51382cf810039c1bec6123724e890a35dd44dae187f4af5a677fce64a088a"
OUTPUT_GIT_BLOB = "9de20e5cd8251475e6f66ff7dbb1994dafed548b"
OUTPUT_BYTES = 2_916_843
OUTPUT_LF = 61_673


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
    headers: tuple[Header, ...]
    rationale: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "escape_projection_positive_branch_reduce_zero_apply",
        "    have hEscape : x ∉ actualCutoffEscapeOpenSet n :=\n"
        "      fun h => h.2 hx\n"
        "    rw [Set.indicator_of_notMem hEscape]\n",
        "    have hEscape : x ∉ actualCutoffEscapeOpenSet n :=\n"
        "      fun h => h.2 hx\n"
        "    rw [Set.indicator_of_notMem hEscape]\n"
        "    simpa only [Pi.zero_apply]\n",
        (Header(61034, 2, "unsolved goals"),),
        "After the indicator rewrite, reduce the remaining function-zero application exactly.",
    ),
    Rule(
        "escape_projection_negative_branch_reduce_zero_apply",
        "  · rw [Set.indicator_of_notMem hx]\n"
        "\n"
        "/-- The escape Hamiltonian fixes the concrete escape-band indicator. -/\n",
        "  · rw [Set.indicator_of_notMem hx]\n"
        "    simpa only [Pi.zero_apply]\n"
        "\n"
        "/-- The escape Hamiltonian fixes the concrete escape-band indicator. -/\n",
        (Header(61038, 2, "unsolved goals"),),
        "After the indicator rewrite, reduce the remaining function-zero application exactly.",
    ),
    Rule(
        "escape_hamiltonian_ext_reduce_clm_zero_apply",
        "    apply ContinuousLinearMap.ext\n"
        "    intro x\n"
        "    simpa using h x\n",
        "    apply ContinuousLinearMap.ext\n"
        "    intro x\n"
        "    simpa only [ContinuousLinearMap.zero_apply] using h x\n",
        (Header(61152, 4, "Type mismatch: After simplification, term"),),
        "Normalize only the continuous-linear-map zero application on the extensionality goal.",
    ),
    Rule(
        "limit_off_ground_bot_membership_supply_scalar",
        "  exact hne (Submodule.mem_bot.mp hu)\n"
        "\n"
        "/-! ## 4. Uniform-gap acceptance package is incompatible with this surrogate -/\n",
        "  exact hne ((Submodule.mem_bot ℂ).mp hu)\n"
        "\n"
        "/-! ## 4. Uniform-gap acceptance package is incompatible with this surrogate -/\n",
        (Header(61335, 13, "Unknown constant `Submodule.mem_bot.mp`"),),
        "Supply the missing scalar parameter, matching the already accepted polymorphic QYM precedent.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


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


def verify_authority(log_raw: bytes, header_raw: bytes) -> list[dict[str, object]]:
    if sha256(log_raw) != LOG_SHA256:
        raise RuntimeError(f"Probe8 log sha256 {sha256(log_raw)} != {LOG_SHA256}")
    if sha256(header_raw) != ERROR_HEADERS_SHA256:
        raise RuntimeError(
            f"Probe8 header sha256 {sha256(header_raw)} != {ERROR_HEADERS_SHA256}"
        )
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
    if log_headers != artifact_headers:
        raise RuntimeError("Probe8 error-header artifact differs from the log headers")
    if len(artifact_headers) != 344:
        raise RuntimeError(f"Probe8 error-header count {len(artifact_headers)} != 344")
    warning_count = len(
        re.findall(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"warning(?:\([^)]*\))?: ",
            log_text,
            re.MULTILINE,
        )
    )
    if warning_count != 374:
        raise RuntimeError(f"Probe8 warning-header count {warning_count} != 374")

    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}",
                re.MULTILINE,
            )
            count = len(pattern.findall(log_text))
            if count != 1:
                raise RuntimeError(
                    f"{rule.label}: exact diagnostic count {count}, expected 1"
                )
            verified.append(
                {
                    "rule": rule.label,
                    "line": header.line,
                    "column": header.column,
                    "message": header.message,
                    "count": count,
                }
            )
    return verified


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
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
                "direct_headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
            }
        )
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe8-log", type=Path, required=True)
    parser.add_argument("--probe8-error-headers", type=Path, required=True)
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
    verified = verify_authority(
        args.probe8_log.read_bytes(), args.probe8_error_headers.read_bytes()
    )
    source_text = source.decode("utf-8", errors="strict")
    before_trust = trust(source_text)
    result_text, rule_audit = transform(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust changed or nonzero: {before_trust} -> {after_trust}")
    restored_text, _ = transform(result_text, not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore the source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE8_AUTHORITY_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe8_run_id": 31969310662,
            "probe8_job_id": 95219107880,
            "probe8_artifact_id": 9269446991,
            "probe8_result_sha256": "02a986f3fe2a3bd6dbd96cd0238ae120cc72d7d09458da0df92b35c8cd6328d7",
            "probe8_candidate_sha256": INPUT_SHA256,
            "probe8_candidate_git_blob": INPUT_GIT_BLOB,
            "probe8_log_sha256": LOG_SHA256,
            "probe8_error_headers_sha256": ERROR_HEADERS_SHA256,
            "probe8_error_headers": 344,
            "probe8_warning_headers": 374,
            "probe8_exit": 1,
            "probe8_panic": 0,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "active_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_headers_verified": len(verified),
        "rules": rule_audit,
        "selected_exact_probe8_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "inverse_byte_equal": True,
        "trust": after_trust,
        "api_static_evidence": {
            "pi_zero_apply_existing_qym_line": 43153,
            "continuous_linear_map_zero_apply_existing_qym_line": 59571,
            "submodule_mem_bot_explicit_scalar_existing_qym_line": 19343,
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
