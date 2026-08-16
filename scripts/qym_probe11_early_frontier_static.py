#!/usr/bin/env python3
"""Exact-Probe10 reversible repairs for the first three independent owners.

The helper is intentionally static and activation-false.  It consumes only the
sealed Probe10 candidate and authority diagnostics, applies three unique exact
anchors, proves every one of the 3! orders has the same output, and proves the
inverse restores the input byte-for-byte.  It does not invoke Lean, Lake, Git,
the network, a remote API, or the canonical repository source.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


SCHEMA = "qym-probe11-early-frontier-v1-exact-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"
ERRORS = 255
WARNINGS = 343

# Sealed after the bootstrap transformation.
OUTPUT_SHA256 = "4f02f16182c8a727b4beff0a65c249644d0b2e4e29586f2812a069611177cc3f"
OUTPUT_GIT_BLOB = "f6417d243fb672d5df357d00c9f4da889b701510"
OUTPUT_BYTES = 2_923_626
OUTPUT_LF = 61_784


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


RULES: tuple[Rule, ...] = (
    Rule(
        "raw_differential_deck_calc_pin_value_space_type",
        "        mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ := by\n",
        "        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :\n"
        "          ScalarOneFormValue) := by\n",
        (
            Header(
                28362,
                4,
                "invalid 'calc' step, failed to synthesize `Trans` instance",
            ),
        ),
        "Fix the calc relation metavariable by pinning the already-declared value-space codomain.",
    ),
    Rule(
        "raw_differential_smul_use_exact_constant_mdifferentiability",
        "  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)\n"
        "      (fun _ : H => c) τ :=\n"
        "    (contMDiff_const.mdifferentiable (by simp)) τ\n",
        "  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)\n"
        "      (fun _ : H => c) τ :=\n"
        "    mdifferentiableAt_const\n",
        (
            Header(28384, 38, "unsolved goals"),
            Header(28379, 59, "unsolved goals"),
        ),
        "Avoid the underconstrained smoothness-order metavariable; use the direct constant MDiffAt theorem.",
    ),
    Rule(
        "raw_differential_constant_change_before_mvfderiv_const",
        "theorem rawDifferential_constantOne (tau : H) :\n"
        "    rawDifferential constantOneInvariant tau = 0 := by\n"
        "  simpa only [rawDifferential, constantOneInvariant] using\n"
        "    (mvfderiv_const (I := 𝓘(ℂ)) (c := (1 : ℂ)) (x := tau))\n",
        "theorem rawDifferential_constantOne (tau : H) :\n"
        "    rawDifferential constantOneInvariant tau = 0 := by\n"
        "  change mvfderiv 𝓘(ℂ) (fun _ : H => (1 : ℂ)) tau = 0\n"
        "  exact mvfderiv_const (I := 𝓘(ℂ)) (c := (1 : ℂ)) (x := tau)\n",
        (
            Header(28740, 2, "Type mismatch: After simplification, term"),
        ),
        "Let the raw mvfderiv equality infer one zero type before applying mvfderiv_const.",
    ),
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
    bootstrap: bool,
) -> None:
    if not (bootstrap and wanted[0] == "__TO_SEAL__"):
        for key, value in zip(
            ("sha256", "git_blob", "bytes", "lf"), wanted, strict=True
        ):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_authority(
    log_data: bytes, headers_data: bytes, diagnostics_data: bytes
) -> list[dict[str, object]]:
    identities = (
        (sha256(log_data), LOG_SHA256, "log"),
        (sha256(headers_data), HEADERS_SHA256, "headers"),
        (sha256(diagnostics_data), DIAGNOSTICS_SHA256, "diagnostics"),
    )
    for actual, wanted, label in identities:
        if actual != wanted:
            raise RuntimeError(f"exact Probe10 {label} identity mismatch: {actual}")

    log_text = log_data.decode("utf-8")
    headers = headers_data.decode("utf-8").splitlines()
    extracted = [
        line
        for line in log_text.splitlines()
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if extracted != headers or len(headers) != ERRORS:
        raise RuntimeError("Probe10 error-header extraction mismatch")
    warning_count = len(
        re.findall(
            r"(?m)^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"warning(?:\([^)]*\))?: ",
            log_text,
        )
    )
    if warning_count != WARNINGS:
        raise RuntimeError(f"Probe10 warnings {warning_count} != {WARNINGS}")

    rows = [json.loads(line) for line in diagnostics_data.decode("utf-8").splitlines()]
    if len(rows) != ERRORS + WARNINGS:
        raise RuntimeError(f"diagnostic rows {len(rows)} != {ERRORS + WARNINGS}")
    severities = {name: sum(row["severity"] == name for row in rows) for name in ("error", "warning")}
    if severities != {"error": ERRORS, "warning": WARNINGS}:
        raise RuntimeError(f"diagnostic severities mismatch: {severities}")

    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            code = rf"\({re.escape(header.code)}\)" if header.code else r"(?:\([^)]*\))?"
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error{code}: {re.escape(header.message)}",
                re.MULTILINE,
            )
            count = len(pattern.findall(log_text))
            if count != 1:
                raise RuntimeError(
                    f"{rule.label}:{header.line}:{header.column} header count {count}"
                )
            matching_rows = [
                row
                for row in rows
                if row["severity"] == "error"
                and row["line"] == header.line
                and row["column"] == header.column
                and row.get("code") == header.code
                and row["message"].startswith(header.message)
            ]
            if len(matching_rows) != 1:
                raise RuntimeError(
                    f"{rule.label}:{header.line}:{header.column} diagnostic count "
                    f"{len(matching_rows)}"
                )
            verified.append(
                {
                    "rule": rule.label,
                    **asdict(header),
                    "header_count": count,
                    "diagnostic_count": len(matching_rows),
                }
            )
    return verified


def replace_rule(text: str, rule: Rule, inverse: bool) -> str:
    old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{rule.label}: source anchor count {count} != 1")
    destination_count = text.count(new)
    if destination_count != 0:
        raise RuntimeError(
            f"{rule.label}: destination anchor already present {destination_count}"
        )
    return text.replace(old, new)


def apply_order(text: str, order: tuple[Rule, ...], inverse: bool) -> str:
    for rule in order:
        text = replace_rule(text, rule, inverse)
    return text


def verify_independence(source: str) -> dict[str, object]:
    spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        start = source.find(rule.old)
        if start < 0 or source.find(rule.old, start + 1) >= 0:
            raise RuntimeError(f"{rule.label}: non-unique exact source anchor")
        if source.count(rule.new):
            raise RuntimeError(f"{rule.label}: destination unexpectedly active")
        spans.append((start, start + len(rule.old), rule.label))
    overlaps = [
        (left_label, right_label)
        for index, (left_start, left_end, left_label) in enumerate(spans)
        for right_start, right_end, right_label in spans[index + 1 :]
        if left_start < right_end and right_start < left_end
    ]
    if overlaps:
        raise RuntimeError(f"rule anchor overlap: {overlaps}")

    canonical = apply_order(source, RULES, False)
    order_rows: list[dict[str, object]] = []
    for order in itertools.permutations(RULES):
        result = apply_order(source, order, False)
        if result != canonical:
            raise RuntimeError("forward order dependence")
        restored = apply_order(result, tuple(reversed(order)), True)
        if restored != source:
            raise RuntimeError("per-order inverse mismatch")
        order_rows.append(
            {
                "order": [rule.label for rule in order],
                "output_sha256": sha256(result.encode("utf-8")),
                "inverse_byte_equal": True,
            }
        )
    return {
        "rules": len(RULES),
        "source_occurrences": len(spans),
        "overlaps": [],
        "orders_tested": len(order_rows),
        "all_order_outputs_equal": True,
        "all_order_inverses_equal": True,
        "orders": order_rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe10-log", type=Path, required=True)
    parser.add_argument("--probe10-error-headers", type=Path, required=True)
    parser.add_argument("--probe10-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()

    inverse = args.mode == "inverse"
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected(inverse, False), bootstrap=args.bootstrap_seal)
    diagnostic_map = verify_authority(
        args.probe10_log.read_bytes(),
        args.probe10_error_headers.read_bytes(),
        args.probe10_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8")
    independence = None if inverse else verify_independence(source_text)
    before_trust = trust(source_text)
    order = tuple(reversed(RULES)) if inverse else RULES
    result_text = apply_order(source_text, order, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected(inverse, True), bootstrap=args.bootstrap_seal)
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust inventory failure: {before_trust} -> {after_trust}")
    restored = apply_order(result_text, tuple(reversed(order)), not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    rule_rows = [
        {
            "label": rule.label,
            "direction": args.mode,
            "occurrences": 1,
            "headers": [asdict(header) for header in rule.headers],
            "rationale": rule.rationale,
        }
        for rule in order
    ]
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE10_NOT_LEAN_EXECUTED",
        "activation": False,
        "activation_gate": "TERMINAL_PROBE11_EXECUTION_REQUIRED",
        "mode": args.mode,
        "authority": {
            "run_id": 31973408809,
            "job_id": 95229227905,
            "artifact_id": 9270510078,
            "github_sha": "0957f9b925663bc78b76c7207084fb6199eb60de",
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": ERRORS,
            "warnings": WARNINGS,
            "panic": 0,
            "exit": 1,
            "first_error": "28362:4",
            "last_error": "59654:45",
        },
        "source": source_shape,
        "result": result_shape,
        "scope": {
            "producer_lines": [28362, 28379, 28384, 28740],
            "independent_owners": [
                "rawDifferential_deck_comp",
                "rawDifferential_smul",
                "rawDifferential_constantOne",
            ],
            "direct_diagnostics": 4,
            "cascade_lines_modified": False,
            "excluded_next_uncertain_line": 31941,
        },
        "repair_families": len(RULES),
        "repair_occurrences": len(RULES),
        "diagnostic_map": diagnostic_map,
        "rules": rule_rows,
        "own_rule_independence": independence,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "static_evidence": {
            "deck_calc_failure_exact_trans_meta": "Trans Eq Eq ?m.210",
            "smul_constant_failure_exact_goal": "¬?m.130 = 0",
            "smul_final_goal_attributed_same_owner": True,
            "constant_failure_zero_type_mismatch": [
                "TangentSpace 𝓘(ℂ, ℂ) tau →L[ℂ] ℂ",
                "ScalarOneFormValue",
            ],
            "local_mathlib_mdifferentiableAt_const_signature_inspected": True,
            "rawDifferential_add_existing_change_precedent_lines": [28373, 28375],
        },
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
    args.audit.write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
