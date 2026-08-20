#!/usr/bin/env python3
"""Probe11-tail conditional repairs reanchored to exact terminal Probe10.

The thirteen Probe9 tail roots are retained only when their exact anchors and
direct diagnostics survive in the terminal Probe10 authority.  Three further
independent tail producer/API roots are added.  The transformer is byte-locked,
exact-counted, reversible, trust0, and activation-disabled.  It writes only
new ``work/`` artifacts and never invokes Lean, Lake, Git, or the network.
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

SCHEMA = "qym-probe11-tail-p10-conditional-v1-exact-terminal-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "d577bdcab8ced2cdf40960582d6c8bebe6d782454fb54a4920fc1c07cb33fe30"
OUTPUT_GIT_BLOB = "dbd3eb62ab1d76a85e4493c2020f29850ad10dbf"
OUTPUT_BYTES = 2_924_073
OUTPUT_LF = 61_788

P9_TAIL_HELPER_SHA256 = (
    "45795b308bc45b2e2b9fc437869810c0de9e7a8fb65f7e3a53247b85a6a7d3e9"
)
P11_MID_HELPER_SHA256 = (
    "68f2b66a12878f3d9d85a3d94f2f5dc4060ec5995f4f5f84d7e17afa7cf07fcb"
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def load_helper(path: Path, expected_sha: str, role: str) -> ModuleType:
    if not path.is_file():
        raise RuntimeError(f"{role} helper missing: {path}")
    actual = sha256(path.read_bytes())
    if actual != expected_sha:
        raise RuntimeError(f"{role} helper identity mismatch: {actual}")
    name = "_qym_probe11_tail_p10_" + hashlib.sha256(
        str(path.resolve()).encode("utf-8")
    ).hexdigest()
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {role} helper: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


PACKAGE_PARENT = Path(__file__).resolve().parent.parent
P9_TAIL_HELPER_PATH = (
    PACKAGE_PARENT / "qym-probe11-tail-conditional" /
    "qym_probe11_tail_conditional.py"
)
P11_MID_HELPER_PATH = (
    PACKAGE_PARENT / "qym-probe11-mid-conditional" /
    "qym_probe11_mid_conditional.py"
)
P9_TAIL = load_helper(
    P9_TAIL_HELPER_PATH, P9_TAIL_HELPER_SHA256, "Probe11-tail exact-P9"
)
P11_MID = load_helper(
    P11_MID_HELPER_PATH, P11_MID_HELPER_SHA256, "Probe11-mid exact-P9"
)


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


SURVIVING_P10_HEADERS: dict[str, Header] = {
    "discriminant_mul_add_expose_product_producer":
        Header(52887, 18, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    "discriminant_mul_smul_expose_product_producer":
        Header(52902, 21, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    "discriminant_form_add_left_use_inner_api":
        Header(53036, 45, "unsolved goals"),
    "discriminant_form_add_right_use_map_and_inner_api":
        Header(53043, 45, "unsolved goals"),
    "discriminant_form_smul_left_use_inner_api":
        Header(53049, 52, "unsolved goals"),
    "discriminant_form_smul_right_use_map_and_inner_api":
        Header(53055, 47, "unsolved goals"),
    "discriminant_sqrt_mul_add_expose_product_producer":
        Header(53965, 18, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    "discriminant_sqrt_mul_smul_expose_product_producer":
        Header(53980, 21, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    "inverse_eta_rank_one_energy_use_star_mul_api":
        Header(55342, 48, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    "projection_hamiltonian_attach_isSymmetric_projection":
        Header(56327, 6, "Function expected at"),
    "natural_stage_cutoff_normalize_add_comm":
        Header(56827, 2, "Type mismatch"),
    "global_stage_projection_add_restore_rewrite_order":
        Header(56960, 18, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    "global_stage_projection_smul_restore_rewrite_order":
        Header(56979, 21, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
}


def retained_rules() -> tuple[Rule, ...]:
    prior = {rule.label: rule for rule in P9_TAIL.RULES}
    if set(prior) != set(SURVIVING_P10_HEADERS):
        raise RuntimeError(
            "the frozen Probe9 helper rule set does not exactly match surviving P10 roots"
        )
    return tuple(
        Rule(
            label=old.label,
            old=old.old,
            new=old.new,
            headers=(SURVIVING_P10_HEADERS[old.label],),
            rationale=old.rationale,
            precedent=old.precedent,
            provenance="retained_exact_anchor_and_surviving_direct_P10_diagnostic",
            occurrences=old.occurrences,
        )
        for old in P9_TAIL.RULES
    )


NEW_RULES: tuple[Rule, ...] = (
    Rule(
        "discriminant_real_multiplier_use_current_inner_smul_api",
        "          ((actualStageDiscriminantPotential Y x : ℂ) • v x) by\n"
        "      rw [InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "        InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ)])\n",
        "          ((actualStageDiscriminantPotential Y x : ℂ) • v x) by\n"
        "      rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "        RCLike.star_def, RCLike.conj_ofReal])\n",
        (Header(52996, 10, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Replace obsolete real-scalar-specialized matching with the current generic inner-smul APIs, then reduce conjugation of the coerced real scalar.",
        "The same current API sequence closes potential_isSymmetric at P10 lines 58531-58533.",
        "new_independent_P10_API_root",
    ),
    Rule(
        "discriminant_sqrt_real_multiplier_use_current_inner_smul_api",
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • v x) by\n"
        "      rw [InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "        InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ)])\n",
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • v x) by\n"
        "      rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "        RCLike.star_def, RCLike.conj_ofReal])\n",
        (Header(54076, 10, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Use the current generic inner-smul APIs for the real square-root multiplier and normalize its conjugation.",
        "The same current API sequence closes potential_isSymmetric at P10 lines 58531-58533.",
        "new_independent_P10_API_root",
    ),
    Rule(
        "global_projection_inner_negative_expose_second_representative",
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,\n"
        "      inner_zero_left, inner_zero_right]\n",
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hx, globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hx, inner_zero_left, inner_zero_right]\n",
        (Header(57072, 34, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose the second representative wrapper before applying the second negative-indicator rewrite.",
        "The exact P10 goal retains globalStageProjectionRepresentative only on the right after the first indicator reduction.",
        "new_independent_P10_producer_root",
    ),
)


RULES: tuple[Rule, ...] = retained_rules() + NEW_RULES


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


def sentinels_unsealed() -> bool:
    return (
        OUTPUT_SHA256 == ""
        and OUTPUT_GIT_BLOB == ""
        and OUTPUT_BYTES == 0
        and OUTPUT_LF == 0
    )


def check_shape(
    actual: dict[str, object], expected: dict[str, object], *, unsealed: bool = False
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
    log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes
) -> list[dict[str, object]]:
    identities = (
        ("Probe10 log", sha256(log_raw), LOG_SHA256),
        ("Probe10 headers", sha256(header_raw), HEADERS_SHA256),
        ("Probe10 diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    )
    for label, actual, expected in identities:
        if actual != expected:
            raise RuntimeError(f"{label} identity mismatch: {actual}")

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
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:"
                rf"{header.column}: error{code}: {re.escape(header.message)}"
            )
            hmatches = [line for line in header_lines if pattern.match(line)]
            dmatches = [
                row for row in rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(hmatches) != 1 or len(dmatches) != 1:
                raise RuntimeError(
                    f"{rule.label}: P10 authority mapping mismatch at "
                    f"{header.line}:{header.column}"
                )
            verified.append({
                "rule": rule.label,
                "line": header.line,
                "column": header.column,
                "code": header.code,
                "message": header.message,
                "kind": "surviving_direct_root",
                "provenance": rule.provenance,
            })
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


def audit_mid_collisions(base: str, *, inverse: bool) -> dict[str, object]:
    own_spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(base, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(
                f"own active span mismatch: {rule.label}: "
                f"{len(found)} != {rule.occurrences}"
            )
        own_spans.extend((start, end, rule.label) for start, end in found)

    overlaps: list[dict[str, object]] = []
    equalities: list[dict[str, str]] = []
    foreign_spans = 0
    for foreign in P11_MID.RULES:
        found = spans(base, foreign.old)
        expected = getattr(foreign, "occurrences", 1)
        if len(found) != expected:
            raise RuntimeError(
                f"Probe11-mid surviving anchor mismatch: {foreign.label}: "
                f"{len(found)} != {expected}"
            )
        foreign_spans += len(found)
        for own in RULES:
            for own_kind, own_anchor in (("old", own.old), ("new", own.new)):
                for foreign_kind, foreign_anchor in (
                    ("old", foreign.old), ("new", foreign.new)
                ):
                    if own_anchor == foreign_anchor:
                        equalities.append({
                            "own": own.label,
                            "own_variant": own_kind,
                            "foreign": foreign.label,
                            "foreign_variant": foreign_kind,
                        })
        for fstart, fend in found:
            for ostart, oend, own_label in own_spans:
                if max(fstart, ostart) < min(fend, oend):
                    overlaps.append({
                        "own": own_label,
                        "foreign": foreign.label,
                        "own_span": [ostart, oend],
                        "foreign_span": [fstart, fend],
                    })
    if equalities or overlaps:
        raise RuntimeError(
            f"Probe11-mid collision: equalities={equalities}, overlaps={overlaps}"
        )
    return {
        "p9_tail_helper_sha256": P9_TAIL_HELPER_SHA256,
        "p11_mid_helper_sha256": P11_MID_HELPER_SHA256,
        "retained_p9_tail_rules": len(SURVIVING_P10_HEADERS),
        "new_p10_rules": len(NEW_RULES),
        "own_spans_checked": len(own_spans),
        "p11_mid_spans_checked": foreign_spans,
        "exact_anchor_equalities": equalities,
        "span_overlaps": overlaps,
    }


def apply_rules(
    text: str, inverse: bool = False
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
        audits.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "headers": [header.__dict__ for header in rule.headers],
            "rationale": rule.rationale,
            "precedent": rule.precedent,
            "provenance": rule.provenance,
        })
    return text, audits


transform = apply_rules


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
    collision = audit_mid_collisions(source_text, inverse=inverse)
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
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 255,
            "warnings": 343,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [50000, 61783],
            "surviving_direct_roots_only": True,
            "retained_probe9_tail_roots": len(SURVIVING_P10_HEADERS),
            "new_independent_probe10_roots": len(NEW_RULES),
            "cascade_diagnostics_selected": False,
            "structural_50000_51837_cluster_excluded": True,
            "probe11_mid_anchor_span_overlap": False,
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
        "related_helper_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
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
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
