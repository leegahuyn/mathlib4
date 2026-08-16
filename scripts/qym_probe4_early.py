#!/usr/bin/env python3
"""Exact reversible transformer for the first independent QYM probe-4 roots.

This package is intentionally static.  It does not invoke Lean, Lake, Git, or
the network.  The forward transform accepts only the terminal probe-3
candidate and applies four exact, single-occurrence proof repairs.  The
inverse applies the same inventory in reverse and must recover every input
byte.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe4-early-transform-v1"
EXPECTED_INPUT_SHA256 = (
    "9e82073bdaf6339feb1ca09d70ab371947c6e07294ae01895a33c75f978bd780"
)
EXPECTED_INPUT_GIT_BLOB = "652a6b11899db967ec19c2f32ca7aa1ad2044c7a"
EXPECTED_INPUT_BYTES = 2_906_639
EXPECTED_INPUT_LF = 61_479

# Sealed after an independent in-memory projection of this exact transformer.
EXPECTED_OUTPUT_SHA256 = (
    "2cddd2f6109a9f3672b240d9db44b5f3bb36a392a3cb5720fc8ab4e8dd39242c"
)
EXPECTED_OUTPUT_GIT_BLOB = "6d6b9349908f2abbc08521ba4a19b3d06db3da0a"
EXPECTED_OUTPUT_BYTES = 2_907_291
EXPECTED_OUTPUT_LF = 61_495

AUTHORITY_LOG_SHA256 = (
    "501029e514ba6bc875527e1bc96fb9f571afda222e53e633078736dccaa71f56"
)


@dataclass(frozen=True)
class Repair:
    label: str
    error_line: int
    classification: str
    old: str
    new: str


REPAIRS = (
    Repair(
        label="left_resolvent_inverse_avoid_dependent_rewrite",
        error_line=17657,
        classification="direct_root",
        old=(
            "  simpa only [spectrum.resolvent_eq hr, ← hr.unit_spec] using "
            "hr.unit.inv_mul\n"
        ),
        new=(
            "  calc\n"
            "    resolvent a r * (algebraMap R A r - a) =\n"
            "        (↑(hr.unit⁻¹) : A) * (algebraMap R A r - a) :=\n"
            "      congrArg (fun x : A => x * (algebraMap R A r - a))\n"
            "        (spectrum.resolvent_eq hr)\n"
            "    _ = (↑(hr.unit⁻¹) : A) * (↑hr.unit : A) :=\n"
            "      congrArg (fun x : A => (↑(hr.unit⁻¹) : A) * x) hr.unit_spec.symm\n"
            "    _ = 1 := hr.unit.inv_mul\n"
        ),
    ),
    Repair(
        label="right_resolvent_inverse_avoid_dependent_rewrite",
        error_line=17663,
        classification="direct_root",
        old=(
            "  simpa only [spectrum.resolvent_eq hr, ← hr.unit_spec] using "
            "hr.unit.mul_inv\n"
        ),
        new=(
            "  calc\n"
            "    (algebraMap R A r - a) * resolvent a r =\n"
            "        (algebraMap R A r - a) * (↑(hr.unit⁻¹) : A) :=\n"
            "      congrArg (fun x : A => (algebraMap R A r - a) * x)\n"
            "        (spectrum.resolvent_eq hr)\n"
            "    _ = (↑hr.unit : A) * (↑(hr.unit⁻¹) : A) :=\n"
            "      congrArg (fun x : A => x * (↑(hr.unit⁻¹) : A)) hr.unit_spec.symm\n"
            "    _ = 1 := hr.unit.mul_inv\n"
        ),
    ),
    Repair(
        label="compact_right_composition_expose_function_composition",
        error_line=17740,
        classification="direct_root",
        old=(
            "    simpa only [ContinuousLinearMap.coe_mul'] using\n"
            "      hcompact.comp_clm scalarDifference\n"
        ),
        new=(
            "    change IsCompactOperator\n"
            "      (⇑(resolvent T r) ∘ ⇑scalarDifference)\n"
            "    exact hcompact.comp_clm scalarDifference\n"
        ),
    ),
    Repair(
        label="compact_left_composition_expose_function_composition",
        error_line=17791,
        classification="direct_root",
        old=(
            "    simpa only [ContinuousLinearMap.coe_mul'] using\n"
            "      hcompact.clm_comp (algebraMap ℝ (H →L[ℝ] H) r - T)\n"
        ),
        new=(
            "    change IsCompactOperator\n"
            "      (⇑(algebraMap ℝ (H →L[ℝ] H) r - T) ∘ ⇑(resolvent T r))\n"
            "    exact hcompact.clm_comp (algebraMap ℝ (H →L[ℝ] H) r - T)\n"
        ),
    ),
)


TRUST_PATTERNS = {
    "sorry": re.compile(r"(?<![\w.])sorry(?![\w])"),
    "admit": re.compile(r"(?<![\w.])admit(?![\w])"),
    "native_decide": re.compile(r"(?<![\w.])native_decide(?![\w])"),
    "Lean.ofReduceBool": re.compile(r"(?<![\w.])Lean\.ofReduceBool(?![\w])"),
    "axiom_declaration": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "unsafe_declaration": re.compile(
        r"^[ \t]*(?:unsafe[ \t]+)(?:def|theorem|abbrev|instance)\b",
        re.MULTILINE,
    ),
    "maxHeartbeats_zero": re.compile(
        r"^[ \t]*set_option[ \t]+maxHeartbeats[ \t]+0\b", re.MULTILINE
    ),
}


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    header = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(header + raw).hexdigest()


def hygiene(raw: bytes, label: str) -> dict[str, object]:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise AssertionError(f"{label}: UTF-8 BOM forbidden")
    if b"\r" in raw:
        raise AssertionError(f"{label}: CR forbidden")
    if b"\x00" in raw:
        raise AssertionError(f"{label}: NUL forbidden")
    if not raw.endswith(b"\n"):
        raise AssertionError(f"{label}: terminal LF required")
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "utf8": True,
        "bom": False,
        "cr": False,
        "nul": False,
        "terminal_lf": True,
    }


def trust_counts(text: str) -> dict[str, int]:
    return {
        name: len(pattern.findall(text))
        for name, pattern in TRUST_PATTERNS.items()
    }


def transform(text: str, *, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    rows = list(REPAIRS)
    if inverse:
        rows.reverse()
    audit: list[dict[str, object]] = []
    for repair in rows:
        old = repair.new if inverse else repair.old
        new = repair.old if inverse else repair.new
        old_count = text.count(old)
        new_count = text.count(new)
        if old_count != 1 or new_count != 0:
            raise AssertionError(
                f"{repair.label}: expected one exact source and zero target; "
                f"found {old_count}/{new_count}"
            )
        text = text.replace(old, new, 1)
        audit.append(
            {
                "label": repair.label,
                "error_line": repair.error_line,
                "classification": repair.classification,
                "direction": "inverse" if inverse else "forward",
                "occurrences": 1,
            }
        )
    return text, audit


def require_seal(info: dict[str, object], *, output: bool) -> None:
    if output:
        expected = (
            EXPECTED_OUTPUT_SHA256,
            EXPECTED_OUTPUT_GIT_BLOB,
            EXPECTED_OUTPUT_BYTES,
            EXPECTED_OUTPUT_LF,
        )
        if EXPECTED_OUTPUT_SHA256 == "__TO_BE_SEALED__":
            return
        label = "probe4 output"
    else:
        expected = (
            EXPECTED_INPUT_SHA256,
            EXPECTED_INPUT_GIT_BLOB,
            EXPECTED_INPUT_BYTES,
            EXPECTED_INPUT_LF,
        )
        label = "probe3 input"
    actual = (info["sha256"], info["git_blob"], info["bytes"], info["lf"])
    if actual != expected:
        raise AssertionError(f"{label}: exact seal mismatch: {actual!r}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--audit", type=Path)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()

    source = args.input.read_bytes()
    source_info = hygiene(source, "source")
    if args.mode == "forward":
        require_seal(source_info, output=False)
        result_text, detail = transform(source.decode("utf-8"), inverse=False)
        result = result_text.encode("utf-8")
        result_info = hygiene(result, "result")
        require_seal(result_info, output=True)
        restored_text, _ = transform(result_text, inverse=True)
    else:
        require_seal(source_info, output=True)
        result_text, detail = transform(source.decode("utf-8"), inverse=True)
        result = result_text.encode("utf-8")
        result_info = hygiene(result, "result")
        require_seal(result_info, output=False)
        restored_text, _ = transform(result_text, inverse=False)

    if restored_text.encode("utf-8") != source:
        raise AssertionError("byte-exact forward/inverse roundtrip failed")

    before_trust = trust_counts(source.decode("utf-8"))
    after_trust = trust_counts(result_text)
    if before_trust != after_trust:
        raise AssertionError("trust-marker inventory changed")
    if any(before_trust.values()):
        raise AssertionError(f"input trust markers are not zero: {before_trust!r}")

    audit = {
        "schema": SCHEMA,
        "status": "STATIC_PROJECTION_PASS_NOT_LEAN_EXECUTED",
        "mode": args.mode,
        "source": source_info,
        "result": result_info,
        "authority_log_sha256": AUTHORITY_LOG_SHA256,
        "direct_root_error_lines": [17657, 17663, 17740, 17791],
        "error_header_range_checked": {"start": 17657, "end": 20050},
        "active_occurrences": 4,
        "detail": detail,
        "trust_counts": before_trust,
        "inverse_byte_equal": True,
        "lean_executed": False,
        "lake_executed": False,
        "remote_accessed": False,
    }
    rendered = json.dumps(audit, indent=2, sort_keys=True) + "\n"
    print(rendered, end="")

    if args.check_only:
        if args.output is not None or args.audit is not None:
            raise AssertionError("--check-only forbids --output/--audit")
        return
    if args.output is None or args.audit is None:
        raise AssertionError("--output and --audit are required without --check-only")
    args.output.write_bytes(result)
    args.audit.write_text(rendered, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
