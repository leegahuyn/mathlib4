#!/usr/bin/env python3
"""Prepare exact, reversible early-frontier QYM repairs without requiring Lean.

The default mode is check-only: the candidate is transformed in memory, audited,
inverted byte-for-byte, and summarized on stdout.  Files are written only when
the caller explicitly supplies --output and/or --audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


EXPECTED_INPUT_SHA256 = (
    "64f045b04dc39e157ba609047e6ac9a0851962b7c74024af9987dbcbd46f19d1"
)
EXPECTED_INPUT_BYTES = 2_906_438
EXPECTED_INPUT_LF = 61_580
EARLY_LINE_LIMIT = 12_000


@dataclass(frozen=True)
class Repair:
    label: str
    old: str
    new: str
    expected: int
    probe1_error_lines: tuple[int, ...]
    rationale: str


REPAIRS = (
    Repair(
        label="expose_projected_reciprocal_definition_at_refutation",
        old=(
            "  exact\n"
            "    QYM.OperatorFormCompactnessCore."
            "projectedReciprocal_not_isSequentiallyClosed\n"
            "      (by\n"
            "        simpa [QYM.OperatorFormCompactnessCore.projectedReciprocal] "
            "using hprojected)"
        ),
        new=(
            "  apply\n"
            "    QYM.OperatorFormCompactnessCore."
            "projectedReciprocal_not_isSequentiallyClosed\n"
            "  change QYM.OperatorFormCompactnessCore.IsSequentiallyClosedOn\n"
            "    QYM.OperatorFormCompactnessCore.positiveRealDomain\n"
            "    (fun x => QYM.OperatorFormCompactnessCore.zeroProjection\n"
            "      (QYM.OperatorFormCompactnessCore.reciprocalPartial x))\n"
            "  exact hprojected"
        ),
        expected=1,
        probe1_error_lines=(11_594,),
        rationale=(
            "The logged term is already the explicit projection/reciprocal "
            "composition; use change on the definitionally equal goal instead "
            "of simplifying the hypothesis."
        ),
    ),
    Repair(
        label="expose_projected_reciprocal_definition_at_countermodel",
        old=(
            "  simpa [QYM.OperatorFormCompactnessCore.projectedReciprocal] using\n"
            "    QYM.OperatorFormCompactnessCore."
            "projectedReciprocal_not_isSequentiallyClosed"
        ),
        new=(
            "  change ¬ QYM.OperatorFormCompactnessCore.IsSequentiallyClosedOn\n"
            "    QYM.OperatorFormCompactnessCore.positiveRealDomain\n"
            "    QYM.OperatorFormCompactnessCore.projectedReciprocal\n"
            "  exact\n"
            "    QYM.OperatorFormCompactnessCore."
            "projectedReciprocal_not_isSequentiallyClosed"
        ),
        expected=1,
        probe1_error_lines=(11_615,),
        rationale=(
            "The existential target contains the unfolded composition; change "
            "it to the definitionally equal named map before applying the exact "
            "negative theorem."
        ),
    ),
    Repair(
        label="correct_main_remainder_addition_side",
        old="add_le_add_left (hremainder.2.2 n hn) _",
        new="add_le_add_right (hremainder.2.2 n hn) _",
        expected=1,
        probe1_error_lines=(11_773,),
        rationale=(
            "The logged goal keeps the main-term absolute value on the left; "
            "add_le_add_right produces exactly that orientation."
        ),
    ),
    Repair(
        label="correct_envelope_addition_side",
        old=(
            "      add_le_add_left\n"
            "        (oneTermRemainderEnvelope_le_rootExponentialEnvelope "
            "hremainder.2.1 hnOne) _"
        ),
        new=(
            "      add_le_add_right\n"
            "        (oneTermRemainderEnvelope_le_rootExponentialEnvelope "
            "hremainder.2.1 hnOne) _"
        ),
        expected=1,
        probe1_error_lines=(11_789,),
        rationale=(
            "The logged goal keeps the leading root-exponential envelope on "
            "the left; add_le_add_right has the required orientation."
        ),
    ),
    Repair(
        label="normalize_uniform_bound_at_real_one",
        old=(
            "  have hqBound : (q : ℝ) ≤ C * 2 := by\n"
            "    simpa [driftingLinearProfile] using hbound q 1 (by norm_num)"
        ),
        new=(
            "  have hqBound : (q : ℝ) ≤ C * 2 := by\n"
            "    have hqBoundRaw := hbound q (1 : ℝ) (by norm_num)\n"
            "    norm_num [driftingLinearProfile] at hqBoundRaw\n"
            "    exact hqBoundRaw"
        ),
        expected=1,
        probe1_error_lines=(11_958,),
        rationale=(
            "The logged hypothesis has C * (1 + 1) while the goal has C * 2; "
            "pin T to Real and normalize the instantiated hypothesis first."
        ),
    ),
)


TRUST_PATTERNS = {
    "sorry": re.compile(r"(?<![\w.])sorry(?![\w])"),
    "admit": re.compile(r"(?<![\w.])admit(?![\w])"),
    "native_decide": re.compile(r"(?<![\w.])native_decide(?![\w])"),
    "Lean.ofReduceBool": re.compile(r"(?<![\w.])Lean\.ofReduceBool(?![\w])"),
    "axiom": re.compile(r"(?<![\w.])axiom(?![\w])"),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hygiene(data: bytes, *, label: str) -> dict[str, object]:
    if b"\x00" in data:
        raise AssertionError(f"{label}: NUL byte found")
    if b"\r" in data:
        raise AssertionError(f"{label}: CR byte found")
    if not data.endswith(b"\n"):
        raise AssertionError(f"{label}: missing final LF")
    text = data.decode("utf-8")
    return {
        "utf8": True,
        "nul": 0,
        "cr": 0,
        "final_lf": True,
        "bytes": len(data),
        "lf": data.count(b"\n"),
        "sha256": sha256(data),
        "trust_literals": {
            name: len(pattern.findall(text))
            for name, pattern in TRUST_PATTERNS.items()
        },
    }


def exact_replace(text: str, repair: Repair) -> tuple[str, dict[str, object]]:
    old_count = text.count(repair.old)
    new_count_before = text.count(repair.new)
    if old_count != repair.expected:
        raise AssertionError(
            f"{repair.label}: expected {repair.expected} old occurrence(s), "
            f"found {old_count}"
        )
    if new_count_before != 0:
        raise AssertionError(
            f"{repair.label}: replacement already occurs {new_count_before} time(s)"
        )
    offsets: list[int] = []
    cursor = 0
    for _ in range(repair.expected):
        offset = text.index(repair.old, cursor)
        offsets.append(offset)
        cursor = offset + len(repair.old)
    source_lines = tuple(text.count("\n", 0, offset) + 1 for offset in offsets)
    if any(line > EARLY_LINE_LIMIT for line in source_lines):
        raise AssertionError(
            f"{repair.label}: source line outside early frontier: {source_lines}"
        )
    transformed = text.replace(repair.old, repair.new)
    if transformed.count(repair.old) != 0:
        raise AssertionError(f"{repair.label}: stale old occurrence remains")
    if transformed.count(repair.new) != repair.expected:
        raise AssertionError(f"{repair.label}: replacement occurrence mismatch")
    return transformed, {
        "label": repair.label,
        "old_occurrences": old_count,
        "new_occurrences_before": new_count_before,
        "new_occurrences_after": repair.expected,
        "candidate_source_lines": source_lines,
        "probe1_error_lines": repair.probe1_error_lines,
        "rationale": repair.rationale,
    }


def invert_exact(text: str) -> str:
    restored = text
    for repair in reversed(REPAIRS):
        new_count = restored.count(repair.new)
        if new_count != repair.expected:
            raise AssertionError(
                f"{repair.label}: inverse expected {repair.expected} new "
                f"occurrence(s), found {new_count}"
            )
        restored = restored.replace(repair.new, repair.old)
    return restored


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output")
    parser.add_argument("--audit")
    args = parser.parse_args()

    raw = Path(args.input).read_bytes()
    input_hygiene = hygiene(raw, label="input")
    if input_hygiene["sha256"] != EXPECTED_INPUT_SHA256:
        raise AssertionError("probe-2 candidate SHA-256 mismatch")
    if input_hygiene["bytes"] != EXPECTED_INPUT_BYTES:
        raise AssertionError("probe-2 candidate byte-count mismatch")
    if input_hygiene["lf"] != EXPECTED_INPUT_LF:
        raise AssertionError("probe-2 candidate LF-count mismatch")

    original = raw.decode("utf-8")
    transformed = original
    rewrite_audit: list[dict[str, object]] = []
    for repair in REPAIRS:
        transformed, entry = exact_replace(transformed, repair)
        rewrite_audit.append(entry)

    candidate = transformed.encode("utf-8")
    output_hygiene = hygiene(candidate, label="output")
    if input_hygiene["trust_literals"] != output_hygiene["trust_literals"]:
        raise AssertionError("trust-literal inventory changed")

    restored = invert_exact(transformed).encode("utf-8")
    if restored != raw:
        raise AssertionError("inverse audit failed to restore exact input bytes")

    result = {
        "schema": "qym-probe3-early-static-v1",
        "mode": "write" if args.output else "check-only",
        "early_line_limit": EARLY_LINE_LIMIT,
        "input": input_hygiene,
        "output": output_hygiene,
        "rewrites": rewrite_audit,
        "rewrite_rules": len(REPAIRS),
        "rewrite_occurrences": sum(repair.expected for repair in REPAIRS),
        "inverse": {
            "restored_exact_bytes": True,
            "restored_sha256": sha256(restored),
        },
        "trust_delta": {
            name: output_hygiene["trust_literals"][name]
            - input_hygiene["trust_literals"][name]
            for name in TRUST_PATTERNS
        },
        "inactive_uncertain_repairs": [],
    }

    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_bytes(candidate)
    if args.audit:
        audit_path = Path(args.audit)
        audit_path.parent.mkdir(parents=True, exist_ok=True)
        with audit_path.open("w", encoding="utf-8", newline="\n") as handle:
            handle.write(json.dumps(result, indent=2, sort_keys=True) + "\n")

    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
