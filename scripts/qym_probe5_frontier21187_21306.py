#!/usr/bin/env python3
"""Exact reversible repairs for the first two observed Probe4 QYM errors."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


EXPECTED_INPUT_SHA256 = (
    "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
)
EXPECTED_INPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_INPUT_BYTES = 2_910_229
EXPECTED_INPUT_LF = 61_523
EXPECTED_PROBE4_LOG_SHA256 = (
    "3ce6d19d831d1723b19fb15181e9561cb1e6b8744e130812838469a03011ddc6"
)

EXPECTED_OUTPUT_SHA256 = (
    "3654c5ac43028fd020e46d520b3f7d5e5a3068be69596cbdf06e5700a5383fe5"
)
EXPECTED_OUTPUT_GIT_BLOB = "13b3446f1d83239c5709d8e820e69be22e1859ab"
EXPECTED_OUTPUT_BYTES = 2_910_465
EXPECTED_OUTPUT_LF = 61_529


@dataclass(frozen=True)
class ExactRule:
    label: str
    error_lines: tuple[int, ...]
    old: str
    new: str
    expected: int


RULES: tuple[ExactRule, ...] = (
    ExactRule(
        "transport_domain_membership_with_rw_not_dependent_cast",
        (21187, 23759),
        """  · intro y hy
    obtain ⟨x, hxy, _⟩ :=
      adjointDomain_eq_domainWitness_of_positiveShift_surjective
        hDense hSymm hSurj ⟨y, hy⟩
    exact hxy ▸ x.property
""",
        """  · intro y hy
    obtain ⟨x, hxy, _⟩ :=
      adjointDomain_eq_domainWitness_of_positiveShift_surjective
        hDense hSymm hSurj ⟨y, hy⟩
    have hxmem : (x : H) ∈ A.domain := x.property
    rw [hxy] at hxmem
    exact hxmem
""",
        2,
    ),
    ExactRule(
        "normalize_double_neg_solution_map_to_positive_inverse",
        (21306, 23883),
        """  exact positiveInverse_positiveShift B j hj hjDense μ c hShift x
""",
        """  simpa only [positiveInverse_apply, map_neg, neg_neg] using
    positiveInverse_positiveShift B j hj hjDense μ c hShift x
""",
        2,
    ),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


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


def trust_counts(text: str) -> dict[str, int]:
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


def transform(text: str, *, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    sequence = tuple(reversed(RULES)) if inverse else RULES
    audit: list[dict[str, object]] = []
    for rule in sequence:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.expected:
            raise RuntimeError(
                f"{rule.label}: {count} exact occurrences, expected {rule.expected}"
            )
        if text.count(new) != 0:
            raise RuntimeError(f"{rule.label}: opposite block already present")
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "probe4_error_lines": list(rule.error_lines),
                "occurrences": count,
                "direction": "inverse" if inverse else "forward",
            }
        )
    return text, audit


def expected_shape(*, output: bool) -> tuple[str, str, int, int]:
    if output:
        return (
            EXPECTED_OUTPUT_SHA256,
            EXPECTED_OUTPUT_GIT_BLOB,
            EXPECTED_OUTPUT_BYTES,
            EXPECTED_OUTPUT_LF,
        )
    return (
        EXPECTED_INPUT_SHA256,
        EXPECTED_INPUT_GIT_BLOB,
        EXPECTED_INPUT_BYTES,
        EXPECTED_INPUT_LF,
    )


def assert_shape(
    actual: dict[str, object], expected: tuple[str, str, int, int], *, allow_unsealed: bool
) -> None:
    if expected[0] == "__TO_SEAL__":
        if allow_unsealed:
            return
        raise RuntimeError("output identity is not sealed")
    for key, wanted in zip(("sha256", "git_blob", "bytes", "lf"), expected, strict=True):
        if actual[key] != wanted:
            raise RuntimeError(f"{key} mismatch: {actual[key]} != {wanted}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--allow-unsealed", action="store_true")
    args = parser.parse_args()

    inverse = args.mode == "inverse"
    source = args.input.read_bytes()
    source_shape = shape(source)
    assert_shape(source_shape, expected_shape(output=inverse), allow_unsealed=args.allow_unsealed)
    source_text = source.decode("utf-8")
    projected_text, rules = transform(source_text, inverse=inverse)
    projected = projected_text.encode("utf-8")
    projected_shape = shape(projected)
    assert_shape(
        projected_shape,
        expected_shape(output=not inverse),
        allow_unsealed=args.allow_unsealed,
    )
    before_trust = trust_counts(source_text)
    after_trust = trust_counts(projected_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust delta: {before_trust} -> {after_trust}")
    args.output.write_bytes(projected)
    audit = {
        "schema": "qym-probe5-frontier21187-21306-transform-v1",
        "status": "STATIC_REPAIR_NOT_LEAN_EXECUTED",
        "direction": "inverse" if inverse else "forward",
        "input": source_shape,
        "output": projected_shape,
        "rules": rules,
        "trust_before": before_trust,
        "trust_after": after_trust,
        "execution": {"lean": False, "lake": False, "remote": False},
    }
    args.audit.write_text(
        json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps(audit, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
