#!/usr/bin/env python3
"""One exact, reversible, conditional Probe5 repair for Probe3 line 41082.

This helper is locked to the exact Probe4 projection.  It only rewrites an
exact proof block in caller-provided work files; it does not run Lean/Lake,
access the network, mutate repository sources, or authorize promotion.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


EXPECTED_INPUT_SHA256 = (
    "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
)
EXPECTED_INPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_INPUT_BYTES = 2_910_229
EXPECTED_INPUT_LF = 61_523
EXPECTED_PROBE3_LOG_SHA256 = (
    "501029e514ba6bc875527e1bc96fb9f571afda222e53e633078736dccaa71f56"
)
EXPECTED_PROBE4_LOG_SHA256 = (
    "3ce6d19d831d1723b19fb15181e9561cb1e6b8744e130812838469a03011ddc6"
)

# Filled after the first deterministic projection, then enforced in both
# directions.  --allow-unsealed is accepted only while these values remain
# placeholders and exists solely to obtain the identities for sealing.
EXPECTED_OUTPUT_SHA256 = (
    "a3822ea18d2ae8aac7dea68d57469ce3cc8d6359af0e1b04b9ef1d24d5866136"
)
EXPECTED_OUTPUT_GIT_BLOB = "9c31e0f8fcd310459b2c962026e0a0cb81550607"
EXPECTED_OUTPUT_BYTES = 2_910_441
EXPECTED_OUTPUT_LF = 61_529

RULE_LABEL = "continuous_congr_pointwise_cusp_shift_probe3_41082_probe4_41115"
PROBE3_ERROR_LINES = (41082,)
PROBE4_ERROR_LINES = (41115,)
PROBE4_ANCHOR_LINES = (41109, 41118)

OLD = """  have hinverseEta : Continuous
      (fun x : ℝ =>
        (inverseEtaMultiplier GammaTwo).factor
          (actualFixedPhaseCuspDeckTranslation kappa)
          (actualFixedPhaseCuspHorocyclePoint kappa Y x)) := by
    simp_rw [inverseEtaMultiplier_factor,
      ← actualFixedPhaseCuspHorocyclePoint_add_two]
    exact heta.div hetaShift
      (fun x => ModularForm.eta_ne_zero
        (actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2)
"""

NEW = """  have hinverseEta : Continuous
      (fun x : ℝ =>
        (inverseEtaMultiplier GammaTwo).factor
          (actualFixedPhaseCuspDeckTranslation kappa)
          (actualFixedPhaseCuspHorocyclePoint kappa Y x)) := by
    refine (heta.div hetaShift
      (fun x => ModularForm.eta_ne_zero
        (actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2)).2)).congr
          (fun x => ?_)
    rw [inverseEtaMultiplier_factor]
    exact congrArg
      (fun z : ℍ =>
        ModularForm.eta
            ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ) /
          ModularForm.eta (z : ℂ))
      (actualFixedPhaseCuspHorocyclePoint_add_two kappa Y x)
"""


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
    old, new = (NEW, OLD) if inverse else (OLD, NEW)
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{RULE_LABEL}: {count} exact occurrences, expected 1")
    if text.count(new) != 0:
        raise RuntimeError(f"{RULE_LABEL}: opposite block already present")
    return text.replace(old, new), [
        {
            "label": RULE_LABEL,
            "probe3_error_lines": list(PROBE3_ERROR_LINES),
            "probe4_error_lines": list(PROBE4_ERROR_LINES),
            "probe4_anchor_lines": list(PROBE4_ANCHOR_LINES),
            "occurrences": count,
            "direction": "inverse" if inverse else "forward",
        }
    ]


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
        raise RuntimeError("conditional output identity is not sealed")
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
    assert_shape(
        source_shape,
        expected_shape(output=inverse),
        allow_unsealed=args.allow_unsealed,
    )
    before_text = source.decode("utf-8")
    projected_text, rules = transform(before_text, inverse=inverse)
    projected = projected_text.encode("utf-8")
    projected_shape = shape(projected)
    assert_shape(
        projected_shape,
        expected_shape(output=not inverse),
        allow_unsealed=args.allow_unsealed,
    )
    before_trust = trust_counts(before_text)
    after_trust = trust_counts(projected_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust delta: {before_trust} -> {after_trust}")

    args.output.write_bytes(projected)
    audit = {
        "schema": "qym-probe5-line41082-conditional-transform-v1",
        "status": "STATIC_CONDITIONAL_NOT_LEAN_EXECUTED",
        "direction": "inverse" if inverse else "forward",
        "input": source_shape,
        "output": projected_shape,
        "rules": rules,
        "inverse_byte_equal": True,
        "trust_before": before_trust,
        "trust_after": after_trust,
        "activation_gate": {
            "activation": False,
            "ready_for_probe5_inclusion": True,
            "promotion_authorized": False,
            "probe4_terminal_artifact_checked": True,
        },
        "execution": {"lean": False, "lake": False, "remote": False},
    }
    args.audit.write_text(
        json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps(audit, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
